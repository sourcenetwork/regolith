//! A commit group whose fsync is owed: one claimable unit every member of the
//! group waits on (D53, plan 4.10).
//!
//! A group with a member committed by
//! [`commit_nowait`](crate::Transaction::commit_nowait) that needs an fsync
//! (one of its members asked for `Immediate` durability) is decided and
//! written by its leader as any group is, and then left owing the rest of its
//! landing: the fsync, the apply to the memtable, the publication of the read
//! horizon. That rest is one job, a [`GroupSync`]:
//!
//! - **One unit, many queues.** Each nowait member's queue waits on the job.
//!   The first member thread to poll claims it with one compare-and-swap and
//!   runs it, and the job pushes one completion to each member's queue. No
//!   member waits for one particular thread to be scheduled.
//! - **Blocking members help.** A member that committed with a blocking call
//!   claims the job and runs it itself, or, when another thread already runs
//!   it, waits for that run to land. The blocking calls do their own I/O.
//! - **Visibility after durability.** The job syncs before it applies or
//!   publishes anything, so at `Immediate` durability a commit is visible
//!   only once durable (`GroupCommit.tla`, `DurableBeforeVisible`). A failed
//!   sync discards the group's bytes and fails every member, as a group run
//!   inline does (G2).
//! - **Groups stay in order.** The pipeline holds the owed group until it
//!   lands: whoever takes the pipeline next lands it first, claiming and
//!   running the job when nobody has, or waiting for the thread that runs it.
//!   So no group is written, rotated past or published before the one ahead
//!   of it landed, and the WAL rollback of a failed sync never reaches past
//!   its own group. Closing the database lands it the same way.
//!
//! What a member learns is written into the group by the job before it lands
//! and taken by the member after, once each.

#![allow(unsafe_code)]

use std::io;
use std::sync::Arc;

use super::super::RegolithEngine;
use super::super::io::job::{Job, JobBody};
use super::txn::Settled;
use super::{GroupTicket, Written};
use crate::sync::internal::{AtomicPtr, Ordering};

/// A value put in once and taken out once, by different threads, with no
/// lock: what one member of a landed group learns.
struct Take<T>(AtomicPtr<T>);

// SAFETY: the value moves from the putting thread to the taking one and is
// never shared by reference, so `T: Send` is all that is needed.
unsafe impl<T: Send> Send for Take<T> {}
// SAFETY: as above; every access goes through the atomic pointer.
unsafe impl<T: Send> Sync for Take<T> {}

impl<T> Take<T> {
    fn empty() -> Self {
        Self(AtomicPtr::new(std::ptr::null_mut()))
    }

    /// Put `value` in. Replaces nothing: a second put drops the first value.
    fn put(&self, value: T) {
        let old = self
            .0
            .swap(Box::into_raw(Box::new(value)), Ordering::AcqRel);
        if !old.is_null() {
            // SAFETY: a non-null pointer here came from `Box::into_raw` above
            // and was swapped out, so this call owns it.
            drop(unsafe { Box::from_raw(old) });
        }
    }

    fn take(&self) -> Option<T> {
        let value = self.0.swap(std::ptr::null_mut(), Ordering::AcqRel);
        if value.is_null() {
            return None;
        }
        // SAFETY: as in `put`: swapped out, so owned here.
        Some(*unsafe { Box::from_raw(value) })
    }
}

impl<T> Drop for Take<T> {
    fn drop(&mut self) {
        drop(self.take());
    }
}

/// A group written to the log and owed its fsync, its apply and its
/// publication: the unit its members wait on.
pub(crate) struct GroupSync {
    job: Arc<Job>,
    /// What each member learns, in group order, put by the job before it
    /// lands. Shared with the job's body, which holds nothing else of the
    /// group, so neither keeps the other alive.
    results: Arc<[Take<io::Result<Settled>>]>,
}

/// What a member of a decided group is settled from once its group landed.
struct Member {
    ticket: GroupTicket,
    ops: u64,
}

/// The job's body: everything the landing needs, moved in.
///
/// It holds the database strongly, so a group always lands against the
/// database it was written to, whichever thread runs it and whenever: until
/// then the database stays open in memory even if every handle went away. A
/// group is always held by a queue that will run or settle it (a queue's poll
/// runs it, a queue's drop releases it, which lands it), by a blocking member
/// that lands it, or by the pipeline, which the next holder and close land.
/// Once the body ran it is dropped, and with it that hold.
struct Landing {
    engine: Arc<RegolithEngine>,
    results: Arc<[Take<io::Result<Settled>>]>,
    written: Written,
    members: Vec<Member>,
}

impl GroupSync {
    /// The unit for `group`, which `written` describes, its members taken
    /// out in group order. Each member's ticket (its verdict) settles the
    /// member when the group lands.
    pub(super) fn new(
        engine: Arc<RegolithEngine>,
        written: Written,
        group: &mut Vec<GroupTicket>,
    ) -> Arc<Self> {
        let members: Vec<Member> = group
            .drain(..)
            .map(|ticket| Member {
                ops: ticket.request.op_count(),
                ticket,
            })
            .collect();
        let results: Arc<[Take<io::Result<Settled>>]> =
            members.iter().map(|_| Take::empty()).collect();
        let body = Landing {
            engine,
            results: Arc::clone(&results),
            written,
            members,
        };
        Arc::new(GroupSync {
            job: Job::new(Box::new(body)),
            results,
        })
    }

    /// The job the members' queues wait on.
    pub(crate) fn job(&self) -> &Arc<Job> {
        &self.job
    }

    /// Whether the group has landed: synced, applied and published, or
    /// failed.
    pub(crate) fn is_landed(&self) -> bool {
        self.job.is_done()
    }

    /// Land the group on this thread: run the job if nobody claimed it yet,
    /// or wait for the thread that runs it. What a blocking member, the next
    /// pipeline holder and close do.
    pub(crate) fn land_here(&self, engine: &RegolithEngine) {
        if self.job.claim() {
            engine.cache.io().run_job(&self.job);
        } else {
            self.job.wait_landed();
        }
    }

    /// What member `member` learned, once the group landed. `None` after it
    /// was taken, or for a member out of range.
    pub(crate) fn take(&self, member: usize) -> Option<io::Result<Settled>> {
        self.results.get(member).and_then(Take::take)
    }

    /// Land the group on this thread if it has not landed, then take what
    /// member `member` learned.
    pub(crate) fn settle(&self, engine: &RegolithEngine, member: usize) -> io::Result<Settled> {
        self.land_here(engine);
        self.take(member).unwrap_or_else(|| {
            Err(io::Error::other(
                "a commit group's outcome was already taken for this commit",
            ))
        })
    }
}

impl std::fmt::Debug for GroupSync {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GroupSync")
            .field("members", &self.results.len())
            .field("landed", &self.is_landed())
            .finish()
    }
}

impl Landing {
    /// Sync, apply and publish, then put each member's outcome.
    fn land(self) {
        let Landing {
            engine,
            results,
            written,
            members,
        } = self;
        let outcome = engine.land_deferred(
            &written,
            members.iter().map(|member| &member.ticket.request),
        );
        let mut seq = outcome.as_ref().ok().copied().unwrap_or(0);
        for (member, result) in members.into_iter().zip(results.iter()) {
            let last = seq.saturating_add(member.ops).saturating_sub(1);
            result.put(match &outcome {
                Ok(_) => member.ticket.settle(member.ops, last),
                Err(err) => Err(crate::Error::clone_io(err)),
            });
            seq = last.saturating_add(1);
        }
    }
}

impl JobBody for Landing {
    fn run(self: Box<Self>) {
        (*self).land();
    }

    /// A group's fsync is never left undone: its records are in the log and
    /// its members wait on it, so a release lands it too.
    fn release(self: Box<Self>) {
        (*self).land();
    }
}
