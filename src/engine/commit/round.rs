//! The round: the one claim on the log's device step (plan 4.7, D53).
//!
//! Syncing the log and rolling a failed log back are done by one thread at
//! a time, and by whichever thread claims the round, a job, with one
//! compare-and-swap:
//!
//! - **A sync round** writes what is decided and not written, syncs the
//!   written prefix of the log and raises the durable offset over it. Every
//!   commit that waits for durability waits on the round: a blocking call
//!   claims it or waits for the thread that did, a `commit_nowait` commit
//!   leaves it on its queue, whose poll claims it when nobody has. Nobody
//!   waits for one particular thread to sync.
//! - **A rollback** is what a round does when the log has failed
//!   (`ordered.rs`), so no sync runs while commits are being discarded.
//! - **A hold** is the round claimed by an ordered unit for the length of
//!   its body ([`RegolithEngine::hold_round`]): the body syncs the log
//!   itself, and no round of another thread runs under it.
//!
//! One round at a time because a sync error is reported to one caller of
//! one file handle and then cleared by the host: two syncs overlapping on
//! the handle could tell the later caller that the bytes of a failed one
//! were safe (`engine::wal_log`). Each round installs the next before it
//! lands, so a thread woken by the landing finds a round it can claim.

use std::sync::Arc;

use super::super::RegolithEngine;
use super::super::callback::InCommit;
use super::super::io::job::{Job, JobBody};
use super::descriptor::{Decision, WRITTEN};
use super::hook;
use super::pipeline::Pipeline;
use super::ring::{Linked, Loaded};
use crate::perf_context::{PerfTimer, PerfTimerField};
use crate::statistics::{Histogram, Ticker};
use crate::sync::internal::{Arc as RingArc, AtomicPtr, AtomicU64, Ordering};

/// One round of the log's device step: the unit whoever needs the log
/// durable, or a failed log rolled back, claims.
pub(super) struct Round {
    pub(super) job: Arc<Job>,
    /// Set by a thread that claimed the round to do the device step itself
    /// (`RegolithEngine::hold_round`): the job's body then does nothing.
    held: AtomicU64,
    link: AtomicPtr<Round>,
}

impl Round {
    pub(super) fn new(engine: std::sync::Weak<RegolithEngine>) -> RingArc<Self> {
        RingArc::new(Self {
            job: Job::new(Box::new(SyncRound { engine })),
            held: AtomicU64::new(0),
            link: AtomicPtr::new(std::ptr::null_mut()),
        })
    }
}

/// A round held by [`RegolithEngine::hold_round`]: landed when dropped, on
/// return or on unwind, so nobody is left waiting on a claim nobody will
/// complete.
pub(super) struct HeldRound<'a> {
    engine: &'a RegolithEngine,
    round: RingArc<Round>,
}

impl Drop for HeldRound<'_> {
    fn drop(&mut self) {
        self.engine.io().run_job(&self.round.job);
    }
}

impl Linked for Round {
    fn link(&self) -> &AtomicPtr<Self> {
        &self.link
    }
}

impl RegolithEngine {
    /// The round to claim or wait on now. A round whose body ended without
    /// installing the next one (it unwound) is replaced here.
    pub(super) fn current_round(&self, pipe: &Pipeline) -> RingArc<Round> {
        loop {
            let round = pipe.round.load();
            if !round.job.is_done() {
                return round;
            }
            pipe.round.replace(&round, Round::new(self.me.clone()));
        }
    }

    /// Bring the log durable through what is written now, or a failed log
    /// rolled back: run the current round, or wait for the thread running
    /// it.
    pub(super) fn sync_round(&self, pipe: &Pipeline) {
        let round = self.current_round(pipe);
        hook::at(hook::Stage::Sync);
        self.run_or_wait(&round.job);
    }

    /// Claim the round, waiting out one another thread has under way, and
    /// hold it until the returned guard drops. The holder does the log's
    /// device step itself: no sync and no rollback of another thread runs
    /// meanwhile. What an ordered unit's body runs under (`ordered.rs`).
    pub(super) fn hold_round<'a>(&'a self, pipe: &Pipeline) -> HeldRound<'a> {
        loop {
            let round = self.current_round(pipe);
            if round.job.claim() {
                round.held.store(1, Ordering::SeqCst);
                return HeldRound {
                    engine: self,
                    round,
                };
            }
            round.job.wait_landed();
        }
    }

    /// One round, run by whichever thread claimed it: write what is decided
    /// and not written, sync the written prefix of the log, raise the
    /// durable offset over it, and publish what that made publishable. A
    /// log that failed, in this round or before it, is rolled back here
    /// (P4).
    fn run_sync_round(&self, pipe: &Pipeline, round: &RingArc<Round>) {
        let tip = pipe.tip.load();
        self.sync_written(pipe, &tip);
        if tip.after.log.is_poisoned() {
            self.roll_back(pipe);
        }
        // The next round is in place before this one lands, so a thread
        // woken by the landing finds a round it can claim.
        pipe.round.replace(round, Round::new(self.me.clone()));
        // The slots this round made durable, and the ones behind them that
        // waited only for those: bounded by what was decided when it began.
        let _ = self.publish_upto(pipe, tip.index);
    }

    /// The sync of one round: the written prefix of the log `tip` names,
    /// unless the log already failed.
    fn sync_written(&self, pipe: &Pipeline, tip: &Decision) {
        let log = &tip.after.log;
        if log.is_poisoned() {
            return;
        }
        // The written prefix ends where the first unwritten record starts,
        // or after the newest decided slot when every record is written.
        let mut through = tip.after.next_off;
        let first = pipe.ring.published() + 1;
        for index in first..=tip.index {
            let Loaded::Ready(desc) = pipe.ring.load(index) else {
                continue;
            };
            let Some(decision) = desc.decision() else {
                continue;
            };
            let Some(place) = &decision.place else {
                continue;
            };
            if !Arc::ptr_eq(&decision.after.log, log) {
                continue;
            }
            self.write_slot(&desc);
            if !desc.is(WRITTEN) {
                through = place.offset;
                break;
            }
        }
        if through > log.durable() && !log.is_poisoned() {
            let _perf = PerfTimer::new(PerfTimerField::WriteWal);
            let start = self.statistics().and_then(|_| self.env.now_micros());
            match log.sync_through(through) {
                Ok(()) => {
                    if let Some(s) = self.statistics() {
                        s.add(Ticker::WalSyncCount, 1);
                        if let Some(micros) = self.elapsed_micros(start) {
                            s.record(Histogram::WalWriteTime, micros);
                        }
                    }
                }
                Err(err) => {
                    tracing::error!(error = %err, "syncing the write-ahead log failed");
                    log.poison(err);
                }
            }
        }
    }
}

/// The body of a sync round's job.
struct SyncRound {
    engine: std::sync::Weak<RegolithEngine>,
}

impl SyncRound {
    fn sync(self) {
        let Some(engine) = self.engine.upgrade() else {
            return;
        };
        let Some(pipe) = engine.pipeline.as_ref() else {
            return;
        };
        let _commit = InCommit::enter();
        // The round this job belongs to: the current one, since a round is
        // replaced only by its own body.
        let round = pipe.round.load();
        if round.held.load(Ordering::SeqCst) != 0 {
            // The thread that held the round did the device step itself.
            pipe.round.replace(&round, Round::new(engine.me.clone()));
            return;
        }
        engine.run_sync_round(pipe, &round);
    }
}

impl JobBody for SyncRound {
    fn run(self: Box<Self>) {
        (*self).sync();
    }

    /// A sync commits wait on is never left undone: a release runs it too.
    fn release(self: Box<Self>) {
        (*self).sync();
    }
}
