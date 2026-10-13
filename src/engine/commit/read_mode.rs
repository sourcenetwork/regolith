//! Whose reads the decision of a slot may make (plan 4.10, D53).
//!
//! Deciding a transaction's slot validates it, and validation reads: the
//! newest version of each key it checks, which may be in a block the cache
//! does not hold. A slot is decided by whichever thread reaches it, so two
//! rules say what that thread may read:
//!
//! - **A commit made through a `CacheOnly` handle never reads the device,
//!   whichever thread decides it.** Its slot is validated with misses sent
//!   to the queue its handle names. A miss refuses the commit with the wait
//!   for the block: it takes no sequence and no record, and the ticket
//!   carries [`crate::TransactionError::WouldBlock`]. The block is read at
//!   that queue's next poll, and the commit made again then finds it.
//! - **A thread that must not read the device decides nobody's slot with
//!   it.** A `commit_nowait` call made through a `CacheOnly` handle helps
//!   the slots before its own, and one of them may belong to a commit that
//!   is allowed to read the device. The helper validates it from the cache
//!   alone. On a miss it decides nothing: deciding the slot with the device
//!   becomes a unit of the slot, which the helper leaves on its queue as it
//!   leaves a sync. A thread that may read the device decides the slot
//!   directly and never needs the unit; the helper's poll runs it otherwise,
//!   which is where a queue's owner does its I/O. The poll waits for no
//!   other thread: a round or a unit in the slot's way that another thread
//!   has parks the decision (`park.rs`).

use std::sync::Arc;
use std::task::Waker;

use super::super::RegolithEngine;
use super::super::io::job::{Job, JobBody, Step};
use super::super::io::scope;
use super::descriptor::{After, Decision, Descriptor, Verdict as Fate};
use super::park::Help;
use super::pipeline::Turn;
use crate::io_queue::wait::is_would_block;

/// Deciding one slot with the device, as a job.
struct DecideSlot {
    engine: std::sync::Weak<RegolithEngine>,
    index: u64,
}

impl DecideSlot {
    /// Decide every slot up to this one. Run by a poll or a blocking call,
    /// which read the device. `false` when a poll parked on a round or a
    /// unit in the way that another thread has.
    fn decide(&self, help: Help<'_>) -> bool {
        let Some(engine) = self.engine.upgrade() else {
            return true;
        };
        let Some(pipe) = engine.pipeline.as_ref() else {
            return true;
        };
        while let Turn::Blocked(job) = engine.help_decide(pipe, self.index, help, None) {
            if !matches!(help, Help::Wait) {
                return false;
            }
            engine.run_or_wait(&job);
        }
        true
    }
}

impl JobBody for DecideSlot {
    fn run(self: Box<Self>) {
        self.decide(Help::Wait);
    }

    /// On a queue's poll: parks instead of waiting for another thread.
    fn step(self: Box<Self>, waker: &Waker) -> Step {
        if self.decide(Help::Park(waker)) {
            Step::Done
        } else {
            Step::Parked(self)
        }
    }

    /// The pipeline cannot pass a slot nobody decided, so a release decides
    /// it too.
    fn release(self: Box<Self>) {
        self.decide(Help::Wait);
    }
}

impl RegolithEngine {
    /// Test-only: the unit that decides slot `index` with the device, as a
    /// helper that must not read it leaves it on its queue.
    #[cfg(test)]
    pub(super) fn decide_unit(&self, index: u64) -> Arc<Job> {
        Job::new(Box::new(DecideSlot {
            engine: self.me.clone(),
            index,
        }))
    }

    /// Decide slot `index` from `base` under the read rules of the module
    /// docs. `Err` is the unit that decides it with the device, for a thread
    /// that must not read it.
    pub(super) fn decide_reading(
        &self,
        index: u64,
        desc: &Descriptor,
        base: &After,
    ) -> Result<Decision, Arc<Job>> {
        if let Some(queue) = desc.read_queue() {
            let _scope = scope::cache_only(queue);
            return Ok(self.decide_work(index, desc, base));
        }
        // Whatever scope this thread is in holds: none for a thread that
        // reads the device, the helper's own queue for one that must not.
        let decision = self.decide_work(index, desc, base);
        // The verdict first: it is a field of the decision at hand, and the
        // scope is a thread-local read only a refused slot needs.
        if let Fate::Refused(err) = &decision.verdict
            && is_would_block(err)
            && scope::current().is_some()
        {
            let job = desc.decide_job.get_or_set(Job::new(Box::new(DecideSlot {
                engine: self.me.clone(),
                index,
            })));
            return Err(Arc::clone(job));
        }
        Ok(decision)
    }
}

#[cfg(test)]
#[path = "read_mode_tests.rs"]
mod tests;
