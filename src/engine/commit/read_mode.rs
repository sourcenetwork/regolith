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
//!   which is where a queue's owner does its I/O.

use std::sync::Arc;

use super::super::RegolithEngine;
use super::super::io::job::{Job, JobBody};
use super::super::io::scope;
use super::descriptor::{After, Decision, Descriptor, Verdict as Fate};
use super::pipeline::Turn;
use crate::io_queue::wait::is_would_block;

/// Deciding one slot with the device, as a job.
struct DecideSlot {
    engine: std::sync::Weak<RegolithEngine>,
    index: u64,
}

impl DecideSlot {
    fn run(self) {
        let Some(engine) = self.engine.upgrade() else {
            return;
        };
        let Some(pipe) = engine.pipeline.as_ref() else {
            return;
        };
        // Run by a poll or a blocking call, which read the device: every
        // slot up to this one is decided here, and a unit in the way is run
        // or waited for.
        while let Turn::Blocked(job) = engine.help_decide(pipe, self.index, true) {
            engine.run_or_wait(&job);
        }
    }
}

impl JobBody for DecideSlot {
    fn run(self: Box<Self>) {
        (*self).run();
    }

    /// The pipeline cannot pass a slot nobody decided, so a release decides
    /// it too.
    fn release(self: Box<Self>) {
        (*self).run();
    }
}

impl RegolithEngine {
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
        if scope::current().is_some()
            && let Fate::Refused(err) = &decision.verdict
            && is_would_block(err)
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
