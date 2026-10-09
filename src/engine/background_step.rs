//! Flushes off the commit path (E9), and the bounded step a database with no
//! background worker owes instead (E16).
//!
//! A writer whose group fills the active memtable seals it and swaps in a
//! fresh one and a fresh log under the pipeline mutex, and does nothing more
//! there: the sealed memtable is written out after the mutex is released.
//!
//! - With a compaction worker, the seal wakes it, and the worker flushes
//!   every frozen memtable, oldest first, before it compacts.
//! - With none, the writer owes one bounded step, which it runs once its own
//!   commit returned from the pipeline: one flush of the oldest frozen
//!   memtable, or, with nothing frozen, one compaction pass. A step that
//!   leaves work behind owes the next one, so writes pace the work and none
//!   pays more than one step.
//!
//! A caller's code that panics in such a step (a listener, a prefix
//! extractor, a rate limiter) fails that flush alone; it is reported and
//! retried as any failing flush is, and latches nothing (`callback.rs`).
//!
//! Frozen memtables install in L0 oldest first (`LsmOrder.tla`, RED
//! FlushAnyOrder): every flush takes the `flushing` exclusion and the oldest
//! frozen memtable, so a memtable sealed later never lands in L0 under one
//! sealed before it, whichever thread flushes.

use super::RegolithEngine;
use super::background_health::{Hazard, Job};
use super::callback::InBackground;
use super::compaction::CompactionOutcome;
use crate::portability::Ordering;

impl RegolithEngine {
    /// Hand the memtable a writer just sealed to whoever flushes it: the
    /// worker when there is one, else the writer itself once it leaves the
    /// pipeline. Called under the pipeline mutex; takes no other lock when no
    /// worker runs, and only the scheduler's when one does.
    pub(super) fn flush_sealed_later(&self) {
        if self.has_worker {
            self.compaction.lock().notify();
        } else {
            self.background_owed.store(true, Ordering::Release);
        }
    }

    /// Run the step this thread's writes left owing, if any: one bounded
    /// step of background work on a database with no worker. A no-op, one
    /// atomic load, when nothing is owed.
    pub(crate) fn run_owed_step(&self) {
        if !self.background_owed.load(Ordering::Acquire)
            || !self.background_owed.swap(false, Ordering::AcqRel)
        {
            return;
        }
        // The writer's own commit already returned: a failure here is the
        // background's, recorded where the step records it, and not the
        // writer's. The stall triggers stop writes it keeps failing.
        if let Err(e) = self.run_one_background_step() {
            tracing::debug!(error = %e, "an owed background step failed");
        }
        if self.background_work_left() {
            self.background_owed.store(true, Ordering::Release);
        }
    }

    /// One bounded step of background work on the calling thread: flush the
    /// oldest frozen memtable if there is one, else run one compaction pass.
    /// `Contended` when another thread is flushing. A failed flush is
    /// [`crate::Error::BackgroundFailed`], as a stopped writer that retries one
    /// reports it.
    pub(crate) fn run_one_background_step(&self) -> Result<CompactionOutcome, crate::Error> {
        self.ensure_writable()?;
        let _background = InBackground::enter();
        if self.view.load().frozen.is_empty() {
            return Ok(self.run_one_compaction_pass()?);
        }
        let Some(flushing) = self.flusher.flushing.try_lock() else {
            return Ok(CompactionOutcome::Contended);
        };
        let flushed = self.flush_oldest_frozen(&flushing);
        drop(flushing);
        self.refresh_stall_level();
        self.stall_signal.notify_all();
        match flushed {
            Ok(_) => Ok(CompactionOutcome::DidWork),
            Err(source) => Err(crate::Error::BackgroundFailed {
                job: Job::Flush.name(),
                hazard: Hazard::of(&source).label(),
                source,
            }),
        }
    }

    /// Whether a database with no worker still owes background work: a
    /// frozen memtable to flush.
    fn background_work_left(&self) -> bool {
        !self.view.load().frozen.is_empty()
    }
}
