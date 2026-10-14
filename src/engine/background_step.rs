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
//!   memtable, or, with nothing frozen, one compaction pass. A step that did
//!   work owes the next one, so writes pace the work and none pays more than
//!   one step. Every flush owes one too, so the write after the flush that
//!   brings L0 to `l0_compaction_trigger` compacts it (E16), where before
//!   nothing compacted until a stall trigger.
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

    /// What a flush owes the background once it installed a table: a wake
    /// of the worker, or, with none, one bounded step the next write runs,
    /// which compacts once L0 reaches its trigger (E16).
    pub(super) fn after_flush(&self) {
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
        // A step that did work, or found another thread doing it, may have
        // left more: the next write takes the next step. One that found
        // nothing to do, or failed, owes nothing more until the next seal
        // or flush, so a failing flush is not retried on every write; the
        // stall triggers stop writes it keeps failing. The writer's own
        // commit already returned, so a failure is the background's,
        // recorded where the step records it.
        let again = match self.run_one_background_step(false) {
            Ok(CompactionOutcome::DidWork | CompactionOutcome::Contended) => true,
            Ok(CompactionOutcome::Idle) => false,
            Err(e) => {
                tracing::debug!(error = %e, "an owed background step failed");
                false
            }
        };
        if again {
            self.background_owed.store(true, Ordering::Release);
        }
    }

    /// One bounded step of background work on the calling thread: flush the
    /// oldest frozen memtable if there is one, else run one compaction pass.
    /// `Contended` when another thread is flushing, or, unless `wait`, holds
    /// the compaction lock. A failed flush is
    /// [`crate::Error::BackgroundFailed`], as a stopped writer that retries one
    /// reports it.
    pub(crate) fn run_one_background_step(
        &self,
        wait: bool,
    ) -> Result<CompactionOutcome, crate::Error> {
        self.ensure_writable()?;
        let _background = InBackground::enter();
        if self.view.load().frozen.is_empty() {
            return Ok(self.run_one_compaction_pass_on(wait)?);
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
}
