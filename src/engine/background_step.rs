//! Flushes off the commit path (E9), the bounded step a database with no
//! background worker owes instead (E16), and where that step runs: on the
//! queue of the thread whose call left it owing, or inline when that thread
//! has none (D53, `NonBlocking.tla` SelfStart and SelfIoNowhere).
//!
//! A writer whose group fills the active memtable seals it and swaps in a
//! fresh one and a fresh log under the pipeline mutex, and does nothing more
//! there: the sealed memtable is written out after the mutex is released.
//!
//! - With a compaction worker, the seal wakes it, and the worker flushes
//!   every frozen memtable, oldest first, before it compacts.
//! - With none, the writes owe one bounded step: one flush of the oldest
//!   frozen memtable, or, with nothing frozen, one compaction pass. A step
//!   that did work owes the next one, so writes pace the work and none pays
//!   more than one step. Every flush owes one too, so the write after the
//!   flush that brings L0 to `l0_compaction_trigger` compacts it (E16),
//!   where before nothing compacted until a stall trigger. A database with
//!   no worker also owes the disk check, once, from its open (D15).
//!
//! What is owed is started by the next write to leave the commit pipeline,
//! once its commit returned:
//!
//! - **On its thread's queue.** When the writing thread has an
//!   [`IoQueue`](crate::IoQueue) open on the database, the work is left
//!   there as a job, and runs when that thread polls: the write itself does
//!   no I/O it did not ask for. One such job waits at a time; it takes what
//!   is owed when it runs. A job the queue drops before it ran leaves the
//!   work owed for the next write.
//! - **Inline.** A thread with no queue runs it before its write returns, as
//!   before, bounded to one step.
//!
//! So a job regolith starts itself always lands on the starting thread's own
//! queue, or runs on that thread: never on a queue nobody polls for it
//! (RED SelfIoNowhere).
//!
//! A write stopped by a stall on a database with no worker and inline
//! compaction on leaves the step that relieves the stop the same way: one
//! step per poll on the writer's queue, continued while the stop holds
//! (`RegolithEngine::stopped`).
//!
//! A caller's code that panics in such a step (a listener, a prefix
//! extractor, a rate limiter) fails that flush alone; it is reported and
//! retried as any failing flush is, and latches nothing (`callback.rs`).
//!
//! Frozen memtables install in L0 oldest first (`LsmOrder.tla`, RED
//! FlushAnyOrder): every flush takes the `flushing` exclusion and the oldest
//! frozen memtable, so a memtable sealed later never lands in L0 under one
//! sealed before it, whichever thread flushes.

use std::sync::Weak;

use super::RegolithEngine;
use super::background_health::{Hazard, Job};
use super::callback::InBackground;
use super::compaction::CompactionOutcome;
use super::io::job::{Job as IoJob, JobBody};
use super::io::shared::QueueShared;
use crate::portability::Ordering;

/// Owed: one bounded step of flush or compaction.
pub(super) const OWED_STEP: u8 = 0b01;
/// Owed: the disk check a database with no worker runs once after open.
pub(super) const OWED_DISK_CHECK: u8 = 0b10;

impl RegolithEngine {
    /// Hand the memtable a writer just sealed to whoever flushes it: the
    /// worker when there is one, else the writer itself once it leaves the
    /// pipeline. Called under the pipeline mutex; takes no other lock when no
    /// worker runs, and only the scheduler's when one does.
    pub(super) fn flush_sealed_later(&self) {
        if self.has_worker {
            self.compaction.lock().notify();
        } else {
            self.owe(OWED_STEP);
        }
    }

    /// What a flush owes the background once it installed a table: a wake
    /// of the worker, or, with none, one bounded step the next write runs,
    /// which compacts once L0 reaches its trigger (E16).
    pub(super) fn after_flush(&self) {
        if self.has_worker {
            self.compaction.lock().notify();
        } else {
            self.owe(OWED_STEP);
        }
    }

    /// Owe the background `work` (`OWED_*` bits).
    pub(super) fn owe(&self, work: u8) {
        self.owed.fetch_or(work, Ordering::AcqRel);
    }

    /// Start what this thread's writes left owing, if anything: as a job on
    /// this thread's queue, or inline when it has none. A no-op, one atomic
    /// load, when nothing is owed.
    pub(crate) fn run_owed_step(&self) {
        if self.owed.load(Ordering::Acquire) == 0 {
            return;
        }
        if let Some(queue) = self.io().current_queue() {
            // One job waits at a time, and it takes what is owed when it
            // runs, this included.
            if self.owed_queued.swap(true, Ordering::AcqRel) {
                return;
            }
            let job = IoJob::new(Box::new(Owed {
                engine: self.me.clone(),
            }));
            if self.io().submit(&queue, job, None).is_ok() {
                return;
            }
            // Closing, or the queue went away meanwhile: run it here.
            self.owed_queued.store(false, Ordering::Release);
        }
        self.run_owed();
    }

    /// Run one round of what is owed on this thread: the disk check, then
    /// one bounded step. A step that did work, or found another thread doing
    /// it, may have left more, so it owes the next one; one that found
    /// nothing to do, or failed, owes nothing more until the next seal or
    /// flush, so a failing flush is not retried on every write: the stall
    /// triggers stop writes it keeps failing. The writer's own commit already
    /// returned, so a failure is the background's, recorded where the step
    /// records it.
    fn run_owed(&self) {
        let owed = self.owed.swap(0, Ordering::AcqRel);
        if owed & OWED_DISK_CHECK != 0 {
            super::disk_check::check(&*self.env, &self.disk_dir);
        }
        if owed & OWED_STEP == 0 {
            return;
        }
        let again = match self.run_one_background_step(false) {
            Ok(CompactionOutcome::DidWork | CompactionOutcome::Contended) => true,
            Ok(CompactionOutcome::Idle) => false,
            Err(e) => {
                tracing::debug!(error = %e, "an owed background step failed");
                false
            }
        };
        if again {
            self.owe(OWED_STEP);
        }
    }

    /// Leave the step that relieves a stop on `queue`, the stopped writer's,
    /// unless one waits already.
    pub(super) fn leave_stall_step(&self, queue: &QueueShared) {
        if self.stall_step_queued.swap(true, Ordering::AcqRel) {
            return;
        }
        let job = IoJob::new(Box::new(StallStep {
            engine: self.me.clone(),
        }));
        if self.io().submit(queue, job, None).is_err() {
            self.stall_step_queued.store(false, Ordering::Release);
        }
    }

    /// One step relieving a stop, on the thread that polled the queue it was
    /// left on. While the stop holds and steps make progress, the next one is
    /// left on this thread's queue for its next poll. A step that finds
    /// nothing to do too many times in a row, or fails, lands the stall's
    /// unit, so the writers waiting on it run again and are told why the
    /// stop will not clear.
    fn run_stall_step(&self) {
        self.stall_step_queued.store(false, Ordering::Release);
        if !matches!(self.stall_state(), Some((_, true))) {
            self.refresh_stall_level();
            return;
        }
        match self.run_one_background_step(false) {
            Ok(CompactionOutcome::DidWork | CompactionOutcome::Contended) => {
                self.stall_steps_idle.store(0, Ordering::Release);
            }
            Ok(CompactionOutcome::Idle) => {
                let idle = self.stall_steps_idle.fetch_add(1, Ordering::AcqRel) + 1;
                if idle > Self::MAX_IDLE_PASSES {
                    self.stall_signal.land();
                    return;
                }
            }
            Err(e) => {
                tracing::debug!(error = %e, "a step relieving a write stall failed");
                self.stall_signal.land();
                return;
            }
        }
        if matches!(self.stall_state(), Some((_, true)))
            && let Some(queue) = self.io().current_queue()
        {
            self.leave_stall_step(&queue);
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

/// The job that runs what writes left owing, on the queue of the thread
/// that started it.
struct Owed {
    engine: Weak<RegolithEngine>,
}

impl JobBody for Owed {
    fn run(self: Box<Self>) {
        if let Some(engine) = self.engine.upgrade() {
            engine.owed_queued.store(false, Ordering::Release);
            engine.run_owed();
        }
    }

    /// Left undone: what is owed stays owed, for the next write.
    fn release(self: Box<Self>) {
        if let Some(engine) = self.engine.upgrade() {
            engine.owed_queued.store(false, Ordering::Release);
        }
    }
}

/// The job that runs one step relieving a write stall, on the stopped
/// writer's queue.
struct StallStep {
    engine: Weak<RegolithEngine>,
}

impl JobBody for StallStep {
    fn run(self: Box<Self>) {
        if let Some(engine) = self.engine.upgrade() {
            engine.run_stall_step();
        }
    }

    /// Left undone: the next stopped write leaves another.
    fn release(self: Box<Self>) {
        if let Some(engine) = self.engine.upgrade() {
            engine.stall_step_queued.store(false, Ordering::Release);
        }
    }
}
