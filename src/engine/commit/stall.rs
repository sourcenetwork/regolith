//! The write stall as a unit writers wait on, completed on each writer's own
//! queue when the stall clears (D23, plan 4.10).
//!
//! A write stopped by a stall threshold applies nothing and returns
//! [`WouldBlock::Stall`](crate::WouldBlock::Stall) at once, with a
//! [`StallWait`](crate::StallWait). Every writer stopped during one stall
//! waits on the same *passive* job (`engine::io::job`): no poll runs it, and
//! it lands only when the stall clears.
//!
//! - **Who clears it.** Whoever makes the progress that clears the stall
//!   re-classifies it here ([`StallSignal::refresh`]): a flush on a worker or
//!   on a writer's queue, a compaction pass, a rotation, an ingest. When
//!   writes are no longer stopped it lands the job, which pushes one
//!   completion to each stopped writer's queue and completes each wait with
//!   no queue directly.
//! - **No lost wakeup.** A writer gets or installs the job, registers its
//!   wait on it, and only then classifies the stall again: if the stall
//!   cleared in between, the writer lands the job itself. A clearer stores
//!   the level before it takes the job. So either the clearer finds the
//!   writer's job, or the writer sees the cleared stall.
//! - **No thread waits.** Nothing here parks or sleeps; the slowdown delay
//!   and the timed wait a stopped writer used to park on are gone.

use std::sync::Arc;

use kovan::Atom;

use super::super::io::IoRuntime;
use super::super::io::job::{Delivery, Job};
use super::super::io::shared::{QueueShared, WaitSlot};
use super::super::read_view::ReadViewCell;
use super::super::{EngineOptions, stall_state};
use crate::StallWait;
use crate::portability::{AtomicU8, Ordering};

/// The stall writers are stopped on now, if any, and the level writers cache.
pub(crate) struct StallSignal {
    view: Arc<ReadViewCell>,
    options: EngineOptions,
    /// The level writers check on every write: 0 none, 1 slowdown, 2 stop.
    level: Arc<AtomicU8>,
    /// The unit writers stopped since the stall began wait on.
    current: Atom<Option<Arc<Job>>>,
}

impl StallSignal {
    pub(crate) fn new(
        view: Arc<ReadViewCell>,
        options: EngineOptions,
        level: Arc<AtomicU8>,
    ) -> Self {
        Self {
            view,
            options,
            level,
            current: Atom::new(None),
        }
    }

    /// A signal over an empty view of `versions`, for a test that starts
    /// workers on their own.
    #[cfg(test)]
    pub(crate) fn for_tests(versions: &super::super::read_view::VersionStore) -> Self {
        use super::super::memtable::{MemTable, MemTableConfig};
        use super::super::read_view::ReadView;
        let view = Arc::new(ReadViewCell::new(ReadView {
            active: Arc::new(MemTable::new(&MemTableConfig::default()).expect("memtable")),
            frozen: Vec::new(),
            version: versions.lock().current(),
        }));
        Self::new(view, EngineOptions::default(), Arc::new(AtomicU8::new(0)))
    }

    /// The thresholds against the current view: `None`, or the reason and
    /// whether writes are stopped (`true`) or slowed (`false`).
    pub(crate) fn classify(&self) -> Option<(&'static str, bool)> {
        stall_state::classify(&self.view.load(), &self.options)
    }

    /// Re-classify after work that can change the thresholds' inputs (a
    /// rotation, a flush, a compaction pass, an ingest), store the level
    /// writers cache, and, once writes are no longer stopped, land the unit
    /// stopped writers wait on.
    pub(crate) fn refresh(&self) {
        let level = match self.classify() {
            None => 0,
            Some((_, false)) => 1,
            Some((_, true)) => 2,
        };
        // Stored before the unit is taken: a writer that registered after the
        // take sees this level when it classifies again (module docs).
        self.level.store(level, Ordering::Release);
        if level < 2 {
            self.land();
        }
    }

    /// Land the unit stopped writers wait on now, whatever the stall: close,
    /// and a writer that found the stall cleared after it registered.
    pub(crate) fn land(&self) {
        if let Some(job) = self.current.swap(None).as_ref() {
            job.release();
        }
    }

    /// A wait for the stall `reason` to clear, for a write that stopped on
    /// it. Recorded on `queue` when the writer's thread has one, so it is
    /// completed at that queue's poll; else completed directly by whoever
    /// clears the stall.
    pub(crate) fn wait(
        &self,
        io: &IoRuntime,
        queue: Option<Arc<QueueShared>>,
        reason: &'static str,
    ) -> StallWait {
        let job = self.unit();
        let slot = Arc::new(WaitSlot::new());
        let waiter = Arc::clone(&slot) as Arc<dyn Delivery>;
        let id = queue.as_ref().map(|queue| queue.id());
        let recorded = match &queue {
            // The queue's owner registers on the unit at its next poll; a
            // unit that landed by then is told at once (`IoQueue::accept_job`).
            Some(queue) => io.wait_on(queue, Arc::clone(&job), Some(Arc::clone(&waiter))),
            None => false,
        };
        // No queue, or one dropped meanwhile: the lander tells the wait
        // itself; refused when it landed already.
        if !recorded && !job.listen(waiter) {
            slot.complete();
        }
        // Classified again only now that the wait is recorded, so a clearer
        // that came before the registration is not missed.
        if self.classify().is_none_or(|(_, stopped)| !stopped) {
            self.refresh();
        }
        StallWait::new(slot, job, id, reason)
    }

    /// The unit for the stall now, installed by the first writer to stop.
    fn unit(&self) -> Arc<Job> {
        loop {
            let current = self.current.load();
            if let Some(job) = current.as_ref()
                && !job.is_done()
            {
                return Arc::clone(job);
            }
            let fresh = Job::passive();
            if self
                .current
                .compare_and_swap(&current, Some(Arc::clone(&fresh)))
                .is_ok()
            {
                return fresh;
            }
        }
    }
}

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;
    use crate::column_family::{DEFAULT_CF_ID, prefix_key};
    use crate::engine::{DurabilityMode, RegolithEngine};
    use crate::{IoBudget, WriteBatchOp};

    fn stopped_engine() -> (tempfile::TempDir, Arc<RegolithEngine>) {
        let dir = tempfile::TempDir::new().unwrap();
        let engine = RegolithEngine::open(
            dir.path(),
            EngineOptions {
                max_background_compactions: 0,
                level0_stop_writes_trigger: 1,
                l0_compaction_trigger: 1,
                ..EngineOptions::default()
            },
        )
        .unwrap();
        engine
            .apply_batch(
                vec![WriteBatchOp::Put {
                    key: prefix_key(DEFAULT_CF_ID, b"k"),
                    value: b"v".to_vec(),
                }],
                DurabilityMode::Eventual,
                false,
            )
            .unwrap();
        engine.flush_active_memtable().unwrap();
        (dir, engine)
    }

    #[test]
    fn a_wait_with_no_queue_is_completed_by_whoever_clears_the_stall() {
        let (_dir, engine) = stopped_engine();
        let signal = engine.stall_signal();
        assert!(matches!(signal.classify(), Some((_, true))));
        let wait = signal.wait(engine.io(), None, "stop");
        assert!(!wait.is_ready());
        let again = signal.wait(engine.io(), None, "stop");
        assert!(!again.is_ready());
        engine.run_one_compaction_pass().unwrap();
        assert!(
            wait.is_ready(),
            "the pass cleared the stall and landed the unit"
        );
        assert!(again.is_ready(), "one unit for every writer of the stall");
    }

    #[test]
    fn a_wait_on_a_queue_is_completed_only_at_that_queues_poll() {
        let (_dir, engine) = stopped_engine();
        let signal = engine.stall_signal();
        let mut queue = engine.io_queue();
        let shared = engine.io().queue(queue.id());
        let wait = signal.wait(engine.io(), shared, "stop");
        queue.poll(IoBudget::ALL);
        assert!(!wait.is_ready());
        engine.run_one_compaction_pass().unwrap();
        assert!(!wait.is_ready(), "cleared, but not delivered yet");
        assert_eq!(queue.poll(IoBudget::ALL).completed, 1);
        assert!(wait.is_ready());
    }

    #[test]
    fn a_wait_for_a_stall_that_already_cleared_is_ready_at_once() {
        let (_dir, engine) = stopped_engine();
        engine.run_one_compaction_pass().unwrap();
        let wait = engine.stall_signal().wait(engine.io(), None, "stop");
        assert!(wait.is_ready());
    }
}
