//! One unit of device I/O, run once however many queues wait on it.
//!
//! A unit is born in the `Free` state when the first `CacheOnly` read misses
//! its block. It moves forward exactly once per step:
//!
//! ```text
//! Free --claim (one CAS)--> Claimed --finish--> Done
//!   \--release (close, a dropped queue): claim, then finish with nothing--/
//! ```
//!
//! The claim is the only way to `Claimed`, so the work runs at most once.
//! `finish` writes the outcome, publishes `Done`, and then closes the list of
//! waiting queues with one swap and pushes one `Done` message to each queue
//! on it. A queue that registers after that swap is refused and reads the
//! outcome itself. So every queue that registered gets exactly one
//! completion, and none is lost.

#![allow(unsafe_code)]

use std::io;
use std::sync::Arc;

use super::Landed;
use super::shared::{Message, QueueShared};
use super::stack::{SHUT, Stack};
use crate::engine::block_cache::BlockCache;
use crate::sync::internal::{AtomicUsize, Ordering, UnsafeCell};

const FREE: usize = 0;
const CLAIMED: usize = 1;
const DONE: usize = 2;

/// What names one unit in the shared table: the block cache's key for the
/// block, and the per-block allocation guard of a size-limited read. Reads of
/// one block with the same guard share one unit.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct UnitKey {
    pub(crate) file_id: u64,
    pub(crate) offset: u64,
    pub(crate) guard: Option<usize>,
}

/// The device read a unit performs, filling the block cache as the blocking
/// read does and handing back what it read.
pub(crate) type Work = Box<dyn FnOnce(&BlockCache) -> io::Result<Landed> + Send>;

/// How a unit ended.
pub(crate) enum Outcome {
    /// The read succeeded.
    Landed(Landed),
    /// The read failed; the error is handed to one read of each waiting queue.
    Failed(Arc<io::Error>),
    /// Closed without reading: the database closed or the queue that held the
    /// unit was dropped. A read run again decides what to do.
    Released,
}

pub(crate) struct Unit {
    key: UnitKey,
    /// What the unit reads from the device: the frame of the block.
    bytes: usize,
    state: AtomicUsize,
    /// Taken by the claim holder.
    work: UnsafeCell<Option<Work>>,
    /// Written by the claim holder before `Done`, read only after it.
    outcome: UnsafeCell<Option<Outcome>>,
    /// The queues waiting on this unit, closed with [`SHUT`] by `finish`.
    waiters: Stack<Arc<QueueShared>>,
}

// SAFETY: `work` is only touched by the one thread whose claim succeeded,
// and `outcome` is written by that thread before `Done` is released and only
// read after `Done` is acquired. `Work` is `Send`, and an `Outcome` is
// `Send + Sync`.
unsafe impl Sync for Unit {}

impl Unit {
    pub(crate) fn new(key: UnitKey, bytes: usize, work: Work) -> Self {
        Self {
            key,
            bytes,
            state: AtomicUsize::new(FREE),
            work: UnsafeCell::new(Some(work)),
            outcome: UnsafeCell::new(None),
            waiters: Stack::new(),
        }
    }

    pub(crate) fn key(&self) -> UnitKey {
        self.key
    }

    pub(crate) fn bytes(&self) -> usize {
        self.bytes
    }

    pub(crate) fn is_done(&self) -> bool {
        self.state.load(Ordering::Acquire) == DONE
    }

    /// Nobody has claimed the unit yet: a waiting queue's owner may run it.
    pub(crate) fn is_free(&self) -> bool {
        self.state.load(Ordering::Acquire) == FREE
    }

    /// Take the unit for this thread with one compare-and-swap. `true` for
    /// exactly one caller over the unit's life; that caller must then
    /// [`run`](Self::run) or [`finish`](Self::finish) it.
    pub(crate) fn claim(&self) -> bool {
        self.state
            .compare_exchange(FREE, CLAIMED, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
    }

    /// Record `queue` as waiting. `false` when the unit already finished: the
    /// caller then reads [`outcome`](Self::outcome) itself.
    pub(crate) fn register(&self, queue: Arc<QueueShared>) -> bool {
        self.waiters.push(queue, SHUT).is_ok()
    }

    /// Run the work on this thread and finish. Only after this caller's
    /// [`claim`](Self::claim) succeeded.
    pub(crate) fn run(self: &Arc<Self>, cache: &BlockCache) {
        debug_assert_eq!(self.state.load(Ordering::Relaxed), CLAIMED);
        // A panic in the work still finishes the unit, so no waiting queue
        // is left on a claim nobody will ever complete.
        struct Unwind<'a>(Option<&'a Arc<Unit>>);
        impl Drop for Unwind<'_> {
            fn drop(&mut self) {
                if let Some(unit) = self.0.take() {
                    unit.finish(Outcome::Released);
                }
            }
        }
        let mut unwind = Unwind(Some(self));
        // SAFETY: the claim gave this thread `work`.
        let work = self.work.with_mut(|work| unsafe { (*work).take() });
        let outcome = match work {
            Some(work) => match work(cache) {
                Ok(landed) => Outcome::Landed(landed),
                Err(err) => Outcome::Failed(Arc::new(err)),
            },
            None => Outcome::Released,
        };
        unwind.0 = None;
        self.finish(outcome);
    }

    /// Close a unit nobody is running, without reading. `false` when another
    /// thread had already claimed it; that thread finishes it.
    pub(crate) fn release(self: &Arc<Self>) -> bool {
        if !self.claim() {
            return false;
        }
        self.finish(Outcome::Released);
        true
    }

    /// Publish `outcome` and hand one completion to every waiting queue.
    /// Only by the claim holder, once.
    fn finish(self: &Arc<Self>, outcome: Outcome) {
        // SAFETY: the claim holder is the only writer, and nobody reads the
        // cells before `Done` is published below.
        self.work.with_mut(|work| unsafe { *work = None });
        self.outcome
            .with_mut(|cell| unsafe { *cell = Some(outcome) });
        self.state.store(DONE, Ordering::Release);
        for queue in self.waiters.take(SHUT) {
            // A queue dropped since it registered refuses the message; it has
            // nobody left to tell.
            let _ = queue.deliver(Message::Done(Arc::clone(self)));
        }
    }

    /// How the unit ended, once it has.
    pub(crate) fn outcome(&self) -> Option<&Outcome> {
        if !self.is_done() {
            return None;
        }
        // SAFETY: `Done` was acquired above, after the one write; the cell is
        // never written again, and the reference lives no longer than `self`.
        self.outcome.with(|cell| unsafe { (*cell).as_ref() })
    }
}

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;

    fn key(offset: u64) -> UnitKey {
        UnitKey {
            file_id: 1,
            offset,
            guard: None,
        }
    }

    fn failing() -> Work {
        Box::new(|_| Err(io::Error::other("device says no")))
    }

    #[test]
    fn exactly_one_claim_wins() {
        let unit = Arc::new(Unit::new(key(0), 10, failing()));
        let wins = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..8)
                .map(|_| {
                    let unit = Arc::clone(&unit);
                    scope.spawn(move || unit.claim())
                })
                .collect();
            handles
                .into_iter()
                .filter_map(|handle| handle.join().ok())
                .filter(|won| *won)
                .count()
        });
        assert_eq!(wins, 1);
        assert!(!unit.release(), "a claimed unit is not released again");
    }

    #[test]
    fn a_run_publishes_its_outcome_and_refuses_later_registrations() {
        let cache = BlockCache::new(0);
        let unit = Arc::new(Unit::new(key(0), 10, failing()));
        assert!(unit.outcome().is_none());
        assert!(unit.claim());
        unit.run(&cache);
        assert!(unit.is_done());
        assert!(
            matches!(unit.outcome(), Some(Outcome::Failed(err)) if err.to_string() == "device says no")
        );
        assert!(!unit.register(Arc::new(QueueShared::new(
            super::super::shared::test_id(),
            1 << 20
        ))));
    }

    #[test]
    fn a_panicking_run_still_finishes_the_unit() {
        let cache = BlockCache::new(0);
        let unit = Arc::new(Unit::new(key(0), 10, Box::new(|_| panic!("work panics"))));
        assert!(unit.claim());
        let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unit.run(&cache)));
        assert!(caught.is_err());
        assert!(matches!(unit.outcome(), Some(Outcome::Released)));
    }

    #[test]
    fn a_release_closes_a_free_unit_without_running_it() {
        let unit = Arc::new(Unit::new(
            key(0),
            10,
            Box::new(|_| unreachable!("a released unit never runs")),
        ));
        assert!(unit.release());
        assert!(matches!(unit.outcome(), Some(Outcome::Released)));
        assert!(!unit.claim());
    }
}
