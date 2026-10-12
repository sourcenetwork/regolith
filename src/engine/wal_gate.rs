//! The gate every write of a positional log passes: what keeps the write of
//! a discarded commit from landing after the rollback that discarded it cut
//! the file (`wal_log.rs`).
//!
//! One word holds the log's write epoch and the number of writes in flight.
//! A write is counted in by a compare-and-swap that succeeds only while the
//! word still carries the epoch the write was decided in, and counted out
//! when its bytes are with the host. A rollback moves the epoch on, keeping
//! the count, and cuts the file once the count is zero.
//!
//! # Invariants
//!
//! - **WG1, a write of an older epoch never starts.** Its count in compares
//!   the epoch in the same step that counts it, so once the epoch moved no
//!   such write is counted in, and none writes uncounted.
//! - **WG2, after the epoch moved the count only falls.** Nothing is decided
//!   in the new epoch until the rollback that moved it is over, so the
//!   writes in flight then are the ones let in before, each of which leaves
//!   once. The rollback waits for exactly those, and for no thread that
//!   merely looked at the gate.
//! - **WG3, a rollback that may not wait is woken by the last write to
//!   leave.** A job a queue's poll steps registers its waker and looks at
//!   the count a last time; the write that takes the count to zero under a
//!   moved epoch wakes the waker registered. One of the two sees the other.

use std::task::Waker;

use super::io::atomic_waker::AtomicWaker;
use crate::sync::internal::{AtomicU64, Ordering, fence};

/// Bits of the word that count the writes in flight; the epoch is above
/// them.
const WRITER_BITS: u32 = 24;
const WRITERS: u64 = (1 << WRITER_BITS) - 1;

/// See the module docs.
pub(crate) struct Gate {
    /// `epoch << WRITER_BITS | writes in flight`.
    word: AtomicU64,
    /// The rollback parked until the writes in flight have left (WG3). One
    /// at a time: a rollback holds the pipeline's round.
    cleared: AtomicWaker,
}

impl Gate {
    /// A gate at epoch zero with nothing in flight.
    pub(crate) fn new() -> Self {
        Self {
            word: AtomicU64::new(0),
            cleared: AtomicWaker::new(),
        }
    }

    /// The epoch a write must have been decided in to be let in now.
    pub(crate) fn epoch(&self) -> u64 {
        self.word.load(Ordering::SeqCst) >> WRITER_BITS
    }

    /// Count a write decided in `epoch` in. `false` when the gate has moved
    /// on: the write is of a discarded commit and is not made (WG1).
    pub(crate) fn enter(&self, epoch: u64) -> bool {
        let mut word = self.word.load(Ordering::SeqCst);
        loop {
            if word >> WRITER_BITS != epoch {
                return false;
            }
            debug_assert!(
                word & WRITERS < WRITERS,
                "more writes in flight than the gate counts"
            );
            match self.word.compare_exchange_weak(
                word,
                word + 1,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => return true,
                Err(now) => word = now,
            }
        }
    }

    /// Count out a write that [`Self::enter`] let in for `epoch`.
    pub(crate) fn leave(&self, epoch: u64) {
        let left = self.word.fetch_sub(1, Ordering::SeqCst) - 1;
        if left & WRITERS == 0 && left >> WRITER_BITS != epoch {
            // The gate moved on under this write, and it was the last one
            // in flight: a rollback parked for it goes on (WG3). With the
            // fence in `clear_or_park`, one side sees the other.
            fence(Ordering::SeqCst);
            self.cleared.wake();
        }
    }

    /// Move the gate on to `epoch`: no write decided before is let in from
    /// here on (WG1). The writes in flight stay counted.
    pub(crate) fn turn(&self, epoch: u64) {
        debug_assert!(epoch < 1 << (u64::BITS - WRITER_BITS));
        let mut word = self.word.load(Ordering::SeqCst);
        loop {
            let turned = epoch << WRITER_BITS | word & WRITERS;
            match self
                .word
                .compare_exchange_weak(word, turned, Ordering::SeqCst, Ordering::SeqCst)
            {
                Ok(_) => return,
                Err(now) => word = now,
            }
        }
    }

    /// Whether no write is in flight.
    pub(crate) fn is_clear(&self) -> bool {
        self.word.load(Ordering::SeqCst) & WRITERS == 0
    }

    /// [`Self::is_clear`] for a rollback that may not wait: when a write is
    /// still in flight, `waker` is woken by the last one to leave, and
    /// `false` tells the caller to park (WG3). Called after [`Self::turn`].
    pub(crate) fn clear_or_park(&self, waker: &Waker) -> bool {
        if self.is_clear() {
            return true;
        }
        self.cleared.register(waker);
        fence(Ordering::SeqCst);
        self.is_clear()
    }
}

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering as StdOrdering};
    use std::task::Wake;

    struct Count(AtomicUsize);

    impl Wake for Count {
        fn wake(self: Arc<Self>) {
            self.0.fetch_add(1, StdOrdering::SeqCst);
        }
    }

    fn counting() -> (Arc<Count>, Waker) {
        let count = Arc::new(Count(AtomicUsize::new(0)));
        (Arc::clone(&count), Waker::from(count))
    }

    #[test]
    fn a_write_of_the_current_epoch_is_let_in_and_one_of_an_older_epoch_is_not() {
        let gate = Gate::new();
        assert_eq!(gate.epoch(), 0);
        assert!(gate.enter(0));
        assert!(!gate.is_clear());
        gate.leave(0);
        assert!(gate.is_clear());
        gate.turn(1);
        assert_eq!(gate.epoch(), 1);
        assert!(!gate.enter(0), "a write decided before the gate moved");
        assert!(gate.is_clear(), "a write turned away is never counted");
        assert!(gate.enter(1));
        gate.leave(1);
    }

    #[test]
    fn the_epoch_moves_with_writes_in_flight_and_keeps_them_counted() {
        let gate = Gate::new();
        assert!(gate.enter(0));
        assert!(gate.enter(0));
        gate.turn(7);
        assert_eq!(gate.epoch(), 7);
        assert!(!gate.is_clear());
        gate.leave(0);
        assert!(!gate.is_clear());
        gate.leave(0);
        assert!(gate.is_clear());
    }

    #[test]
    fn a_parked_rollback_is_woken_by_the_last_write_to_leave() {
        let gate = Gate::new();
        assert!(gate.enter(0));
        assert!(gate.enter(0));
        gate.turn(1);
        let (count, waker) = counting();
        assert!(!gate.clear_or_park(&waker), "two writes are in flight");
        gate.leave(0);
        assert_eq!(count.0.load(StdOrdering::SeqCst), 0, "one write is left");
        gate.leave(0);
        assert_eq!(count.0.load(StdOrdering::SeqCst), 1);
        assert!(gate.clear_or_park(&waker));
        assert_eq!(count.0.load(StdOrdering::SeqCst), 1, "nothing to wait for");
    }

    #[test]
    fn a_write_that_leaves_under_its_own_epoch_wakes_nobody() {
        let gate = Gate::new();
        let (count, waker) = counting();
        assert!(gate.enter(0));
        // Nothing moved the gate: the rollback that would park has not
        // begun, so no waker is taken.
        gate.cleared.register(&waker);
        gate.leave(0);
        assert_eq!(count.0.load(StdOrdering::SeqCst), 0);
    }
}
