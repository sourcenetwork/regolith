//! The claim word and waiter list every single-flight unit shares.
//!
//! A block read (`unit.rs`) and a job (`job.rs`) are both run once however
//! many queues wait on them. Both move through the same states:
//!
//! ```text
//! Free --claim (one CAS)--> Claimed --land--> Done
//!   ^                        |
//!   |                        +--park (a block read whose reopen found no
//!   +--unpark (one CAS)-- Parked      open-file slot, D60)
//! ```
//!
//! The claim is the only way to `Claimed`, so the work runs on one thread
//! at a time and lands at most once. `land` publishes `Done` and then closes
//! the list of waiting queues with one swap, handing the caller every queue
//! that registered. A queue that registers after that swap is refused and
//! reads the outcome itself. So every queue that registered is handed to the
//! lander exactly once, and none is lost.
//!
//! Only a block read parks: its holder gives the claim up without landing,
//! and the unit is neither run nor landed until it is unparked (a slot
//! freed) or released (close, a dropped queue). A parked flight is still in
//! flight, so queues go on registering on it. A job never parks.

use std::sync::Arc;

use super::shared::QueueShared;
use super::stack::{SHUT, Stack, Taken};
use crate::sync::internal::{AtomicUsize, Ordering};

const FREE: usize = 0;
const CLAIMED: usize = 1;
const DONE: usize = 2;
const PARKED: usize = 3;

pub(crate) struct Flight {
    state: AtomicUsize,
    /// The queues waiting on this unit, closed with [`SHUT`] by `land`.
    waiters: Stack<Arc<QueueShared>>,
}

impl Flight {
    pub(crate) fn new() -> Self {
        Self {
            state: AtomicUsize::new(FREE),
            waiters: Stack::new(),
        }
    }

    pub(crate) fn is_done(&self) -> bool {
        self.state.load(Ordering::Acquire) == DONE
    }

    /// Nobody has claimed the unit yet.
    pub(crate) fn is_free(&self) -> bool {
        self.state.load(Ordering::Acquire) == FREE
    }

    /// Whether the unit is parked.
    #[cfg(test)]
    pub(crate) fn is_parked(&self) -> bool {
        self.state.load(Ordering::Acquire) == PARKED
    }

    /// Take the unit for this thread with one compare-and-swap. `true` for
    /// one caller at a time (exactly one over the unit's life unless its
    /// holder parks it); that caller must then land or park it.
    pub(crate) fn claim(&self) -> bool {
        self.state
            .compare_exchange(FREE, CLAIMED, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
    }

    /// Take the unit to close it without running it, whether nobody has
    /// claimed it or its holder parked it. `false` when a thread holds it
    /// claimed or it has landed.
    pub(crate) fn claim_to_release(&self) -> bool {
        let mut state = self.state.load(Ordering::Acquire);
        loop {
            if state != FREE && state != PARKED {
                return false;
            }
            match self
                .state
                .compare_exchange(state, CLAIMED, Ordering::AcqRel, Ordering::Acquire)
            {
                Ok(_) => return true,
                Err(now) => state = now,
            }
        }
    }

    /// Give the claim up without landing: the unit is neither run nor
    /// landed until [`unpark`](Self::unpark) or
    /// [`claim_to_release`](Self::claim_to_release). Only the claim holder
    /// writes a claimed unit's state, so a store suffices; `Release` hands
    /// what the holder left behind to whoever claims it next.
    pub(crate) fn park(&self) {
        debug_assert_eq!(self.state.load(Ordering::Relaxed), CLAIMED);
        self.state.store(PARKED, Ordering::Release);
    }

    /// Make a parked unit claimable again. `true` for the one call that
    /// did; `false` when it was not parked (unparked already, released, or
    /// landed).
    pub(crate) fn unpark(&self) -> bool {
        self.state
            .compare_exchange(PARKED, FREE, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
    }

    /// Record `queue` as waiting. `false` when the unit already landed: the
    /// caller then reads the outcome itself.
    pub(crate) fn register(&self, queue: Arc<QueueShared>) -> bool {
        self.waiters.push(queue, SHUT).is_ok()
    }

    /// Publish `Done` and close the waiter list, returning every queue that
    /// registered. Only by the claim holder, once, after it wrote the
    /// outcome: the `Release` store orders that write before `Done`.
    pub(crate) fn land(&self) -> Taken<Arc<QueueShared>> {
        debug_assert_eq!(self.state.load(Ordering::Relaxed), CLAIMED);
        self.state.store(DONE, Ordering::Release);
        self.waiters.take(SHUT)
    }
}
