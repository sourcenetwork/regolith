//! The claim word and waiter list every single-flight unit shares.
//!
//! A block read (`unit.rs`) and a job (`job.rs`) are both run once however
//! many queues wait on them. Both move through the same three states:
//!
//! ```text
//! Free --claim (one CAS)--> Claimed --land--> Done
//! ```
//!
//! The claim is the only way to `Claimed`, so the work runs at most once.
//! `land` publishes `Done` and then closes the list of waiting queues with
//! one swap, handing the caller every queue that registered. A queue that
//! registers after that swap is refused and reads the outcome itself. So
//! every queue that registered is handed to the lander exactly once, and
//! none is lost.

use std::sync::Arc;

use super::shared::QueueShared;
use super::stack::{SHUT, Stack, Taken};
use crate::sync::internal::{AtomicUsize, Ordering};

const FREE: usize = 0;
const CLAIMED: usize = 1;
const DONE: usize = 2;

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

    /// Take the unit for this thread with one compare-and-swap. `true` for
    /// exactly one caller over the unit's life; that caller must then land
    /// it.
    pub(crate) fn claim(&self) -> bool {
        self.state
            .compare_exchange(FREE, CLAIMED, Ordering::AcqRel, Ordering::Acquire)
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
