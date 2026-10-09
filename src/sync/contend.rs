//! The acquire every lock-like primitive shares: take what is free at
//! once, spin briefly, then wait in the queue with a bounded bypass.
//!
//! A caller takes what it asks for whenever it is free and no handoff is
//! owed, even past queued waiters: the thread that has just released a
//! lock and asks again takes it straight back, with no context switch.
//! When the first attempt fails and nobody is queued yet, the caller
//! retries for [`SPIN`] rounds with `core::hint::spin_loop` between them;
//! then it queues and returns `Pending`. A release wakes the front
//! waiter, whatever it asks for, and the waiters behind it the free
//! permits could serve; a woken waiter tries again when polled. Each time
//! it cannot take its whole request it counts one bypass; at
//! [`MAX_BYPASS`] it is owed a handoff, barging stops, and released
//! permits gather for it until its request is met. No clock is read:
//! fairness is counted, not timed.

use core::task::{Poll, Waker};

use super::queue::{HANDOFF, Policy, QUEUED};
use super::waiter::{Cancel, Park, Wait};

/// How many times a waiter can be passed over before it is owed a
/// handoff: a woken waiter that loses its retry this many times is handed
/// the next release directly, and nobody barges past it meanwhile.
#[cfg(not(loom))]
pub const MAX_BYPASS: u32 = 16;
/// Small under loom, so a model with a handful of operations reaches the
/// handoff.
#[cfg(loom)]
pub const MAX_BYPASS: u32 = 2;

/// Retries a contended acquire makes before it queues, and only while no
/// waiter is queued: once one is, the holder is likely suspended (a task
/// holding across an await, on this thread or another), and a spin only
/// burns the time it would have run. Measured with `benches/sync.rs`:
/// spinning on every contended poll, at 16 or 64 rounds, cost two to five
/// times the throughput of not spinning in every shape; 16 rounds that
/// stop at the first queued waiter measured the same as no spin. None
/// where a spin cannot help: on a single-threaded target nobody else runs
/// while the caller spins, and under loom a spin is only more
/// interleavings.
pub(super) const SPIN: u32 = if cfg!(any(
    loom,
    all(target_family = "wasm", not(target_feature = "atomics"))
)) {
    0
} else {
    16
};

/// A primitive whose waits take something and give it back.
pub(super) trait Lock: Policy {
    /// One attempt to take `need` the way a fresh caller would: whenever it
    /// is free, but never while a handoff is owed. On failure, the state it
    /// saw.
    fn try_take(&self, need: usize) -> Result<(), usize>;

    /// Gives back what a waiter held, handing it on.
    fn give_back(&self, need: usize);
}

/// [`Lock::try_take`], retried through the spin while nobody is queued
/// and no handoff is owed.
pub(super) fn spin_take<L: Lock>(lock: &L, need: usize) -> Result<(), usize> {
    let mut result = lock.try_take(need);
    for _ in 0..SPIN {
        match result {
            Ok(()) => return Ok(()),
            Err(seen) if seen & (HANDOFF | QUEUED) != 0 => return Err(seen),
            Err(_) => {}
        }
        core::hint::spin_loop();
        result = lock.try_take(need);
    }
    result
}

/// A future's contended acquire.
pub(super) struct Contend {
    wait: Wait,
    bypass: u32,
}

impl Contend {
    pub(super) const fn new() -> Self {
        Self {
            wait: Wait::new(),
            bypass: 0,
        }
    }

    pub(super) fn is_queued(&self) -> bool {
        self.wait.is_queued()
    }

    /// Ready once `need` is taken, by the caller's own attempt or by a
    /// handoff.
    pub(super) fn poll<L: Lock>(&mut self, lock: &L, need: usize, waker: &Waker) -> Poll<()> {
        let queue = lock.queue();
        // A loss in the poll that queues is not a bypass: nobody has
        // passed the waiter yet, the holder was simply there first.
        let mut arriving = !self.wait.is_queued();
        let mut park = if arriving {
            if spin_take(lock, need).is_ok() {
                return Poll::Ready(());
            }
            lock.enqueue(&mut self.wait, need, waker);
            self.wait.park(queue, None)
        } else {
            self.wait.park(queue, Some(waker))
        };
        loop {
            match park {
                Park::Granted(_) => {
                    // A nudge may have been pending when the grant came.
                    queue.consume_nudge();
                    return Poll::Ready(());
                }
                Park::Pending => return Poll::Pending,
                Park::Nudged => {
                    queue.consume_nudge();
                    match spin_take(lock, need) {
                        Ok(()) => {
                            self.cancel(lock, need);
                            return Poll::Ready(());
                        }
                        Err(seen) if seen & HANDOFF == 0 && !arriving => {
                            self.bypass += 1;
                            if self.bypass == MAX_BYPASS {
                                lock.owe(&self.wait);
                            }
                        }
                        Err(_) => {}
                    }
                    arriving = false;
                    park = self.wait.park(queue, Some(waker));
                }
            }
        }
    }

    /// Leaves the queue: the future was dropped, or took what it waits
    /// for on its own. What a handoff gave it meanwhile is passed on.
    pub(super) fn cancel<L: Lock>(&mut self, lock: &L, need: usize) {
        match self.wait.cancel(lock.queue()) {
            Cancel::Idle => {}
            Cancel::Withdrawn(woken) => lock.withdrawn(woken),
            Cancel::Granted(_) => {
                lock.queue().consume_nudge();
                lock.give_back(need);
            }
        }
    }
}
