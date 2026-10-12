//! The acquire every lock-like primitive shares: take what is free at
//! once, otherwise wait in the queue with a bounded bypass.
//!
//! A caller takes what it asks for whenever it is free and no handoff is
//! owed, even past queued waiters: the thread that has just released a
//! lock and asks again takes it straight back, with no context switch.
//! When that one attempt fails, the caller queues and returns `Pending`;
//! it does not spin first. A release wakes the front waiter, whatever it
//! asks for, and the waiters behind it the free permits could serve; a
//! woken waiter tries again when polled. Each time it cannot take its
//! whole request it counts one bypass. The attempt that would be its
//! [`MAX_BYPASS`]th loss is owed a handoff in the same compare-and-swap
//! that finds it short, so barging stops before anything more is freed,
//! and released permits gather for it until its request is met. No clock
//! is read: fairness is counted, not timed.
//!
//! Why no spin before queueing, measured with `benches/sync.rs`: spinning
//! on every contended poll, at 16 or 64 rounds, cost two to five times the
//! throughput in every shape. Spinning 16 rounds only while nobody was
//! queued measured within 6% of not spinning across threads in every
//! shape (medians of six runs on a loaded host, less than the run-to-run
//! spread), and 9% slower with two tasks on one thread, where the holder
//! cannot run until the spinner gives up.

use core::task::{Poll, Waker};

use super::internal::Ordering;
use super::queue::{HANDOFF, Policy};
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

/// A primitive whose waits take something and give it back.
pub(super) trait Lock: Policy {
    /// `state` with `need` taken, when `state` has room for it; the owed
    /// bit aside.
    fn admit(&self, state: usize, need: usize) -> Option<usize>;

    /// Gives back what a waiter held, handing it on.
    fn give_back(&self, need: usize);

    /// One attempt to take `need` the way a fresh caller would: whenever it
    /// is free, but never while a handoff is owed. On failure, the state it
    /// saw.
    fn try_take(&self, need: usize) -> Result<(), usize> {
        take(self, need, false)
    }

    /// Takes `need` for a handoff, which may pass the owed bit because it
    /// serves the queue.
    fn take_for_waiter(&self, need: usize) -> bool {
        take(self, need, true).is_ok()
    }

    /// A queued waiter's attempt that would be its last counted loss: it
    /// takes `need` as [`try_take`](Self::try_take) would, or in the same
    /// compare-and-swap is owed a handoff (see `Policy::owe_or_take`).
    fn take_or_owe(&self, wait: &Wait, need: usize) -> Result<(), usize> {
        self.owe_or_take(wait, |state| self.admit(state, need))
    }
}

/// One compare-and-swap loop taking `need` through [`Lock::admit`]; past
/// an owed handoff only for the drain that hands it out.
pub(super) fn take<L: Lock + ?Sized>(lock: &L, need: usize, for_waiter: bool) -> Result<(), usize> {
    let (success, failure) = if for_waiter {
        (Ordering::AcqRel, Ordering::Acquire)
    } else {
        (Ordering::Acquire, Ordering::Relaxed)
    };
    let state = &lock.queue().state;
    let mut current = state.load(failure);
    loop {
        let next = match lock.admit(current, need) {
            Some(next) if for_waiter || current & HANDOFF == 0 => next,
            _ => return Err(current),
        };
        match state.compare_exchange_weak(current, next, success, failure) {
            Ok(_) => return Ok(()),
            Err(actual) => current = actual,
        }
    }
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
            if lock.try_take(need).is_ok() {
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
                    let attempt = if !arriving && self.bypass + 1 == MAX_BYPASS {
                        lock.take_or_owe(&self.wait, need)
                    } else {
                        lock.try_take(need)
                    };
                    match attempt {
                        Ok(()) => {
                            self.cancel(lock, need);
                            return Poll::Ready(());
                        }
                        Err(seen) if seen & HANDOFF == 0 && !arriving => self.bypass += 1,
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

#[cfg(all(test, not(loom)))]
mod tests {
    use core::cell::Cell;

    use super::super::queue::{Arrivals, WaitQueue};
    use super::super::raw_semaphore::RawSemaphore;
    use super::super::test_support::Polled;
    use super::super::waiter::WakeList;
    use super::*;

    /// A semaphore whose waiter runs `after_loss` right after an attempt
    /// of its fails, before its poll goes on: what another thread could do
    /// between the two.
    struct Gap<'a> {
        sem: &'a RawSemaphore,
        after_loss: Cell<Option<Box<dyn FnOnce() + 'a>>>,
    }

    impl Gap<'_> {
        fn lost(&self, attempt: Result<(), usize>) -> Result<(), usize> {
            if attempt.is_err()
                && let Some(between) = self.after_loss.take()
            {
                between();
            }
            attempt
        }
    }

    impl Policy for Gap<'_> {
        fn queue(&self) -> &WaitQueue {
            self.sem.queue()
        }

        fn pass(&self, arrivals: Arrivals, woken: &mut WakeList<'_>, wake_front: bool) -> usize {
            self.sem.pass(arrivals, woken, wake_front)
        }
    }

    impl Lock for Gap<'_> {
        fn admit(&self, state: usize, need: usize) -> Option<usize> {
            self.sem.admit(state, need)
        }

        fn give_back(&self, need: usize) {
            self.sem.give_back(need);
        }

        fn try_take(&self, need: usize) -> Result<(), usize> {
            self.lost(self.sem.try_take(need))
        }

        fn take_or_owe(&self, wait: &Wait, need: usize) -> Result<(), usize> {
            self.lost(self.sem.take_or_owe(wait, need))
        }
    }

    #[test]
    fn nothing_barges_between_a_waiters_last_loss_and_its_handoff() {
        let sem = RawSemaphore::new(1);
        let barged = Cell::new(false);
        let gap = Gap {
            sem: &sem,
            after_loss: Cell::new(None),
        };
        assert!(sem.try_acquire(1));
        let mut contend = Contend::new();
        let mut waiter = Polled::new(core::future::poll_fn(|cx| {
            contend.poll(&gap, 1, cx.waker())
        }));
        waiter.pending();
        for round in 1..=MAX_BYPASS {
            sem.release(1);
            assert_eq!(waiter.wakes() as u32, round, "a release nudges it");
            assert!(sem.try_acquire(1), "a free permit is taken past it");
            if round < MAX_BYPASS {
                waiter.pending();
            }
        }
        // Its last loss: the holder lets go and someone asks at once,
        // before the waiter's poll returns.
        gap.after_loss.set(Some(Box::new(|| {
            sem.release(1);
            barged.set(sem.try_acquire(1));
        })));
        let served = waiter.poll().is_ready();
        assert!(
            !barged.get(),
            "a barger took the permit freed after the waiter's last counted loss"
        );
        assert!(served, "the freed permit is handed to the waiter");
        assert!(!sem.try_acquire(1), "the waiter holds it");
        sem.release(1);
        assert!(sem.try_acquire(1), "barging resumes once it is served");
    }
}
