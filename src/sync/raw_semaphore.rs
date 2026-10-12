//! The permit core of [`Semaphore`](super::Semaphore), which
//! [`Mutex`](super::Mutex), [`ReentrantMutex`](super::ReentrantMutex),
//! [`OnceCell`](super::OnceCell) and the bounded channel build on too.
//!
//! The state word holds the free permits above the queue's bits. A
//! request takes its permits whenever enough are free and no handoff is
//! owed, past any waiters (see `contend`). A release nudges the oldest
//! waiters the freed permits could serve, oldest first and stopping at
//! the first that does not fit, so a large request at the front is not
//! skipped by the nudges for smaller ones behind it; while a handoff is
//! owed, it hands permits to the waiters in queue order instead.

#![allow(unsafe_code)]

use core::future::Future;
use core::pin::Pin;
use core::task::{Context, Poll, Waker};

use super::contend::{self, Contend, Lock};
use super::internal::{Ordering, UnsafeCell};
use super::list::List;
use super::queue::{
    Arrivals, FIRST_BIT, HANDOFF, Nudges, Policy, QUEUED, Step, WAKE_FRONT, WaitQueue, wants_drain,
};
use super::waiter::WakeList;

const SHIFT: u32 = FIRST_BIT;
const FLAGS: usize = (1 << SHIFT) - 1;
/// The most permits a semaphore can hold.
pub(super) const MAX: usize = usize::MAX >> SHIFT;

/// The permit core: a weighted semaphore with no value attached.
pub(super) struct RawSemaphore {
    queue: WaitQueue,
    waiting: UnsafeCell<List>,
}

// SAFETY: the waiting list is touched only by the drain role's holder.
unsafe impl Send for RawSemaphore {}
// SAFETY: as above.
unsafe impl Sync for RawSemaphore {}

impl RawSemaphore {
    loom_const_fn! {
        pub(super) fn new(permits: usize) -> Self {
            assert!(permits <= MAX, "a semaphore holds at most Semaphore::MAX_PERMITS permits");
            Self {
                queue: WaitQueue::new(permits << SHIFT),
                waiting: UnsafeCell::new(List::new()),
            }
        }
    }

    pub(super) fn available(&self) -> usize {
        self.queue.state.load(Ordering::Acquire) >> SHIFT
    }

    /// Takes `n` permits if they are free and no handoff is owed.
    pub(super) fn try_acquire(&self, n: usize) -> bool {
        self.try_take(n).is_ok()
    }

    /// Returns `n` permits taken earlier, nudging waiters if any.
    ///
    /// One `fetch_add` when nobody waits, or when a nudge is already on
    /// its way. It cannot overflow: the permits were in the semaphore
    /// before. A waiter queueing concurrently either was already flagged,
    /// and is seen by the drain here, or flags itself after this add and
    /// finds the permits in its own pass.
    pub(super) fn release(&self, n: usize) {
        if n == 0 {
            return;
        }
        let before = self.queue.state.fetch_add(n << SHIFT, Ordering::AcqRel);
        if wants_drain(before) {
            self.released();
        }
    }

    /// Adds `n` new permits, nudging waiters if any.
    ///
    /// # Panics
    ///
    /// When the semaphore would hold more than
    /// [`Semaphore::MAX_PERMITS`](super::Semaphore::MAX_PERMITS).
    pub(super) fn add(&self, n: usize) {
        if n == 0 {
            return;
        }
        self.transition(|state| {
            let permits = match (state >> SHIFT).checked_add(n) {
                Some(permits) if permits <= MAX => permits,
                _ => panic!("a semaphore holds at most Semaphore::MAX_PERMITS permits"),
            };
            let next = (state & FLAGS) | (permits << SHIFT);
            if state & QUEUED != 0 {
                Step::Drain(next | WAKE_FRONT)
            } else {
                Step::Set(next)
            }
        });
    }
}

impl Lock for RawSemaphore {
    fn admit(&self, state: usize, need: usize) -> Option<usize> {
        (state >> SHIFT >= need).then(|| state - (need << SHIFT))
    }

    fn give_back(&self, need: usize) {
        self.release(need);
    }

    fn try_take(&self, need: usize) -> Result<(), usize> {
        // Nothing to take, so nothing to wait for, owed handoff or not.
        if need == 0 {
            return Ok(());
        }
        contend::take(self, need, false)
    }
}

impl Policy for RawSemaphore {
    fn queue(&self) -> &WaitQueue {
        &self.queue
    }

    fn pass(&self, arrivals: Arrivals, woken: &mut WakeList<'_>, wake_front: bool) -> usize {
        let queue = &self.queue;
        // SAFETY: only the drain role's holder runs a pass.
        self.waiting.with_mut(|waiting| unsafe {
            let waiting = &mut *waiting;
            waiting.absorb(arrivals, queue);
            waiting.tidy(queue);
            if queue.state.load(Ordering::Acquire) & HANDOFF != 0 {
                while let Some(node) = waiting.front(queue) {
                    let need = node.as_ref().payload();
                    if !self.take_for_waiter(need) {
                        break;
                    }
                    waiting.pop_front();
                    if !woken.grant(node) {
                        queue.state.fetch_add(need << SHIFT, Ordering::AcqRel);
                    }
                }
            }
            // While nobody is owed, the queue competes: wake the waiters
            // the free permits could serve, oldest first. After a release,
            // wake the front whatever it asks for, so a request the free
            // permits cannot cover still tries, loses, counts the bypass,
            // and is owed a handoff in the end rather than starving behind
            // smaller callers.
            if !queue.hands_off() && waiting.front(queue).is_some() {
                let mut budget = queue.state.load(Ordering::Acquire) >> SHIFT;
                let mut nudges = Nudges::new(woken, queue);
                for (at, node) in waiting.iter().enumerate() {
                    let need = node.as_ref().payload();
                    if need > budget && !(at == 0 && wake_front) {
                        break;
                    }
                    nudges.nudge(node);
                    budget = budget.saturating_sub(need);
                }
                nudges.finish();
            }
            if waiting.front(queue).is_none() {
                QUEUED
            } else {
                0
            }
        })
    }
}

impl Drop for RawSemaphore {
    fn drop(&mut self) {
        let queue = &self.queue;
        // SAFETY: `&mut self` rules out a concurrent pass.
        self.waiting
            .with_mut(|waiting| unsafe { (*waiting).clear(queue) });
    }
}

#[cfg(all(test, not(loom)))]
impl RawSemaphore {
    /// Nodes on the waiting list, withdrawn ones included.
    pub(super) fn linked(&self) -> usize {
        // SAFETY: tests call this with no pass running.
        self.waiting.with(|waiting| unsafe { (*waiting).len() })
    }
}

/// A future's wait for permits on a [`RawSemaphore`].
pub(super) struct PermitWait {
    contend: Contend,
}

impl PermitWait {
    pub(super) const fn new() -> Self {
        Self {
            contend: Contend::new(),
        }
    }

    pub(super) fn is_queued(&self) -> bool {
        self.contend.is_queued()
    }

    pub(super) fn poll(&mut self, sem: &RawSemaphore, n: usize, waker: &Waker) -> Poll<()> {
        self.contend.poll(sem, n, waker)
    }

    /// Withdraws a pending wait, passing on permits handed over meanwhile.
    pub(super) fn cancel(&mut self, sem: &RawSemaphore, n: usize) {
        self.contend.cancel(sem, n);
    }
}

/// Permits held on a [`RawSemaphore`], returned on drop.
pub(super) struct RawPermit<'a> {
    sem: &'a RawSemaphore,
    n: usize,
}

impl RawPermit<'_> {
    /// Keeps the permits out of the semaphore for good.
    pub(super) fn forget(mut self) {
        self.n = 0;
    }
}

impl Drop for RawPermit<'_> {
    fn drop(&mut self) {
        self.sem.release(self.n);
    }
}

/// The future [`RawSemaphore::acquire`] returns.
pub(super) struct RawAcquire<'a> {
    sem: &'a RawSemaphore,
    n: usize,
    wait: PermitWait,
}

impl RawSemaphore {
    /// Waits for `n` permits.
    pub(super) fn acquire(&self, n: usize) -> RawAcquire<'_> {
        RawAcquire {
            sem: self,
            n,
            wait: PermitWait::new(),
        }
    }
}

impl<'a> Future for RawAcquire<'a> {
    type Output = RawPermit<'a>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<RawPermit<'a>> {
        let this = self.get_mut();
        this.wait
            .poll(this.sem, this.n, cx.waker())
            .map(|()| RawPermit {
                sem: this.sem,
                n: this.n,
            })
    }
}

impl Drop for RawAcquire<'_> {
    fn drop(&mut self) {
        self.wait.cancel(self.sem, self.n);
    }
}
