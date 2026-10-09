//! The permit core of [`Semaphore`](super::Semaphore), which
//! [`Mutex`](super::Mutex), [`ReentrantMutex`](super::ReentrantMutex),
//! [`OnceCell`](super::OnceCell) and the bounded channel build on too.
//!
//! The state word holds the free permits above a queued flag. A waiter
//! asking for `n` permits waits until the oldest waiter's request fits;
//! a smaller request behind a larger one waits its turn rather than
//! slipping past it, so a large request is never starved.

#![allow(unsafe_code)]

use core::future::Future;
use core::pin::Pin;
use core::task::{Context, Poll, Waker};

use super::internal::{Ordering, UnsafeCell};
use super::list::List;
use super::queue::{Arrivals, FIRST_BIT, Policy, Step, WaitQueue};
use super::waiter::{Cancel, Wait, WakeList};

/// Waiters may be queued: fast paths step aside.
const QUEUED: usize = 1 << FIRST_BIT;
const SHIFT: u32 = FIRST_BIT + 1;
const FLAGS: usize = (1 << SHIFT) - 1;
/// The most permits a semaphore can hold.
pub(super) const MAX: usize = usize::MAX >> SHIFT;

/// The permit core: a weighted FIFO semaphore with no value attached.
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

    /// Takes `n` permits if they are free and nobody waits.
    pub(super) fn try_acquire(&self, n: usize) -> bool {
        if n == 0 {
            return true;
        }
        let mut state = self.queue.state.load(Ordering::Relaxed);
        loop {
            if state & QUEUED != 0 || state >> SHIFT < n {
                return false;
            }
            match self.queue.state.compare_exchange_weak(
                state,
                state - (n << SHIFT),
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => return true,
                Err(actual) => state = actual,
            }
        }
    }

    /// Returns `n` permits taken earlier, handing them to waiters first.
    ///
    /// One `fetch_add` when nobody waits. It cannot overflow: the permits
    /// were in the semaphore before. A waiter queueing concurrently either
    /// was already flagged, and is drained here, or flags itself after
    /// this add and finds the permits in its own pass.
    pub(super) fn release(&self, n: usize) {
        if n == 0 {
            return;
        }
        let before = self.queue.state.fetch_add(n << SHIFT, Ordering::AcqRel);
        if before & QUEUED != 0 {
            self.transition(Step::Drain);
        }
    }

    /// Adds `n` new permits, handing them to waiters first.
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
                Step::Drain(next)
            } else {
                Step::Set(next)
            }
        });
    }

    /// Takes `n` permits for the drainer, which may jump the queued flag
    /// because it serves the queue.
    fn take_for_waiter(&self, n: usize) -> bool {
        let mut state = self.queue.state.load(Ordering::Acquire);
        loop {
            if state >> SHIFT < n {
                return false;
            }
            match self.queue.state.compare_exchange_weak(
                state,
                state - (n << SHIFT),
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => return true,
                Err(actual) => state = actual,
            }
        }
    }
}

impl Policy for RawSemaphore {
    fn queue(&self) -> &WaitQueue {
        &self.queue
    }

    fn pass(&self, arrivals: Arrivals, woken: &mut WakeList<'_>) -> usize {
        let pool = self.queue.pool();
        // SAFETY: only the drain role's holder runs a pass.
        self.waiting.with_mut(|waiting| unsafe {
            let waiting = &mut *waiting;
            waiting.absorb(arrivals, pool);
            waiting.tidy(&self.queue);
            while let Some(node) = waiting.front(pool) {
                let need = node.as_ref().payload();
                if !self.take_for_waiter(need) {
                    break;
                }
                waiting.pop_front();
                if !woken.grant(node) {
                    self.queue.state.fetch_add(need << SHIFT, Ordering::AcqRel);
                }
            }
            if waiting.is_empty() { QUEUED } else { 0 }
        })
    }
}

impl Drop for RawSemaphore {
    fn drop(&mut self) {
        let pool = self.queue.pool();
        // SAFETY: `&mut self` rules out a concurrent pass.
        self.waiting
            .with_mut(|waiting| unsafe { (*waiting).clear(pool) });
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
    wait: Wait,
}

impl PermitWait {
    pub(super) const fn new() -> Self {
        Self { wait: Wait::new() }
    }

    pub(super) fn is_queued(&self) -> bool {
        self.wait.is_queued()
    }

    pub(super) fn poll(&mut self, sem: &RawSemaphore, n: usize, waker: &Waker) -> Poll<()> {
        if self.wait.is_queued() {
            return self.wait.poll(&sem.queue, Some(waker)).map(drop);
        }
        if sem.try_acquire(n) {
            return Poll::Ready(());
        }
        sem.enqueue(&mut self.wait, n, waker, QUEUED);
        self.wait.poll(&sem.queue, None).map(drop)
    }

    /// Withdraws a pending wait, passing on permits granted meanwhile.
    pub(super) fn cancel(&mut self, sem: &RawSemaphore, n: usize) {
        match self.wait.cancel(&sem.queue) {
            Cancel::Idle => {}
            Cancel::Withdrawn => sem.withdrawn(),
            Cancel::Granted(_) => sem.release(n),
        }
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
