//! The wait queue and the drain role every primitive builds on.
//!
//! A [`WaitQueue`] is one state word, a lock-free stack of arriving waiter
//! nodes, and the node pool. The two low bits of the state word belong to
//! the drain role; a primitive keeps its own state in the bits above them.
//!
//! # The drain role
//!
//! A drain pass is the only code that sorts arrivals, grants waiters and
//! prunes withdrawn ones, so it is single-consumer by construction and its
//! lists need no synchronization of their own. The role is a bit in the
//! state word, and nobody ever waits for it:
//!
//! - Every operation that may let a waiter run (a release, a new waiter, a
//!   withdrawal, a notification) ends in a [`Step::Drain`] transition: one
//!   compare-and-swap that applies the operation's own state change and
//!   either claims the role or, when another thread holds it, sets the
//!   dirty bit.
//! - The holder clears the dirty bit, then takes the arrival stack, runs
//!   its primitive's pass, and gives the role up with a compare-and-swap
//!   that requires the dirty bit still clear. If anything changed while it
//!   worked, that swap fails and it passes again.
//!
//! So every change made while a pass runs is seen by that pass or by a
//! later one, and every change made after the role is given up claims it
//! afresh: no wakeup is lost, and no call waits on another thread.
//!
//! Arrivals push onto a Treiber stack. Pushing is ABA-safe because nothing
//! pops single nodes: a pass takes the whole stack with one swap and
//! reverses it into arrival order.

#![allow(unsafe_code)]

use core::ptr::{self, NonNull};

use super::internal::{AtomicPtr, AtomicUsize, Ordering};
use super::waiter::{Pool, Wait, Waiter, WakeList, release_queued};

/// The drain role is held.
const DRAINING: usize = 1;
/// The state changed while the role was held, so its holder passes again.
const DIRTY: usize = 1 << 1;

/// The lowest state bit a primitive may use.
pub(super) const FIRST_BIT: u32 = 2;

/// What a [`Policy::transition`] does with the state it was shown.
pub(super) enum Step {
    /// Leave the state alone.
    Keep,
    /// Store this state.
    Set(usize),
    /// Store this state and make sure a drain pass sees it.
    Drain(usize),
}

pub(super) struct WaitQueue {
    pub(super) state: AtomicUsize,
    arrivals: AtomicPtr<Waiter>,
    cancels: AtomicUsize,
    pool: Pool,
}

impl WaitQueue {
    loom_const_fn! {
        pub(super) fn new(state: usize) -> Self {
            Self {
                state: AtomicUsize::new(state),
                arrivals: AtomicPtr::new(ptr::null_mut()),
                cancels: AtomicUsize::new(0),
                pool: Pool::new(),
            }
        }
    }

    pub(super) fn pool(&self) -> &Pool {
        &self.pool
    }

    /// How many waiters have withdrawn, ever; lists compare it against
    /// their last sweep.
    pub(super) fn cancels(&self) -> usize {
        self.cancels.load(Ordering::Relaxed)
    }

    pub(super) fn push(&self, node: NonNull<Waiter>) {
        let mut head = self.arrivals.load(Ordering::Relaxed);
        loop {
            // SAFETY: the caller owns `node` until this push publishes it.
            unsafe { node.as_ref() }.set_next(head);
            match self.arrivals.compare_exchange_weak(
                head,
                node.as_ptr(),
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => return,
                Err(actual) => head = actual,
            }
        }
    }

    /// Takes every node pushed so far, oldest first.
    fn take(&self) -> Arrivals {
        let mut cursor = self.arrivals.swap(ptr::null_mut(), Ordering::Acquire);
        let mut fifo: *mut Waiter = ptr::null_mut();
        while let Some(node) = NonNull::new(cursor) {
            // SAFETY: the swap handed over every node on the stack.
            let waiter = unsafe { node.as_ref() };
            cursor = waiter.next();
            waiter.set_next(fifo);
            fifo = node.as_ptr();
        }
        Arrivals(fifo)
    }
}

impl Drop for WaitQueue {
    fn drop(&mut self) {
        // No future outlives its primitive, so whatever is still stacked
        // has withdrawn and only the queue's reference is left.
        for node in self.take() {
            release_queued(node, &self.pool);
        }
    }
}

/// Nodes taken off the arrival stack, oldest first, each with the queue's
/// reference. A pass must consume them all.
pub(super) struct Arrivals(*mut Waiter);

impl Iterator for Arrivals {
    type Item = NonNull<Waiter>;

    fn next(&mut self) -> Option<NonNull<Waiter>> {
        let node = NonNull::new(self.0)?;
        // SAFETY: the chain holds the queue's reference to every node.
        self.0 = unsafe { node.as_ref() }.next();
        Some(node)
    }
}

/// A primitive's half of the drain protocol.
pub(super) trait Policy {
    fn queue(&self) -> &WaitQueue;

    /// One pass with the drain role held: absorb `arrivals`, grant what
    /// the state allows into `woken`, and return the state bits to clear
    /// on the way out, which stand only if nothing changed meanwhile.
    fn pass(&self, arrivals: Arrivals, woken: &mut WakeList<'_>) -> usize;

    /// Applies `f` to the state atomically and returns the state it last
    /// saw. A [`Step::Drain`] also claims the drain role, or marks its
    /// holder dirty; a claimed role is drained before this returns.
    fn transition(&self, mut f: impl FnMut(usize) -> Step) -> usize {
        let state = &self.queue().state;
        let mut current = state.load(Ordering::Acquire);
        loop {
            let (next, claim) = match f(current) {
                Step::Keep => return current,
                Step::Set(next) => (next, false),
                Step::Drain(next) if current & DRAINING != 0 => (next | DIRTY, false),
                Step::Drain(next) => (next | DRAINING, true),
            };
            match state.compare_exchange_weak(current, next, Ordering::AcqRel, Ordering::Acquire) {
                Ok(_) => {
                    if claim {
                        self.drain();
                    }
                    return current;
                }
                Err(actual) => current = actual,
            }
        }
    }

    /// Runs passes until one finishes with nothing new, then gives the
    /// role up and wakes what the passes granted. The caller holds the
    /// role.
    fn drain(&self) {
        let queue = self.queue();
        let mut woken = WakeList::new(&queue.pool);
        loop {
            queue.state.fetch_and(!DIRTY, Ordering::AcqRel);
            let clear = self.pass(queue.take(), &mut woken);
            let mut current = queue.state.load(Ordering::Acquire);
            while current & DIRTY == 0 {
                match queue.state.compare_exchange_weak(
                    current,
                    current & !(DRAINING | clear),
                    Ordering::AcqRel,
                    Ordering::Acquire,
                ) {
                    Ok(_) => return,
                    Err(actual) => current = actual,
                }
            }
        }
    }

    /// Queues `wait` with `payload` and publishes it by setting `flag`.
    fn enqueue(&self, wait: &mut Wait, payload: usize, waker: &core::task::Waker, flag: usize) {
        wait.enqueue(self.queue(), payload, waker);
        self.transition(|state| Step::Drain(state | flag));
    }

    /// Tells the drainer a waiter withdrew, so it can prune it and
    /// reconsider whatever it was blocking.
    fn withdrawn(&self) {
        self.queue().cancels.fetch_add(1, Ordering::Relaxed);
        self.transition(Step::Drain);
    }
}
