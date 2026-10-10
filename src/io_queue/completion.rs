//! The shared half of a ticket: an outcome decided once, then delivered
//! once, on the thread that owns the ticket's queue.
//!
//! A ticket ([`CommitTicket`](crate::CommitTicket),
//! [`JobTicket`](crate::JobTicket)) moves through four states:
//!
//! ```text
//! Pending --decide--> Decided --deliver--> Delivering --> Ready
//! ```
//!
//! - **Decide** stores the outcome. Whoever learns it does this, on any
//!   thread: a worker that ran a foreground job, or, for a commit whose group
//!   was still owed its fsync, the delivering thread itself, which resolves
//!   the outcome from the group the moment it is told the group landed.
//! - **Deliver** is the one step that makes the outcome visible to the
//!   ticket's holder. It runs on the thread that owns the ticket's queue, at
//!   the `poll` that takes the completion in (or on the deciding thread, for
//!   a ticket with no queue). One compare-and-swap from `Decided` to
//!   `Delivering` makes it run once however many parties reach for it. It
//!   runs, in order, what the outcome owes first (a commit's own `on_commit`
//!   or `on_abort` callbacks, then the database's hooks), then every
//!   `on_complete` callback, then marks the ticket ready and wakes the task
//!   awaiting it and every thread blocked on it.
//!
//! An `on_complete` registered while delivery is under way is refused by the
//! closed callback list and runs at once on the registering thread, so each
//! callback runs exactly once, at delivery or at registration. Nothing here
//! takes a lock.

use std::sync::{Arc, OnceLock, Weak};
use std::task::{Context, Poll};
use std::thread::{self, Thread};

use crate::engine::RegolithEngine;
use crate::engine::io::atomic_waker::AtomicWaker;
use crate::engine::io::job::Delivery;
use crate::engine::io::stack::{SHUT, Stack};
use crate::sync::internal::{AtomicUsize, Ordering};

const PENDING: usize = 0;
const DECIDED: usize = 1;
const DELIVERING: usize = 2;
const READY: usize = 3;

/// A callback that runs once with the outcome.
pub(crate) type Callback<T> = Box<dyn FnOnce(&T) + Send>;

/// What computes an outcome once the work it waits on has landed.
pub(crate) type Resolve<T> = Box<dyn FnOnce() -> T + Send>;

pub(crate) struct Completion<T> {
    outcome: OnceLock<T>,
    state: AtomicUsize,
    /// The task awaiting the ticket.
    waker: AtomicWaker,
    /// Computes the outcome at delivery, for a completion not decided when it
    /// was handed out. Taken whole, once, with [`SHUT`].
    resolve: Stack<Resolve<T>>,
    /// What the outcome owes before anything else: a commit's own callbacks
    /// and the database hooks. Closed with [`SHUT`] at delivery.
    first: Stack<Callback<T>>,
    /// The ticket's `on_complete` callbacks, closed with [`SHUT`] at delivery.
    on_complete: Stack<Callback<T>>,
    /// Threads blocked in [`Completion::wait_decided`], closed with [`SHUT`]
    /// once the outcome is decided.
    sleepers: Stack<Thread>,
    /// Told when an `on_complete` callback panics.
    report: Weak<RegolithEngine>,
    /// What a panic in an `on_complete` callback is reported as.
    name: &'static str,
}

impl<T: Send + Sync + 'static> Completion<T> {
    /// A pending completion whose `on_complete` panics are reported to
    /// `report` under `name`.
    pub(crate) fn new(report: Weak<RegolithEngine>, name: &'static str) -> Arc<Self> {
        Arc::new(Self {
            outcome: OnceLock::new(),
            state: AtomicUsize::new(PENDING),
            waker: AtomicWaker::new(),
            resolve: Stack::new(),
            first: Stack::new(),
            on_complete: Stack::new(),
            sleepers: Stack::new(),
            report,
            name,
        })
    }

    /// The database a callback's panic is reported to.
    pub(crate) fn report(&self) -> &Weak<RegolithEngine> {
        &self.report
    }

    /// Compute the outcome with `f` at delivery, unless it was decided by
    /// then. Set before the completion is handed out.
    pub(crate) fn resolve_with(&self, f: Resolve<T>) {
        // Refused only after delivery began, which the caller's order rules
        // out; nothing is left to resolve then.
        let _ = self.resolve.push(f, SHUT);
    }

    /// Owe `f` first at delivery, before any `on_complete` callback. Made
    /// before the completion is handed out.
    pub(crate) fn first(&self, f: Callback<T>) {
        // Refused only after delivery began, which the caller's order rules
        // out; run it then rather than drop it.
        if let Err(f) = self.first.push(f, SHUT)
            && let Some(outcome) = self.outcome.get()
        {
            f(outcome);
        }
    }

    /// Store the outcome. `false` (and `outcome` dropped) when one was
    /// already decided: the first decision stands.
    pub(crate) fn decide(&self, outcome: T) -> bool {
        if self.outcome.set(outcome).is_err() {
            return false;
        }
        let decided = self
            .state
            .compare_exchange(PENDING, DECIDED, Ordering::AcqRel, Ordering::Acquire)
            .is_ok();
        for sleeper in self.sleepers.take(SHUT) {
            sleeper.unpark();
        }
        decided
    }

    /// Whether an outcome has been decided.
    fn is_decided(&self) -> bool {
        self.state.load(Ordering::Acquire) != PENDING
    }

    /// Whether the ticket's holder may see the outcome: delivery finished.
    pub(crate) fn is_ready(&self) -> bool {
        self.state.load(Ordering::Acquire) == READY
    }

    /// Deliver the decided outcome on this thread: what it owes first, then
    /// each `on_complete` callback, then readiness and the wakes. Runs once;
    /// a call before the decision, or after another delivery began, does
    /// nothing.
    pub(crate) fn deliver_decided(&self) {
        if self
            .state
            .compare_exchange(DECIDED, DELIVERING, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            return;
        }
        let Some(outcome) = self.outcome.get() else {
            return;
        };
        for f in self.first.take(SHUT) {
            f(outcome);
        }
        let report = self.report.upgrade();
        for f in self.on_complete.take(SHUT) {
            crate::engine::callback::survive(report.as_deref(), self.name, || f(outcome));
        }
        self.state.store(READY, Ordering::Release);
        self.waker.wake();
    }

    /// Run `f` with the outcome once: at delivery, or now if delivery has
    /// begun or finished.
    pub(crate) fn on_complete(&self, f: Callback<T>) {
        if self.is_ready() {
            self.run_now(f);
        } else if let Err(f) = self.on_complete.push(f, SHUT) {
            // Delivery took the list after the check: it is under way or
            // done, and the outcome is decided.
            self.run_now(f);
        }
    }

    fn run_now(&self, f: Callback<T>) {
        if let Some(outcome) = self.outcome.get() {
            let report = self.report.upgrade();
            crate::engine::callback::survive(report.as_deref(), self.name, || f(outcome));
        }
    }

    /// The outcome when ready, else register `cx`'s waker to be woken at
    /// delivery.
    pub(crate) fn poll_ready(&self, cx: &mut Context<'_>) -> Poll<&T> {
        if !self.is_ready() {
            self.waker.register(cx.waker());
            // Delivery may have finished between the check and the
            // registration, and then woke no waker or an old one.
            if !self.is_ready() {
                return Poll::Pending;
            }
        }
        match self.outcome.get() {
            Some(outcome) => Poll::Ready(outcome),
            None => Poll::Pending,
        }
    }

    /// Block this thread until the outcome is decided, and return it. Its
    /// delivery (the callbacks, the ticket's readiness) still happens where
    /// it always does.
    pub(crate) fn wait_decided(&self) -> &T {
        loop {
            if let Some(outcome) = self.decided_outcome() {
                return outcome;
            }
            // Refused once the decision took the sleepers: decided now.
            if self.sleepers.push(thread::current(), SHUT).is_ok() {
                while !self.is_decided() {
                    thread::park();
                }
            }
        }
    }

    fn decided_outcome(&self) -> Option<&T> {
        if self.is_decided() {
            self.outcome.get()
        } else {
            None
        }
    }
}

impl<T: Send + Sync + 'static> Delivery for Completion<T> {
    /// Resolve the outcome if nobody decided it yet, then deliver it.
    fn deliver(&self) {
        if let Some(resolve) = self.resolve.take(SHUT).next() {
            self.decide(resolve());
        }
        self.deliver_decided();
    }
}

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicUsize;

    fn completion() -> Arc<Completion<u32>> {
        Completion::new(Weak::new(), "on_complete")
    }

    #[test]
    fn nothing_is_ready_before_delivery_and_everything_runs_once_at_it() {
        let done = completion();
        let order = Arc::new(std::sync::Mutex::new(Vec::new()));
        let seen = Arc::clone(&order);
        done.first(Box::new(move |v| seen.lock().unwrap().push(("first", *v))));
        let seen = Arc::clone(&order);
        done.on_complete(Box::new(move |v| {
            seen.lock().unwrap().push(("complete", *v))
        }));
        assert!(done.decide(7));
        assert!(!done.decide(8), "the first decision stands");
        assert!(!done.is_ready(), "decided is not delivered");
        done.deliver_decided();
        done.deliver_decided();
        assert!(done.is_ready());
        assert_eq!(*done.wait_decided(), 7);
        assert_eq!(*order.lock().unwrap(), vec![("first", 7), ("complete", 7)]);
        // Registered after delivery: runs at once, once.
        let runs = Arc::new(AtomicUsize::new(0));
        let counted = Arc::clone(&runs);
        done.on_complete(Box::new(move |_| {
            counted.fetch_add(1, Ordering::SeqCst);
        }));
        assert_eq!(runs.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn delivery_before_a_decision_does_nothing() {
        let done = completion();
        done.deliver_decided();
        assert!(!done.is_ready());
    }

    #[test]
    fn a_blocked_thread_wakes_at_the_decision() {
        let done = completion();
        std::thread::scope(|scope| {
            let waiting = Arc::clone(&done);
            let blocked = scope.spawn(move || *waiting.wait_decided());
            assert!(done.decide(3));
            assert_eq!(blocked.join().unwrap(), 3);
            assert!(!done.is_ready(), "decided is not delivered");
        });
    }

    #[test]
    fn a_panicking_on_complete_does_not_stop_the_others() {
        let done = completion();
        let runs = Arc::new(AtomicUsize::new(0));
        done.on_complete(Box::new(|_| panic!("callback panics")));
        let counted = Arc::clone(&runs);
        done.on_complete(Box::new(move |_| {
            counted.fetch_add(1, Ordering::SeqCst);
        }));
        done.decide(1);
        done.deliver_decided();
        assert!(done.is_ready());
        assert_eq!(runs.load(Ordering::SeqCst), 1);
    }
}
