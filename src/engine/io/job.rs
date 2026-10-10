//! One unit of I/O that is not a block read, run once however many queues
//! wait on it (D53).
//!
//! regolith hands every piece of I/O a non-blocking caller owes to the queue
//! of the thread that asked for it, as a job:
//!
//! - a commit group's fsync, which every member of the group waits on, and
//!   which the first member thread to poll runs (`engine::commit::deferred`);
//! - the bounded step of background work a write left owing with no worker,
//!   on the writing thread's queue (`engine::background_step`);
//! - the stall a stopped write waits out, which does no work of its own and
//!   lands when the stall clears (`engine::commit::stall`);
//! - a foreground job with no worker: `compact_range`, an ingest, a
//!   checkpoint (`engine::foreground`).
//!
//! A job is a [`Flight`]: claimed by one compare-and-swap and landed once,
//! pushing one `JobDone` to every queue that registered on it. A waiter with
//! no queue (a blocking call, a ticket whose caller has none) listens on the
//! job directly and is told by the thread that lands it, and a thread that
//! blocks on the job parks until then.
//!
//! A *passive* job has no body: no poll ever runs it, and only the event it
//! stands for lands it, through [`Job::release`]. That is the stall: its
//! readiness is the stall clearing, which a flush or a compaction makes
//! happen elsewhere.

#![allow(unsafe_code)]

use std::sync::Arc;
use std::thread::{self, Thread};

use super::flight::Flight;
use super::shared::{Message, QueueShared};
use super::stack::{SHUT, Stack};
use crate::sync::internal::UnsafeCell;

/// The work a job does.
pub(crate) trait JobBody: Send {
    /// Do the work, on the thread that claimed the job.
    fn run(self: Box<Self>);
    /// Settle the job without running it, when the database closes or the
    /// queue that would have run it is dropped. A job whose work cannot be
    /// left undone (a commit group's fsync) runs it here instead.
    fn release(self: Box<Self>);
}

/// Something a caller waits for, told on its owner's thread when the work
/// it waits on is done: a read's wait, a commit's ticket, a job's ticket.
pub(crate) trait Delivery: Send + Sync {
    /// Mark the wait ready, run what it owes on this thread, and wake the
    /// task awaiting it.
    fn deliver(&self);
}

pub(crate) struct Job {
    flight: Flight,
    /// Taken by the claim holder. `None` from the start for a passive job.
    body: UnsafeCell<Option<Box<dyn JobBody>>>,
    passive: bool,
    /// Waiters with no queue, told by the lander, closed with [`SHUT`].
    direct: Stack<Arc<dyn Delivery>>,
    /// Threads blocked until the job lands, closed with [`SHUT`].
    sleepers: Stack<Thread>,
}

// SAFETY: `body` is only touched by the one thread whose claim succeeded
// (`Flight::claim`), and a `JobBody` is `Send`. Everything else is atomic.
unsafe impl Sync for Job {}

impl Job {
    /// A job that runs `body` when a waiting queue's owner claims it.
    pub(crate) fn new(body: Box<dyn JobBody>) -> Arc<Self> {
        Arc::new(Self {
            flight: Flight::new(),
            body: UnsafeCell::new(Some(body)),
            passive: false,
            direct: Stack::new(),
            sleepers: Stack::new(),
        })
    }

    /// A job no poll runs, landed only by [`Job::release`].
    pub(crate) fn passive() -> Arc<Self> {
        Arc::new(Self {
            flight: Flight::new(),
            body: UnsafeCell::new(None),
            passive: true,
            direct: Stack::new(),
            sleepers: Stack::new(),
        })
    }

    pub(crate) fn is_done(&self) -> bool {
        self.flight.is_done()
    }

    /// No poll runs it; only the event it stands for lands it.
    pub(crate) fn is_passive(&self) -> bool {
        self.passive
    }

    /// A waiting queue's owner may claim and run it now.
    pub(crate) fn is_runnable(&self) -> bool {
        !self.passive && self.flight.is_free()
    }

    /// Take the job to run it, with one compare-and-swap. Never for a
    /// passive job. `true` for exactly one caller; it must then
    /// [`run`](Self::run) it.
    pub(crate) fn claim(&self) -> bool {
        !self.passive && self.flight.claim()
    }

    /// Record `queue` as waiting. `false` when the job already landed.
    pub(crate) fn register(&self, queue: Arc<QueueShared>) -> bool {
        self.flight.register(queue)
    }

    /// Tell `waiter` directly, on the landing thread, when the job lands.
    /// `false` when it already landed: the caller tells `waiter` itself.
    pub(crate) fn listen(&self, waiter: Arc<dyn Delivery>) -> bool {
        self.direct.push(waiter, SHUT).is_ok()
    }

    /// Run the body on this thread, after this caller's claim won, and land
    /// the job. A panic in the body still lands it, so no waiter is left on
    /// a claim nobody will complete; the panic then goes on unwinding.
    pub(crate) fn run(self: &Arc<Self>) {
        struct Unwind<'a>(Option<&'a Arc<Job>>);
        impl Drop for Unwind<'_> {
            fn drop(&mut self) {
                if let Some(job) = self.0.take() {
                    job.land();
                }
            }
        }
        let mut unwind = Unwind(Some(self));
        // SAFETY: the claim gave this thread the body.
        if let Some(body) = self.body.with_mut(|body| unsafe { (*body).take() }) {
            body.run();
        }
        unwind.0 = None;
        self.land();
    }

    /// Settle a job nobody is running without running it (its body says how)
    /// and land it. `false` when another thread had already claimed it; that
    /// thread lands it.
    pub(crate) fn release(self: &Arc<Self>) -> bool {
        if !self.flight.claim() {
            return false;
        }
        // SAFETY: the claim above gave this thread the body.
        if let Some(body) = self.body.with_mut(|body| unsafe { (*body).take() }) {
            body.release();
        }
        self.land();
        true
    }

    /// Block this thread until the job has landed.
    pub(crate) fn wait_landed(&self) {
        while !self.is_done() {
            // A refused push means the lander already took the sleepers: the
            // job is done.
            if self.sleepers.push(thread::current(), SHUT).is_err() {
                return;
            }
            // An unpark that raced ahead of this park is kept by the thread,
            // so the park returns at once.
            while !self.is_done() {
                thread::park();
            }
        }
    }

    /// Publish `Done` and tell everyone waiting: one `JobDone` per queue that
    /// registered, each direct waiter on this thread, and every blocked
    /// thread.
    fn land(self: &Arc<Self>) {
        for queue in self.flight.land() {
            // A queue dropped since it registered refuses the message; its
            // drop told its own waiters.
            let _ = queue.deliver(Message::JobDone(Arc::clone(self)));
        }
        for waiter in self.direct.take(SHUT) {
            waiter.deliver();
        }
        for sleeper in self.sleepers.take(SHUT) {
            sleeper.unpark();
        }
    }
}

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    struct Count(Arc<AtomicUsize>, Arc<AtomicUsize>);

    impl JobBody for Count {
        fn run(self: Box<Self>) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
        fn release(self: Box<Self>) {
            self.1.fetch_add(1, Ordering::SeqCst);
        }
    }

    struct Told(AtomicUsize);

    impl Delivery for Told {
        fn deliver(&self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }

    fn counted() -> (Arc<Job>, Arc<AtomicUsize>, Arc<AtomicUsize>) {
        let runs = Arc::new(AtomicUsize::new(0));
        let releases = Arc::new(AtomicUsize::new(0));
        let job = Job::new(Box::new(Count(Arc::clone(&runs), Arc::clone(&releases))));
        (job, runs, releases)
    }

    #[test]
    fn one_claim_runs_the_body_once_and_tells_every_direct_waiter() {
        let (job, runs, releases) = counted();
        let told = Arc::new(Told(AtomicUsize::new(0)));
        assert!(job.listen(Arc::clone(&told) as Arc<dyn Delivery>));
        assert!(job.claim());
        assert!(!job.claim(), "a claimed job is not claimed again");
        job.run();
        assert!(job.is_done());
        assert_eq!(runs.load(Ordering::SeqCst), 1);
        assert_eq!(releases.load(Ordering::SeqCst), 0);
        assert_eq!(told.0.load(Ordering::SeqCst), 1);
        assert!(
            !job.listen(told as Arc<dyn Delivery>),
            "a landed job refuses"
        );
        assert!(!job.release(), "a landed job is not released");
    }

    #[test]
    fn a_release_settles_a_free_job_without_running_it() {
        let (job, runs, releases) = counted();
        assert!(job.release());
        assert!(job.is_done());
        assert_eq!(runs.load(Ordering::SeqCst), 0);
        assert_eq!(releases.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn a_passive_job_is_never_runnable_and_lands_only_by_release() {
        let job = Job::passive();
        assert!(!job.is_runnable());
        assert!(!job.claim());
        assert!(!job.is_done());
        assert!(job.release());
        assert!(job.is_done());
    }

    #[test]
    fn a_blocked_thread_wakes_when_the_job_lands() {
        let (job, _, _) = counted();
        std::thread::scope(|scope| {
            let waiting = Arc::clone(&job);
            let blocked = scope.spawn(move || waiting.wait_landed());
            assert!(job.claim());
            job.run();
            blocked.join().unwrap();
        });
        // Landed already: returns at once.
        job.wait_landed();
    }

    #[test]
    fn a_panicking_body_still_lands_the_job() {
        struct Boom;
        impl JobBody for Boom {
            fn run(self: Box<Self>) {
                panic!("the body panics");
            }
            fn release(self: Box<Self>) {}
        }
        let job = Job::new(Box::new(Boom));
        assert!(job.claim());
        let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| job.run()));
        assert!(caught.is_err());
        assert!(job.is_done());
    }
}
