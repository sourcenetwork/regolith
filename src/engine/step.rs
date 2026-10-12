//! A step: work that runs one section at a time, on whichever thread holds
//! the step, in place of a mutex (plan 4.6, 4.7).
//!
//! A caller hands [`Step::run`] a *section*, a closure. Sections never
//! overlap and run in the order they were handed over, as critical sections
//! of one mutex would. What differs is who runs them and what a caller
//! waits for:
//!
//! - **The step is taken, not waited for.** A section is pushed on a
//!   lock-free list. The push that finds nobody holding the step takes it,
//!   with the same compare-and-swap that pushed, and runs every section
//!   queued, its own and other threads', oldest first, until the list is
//!   empty. So a section never waits for its own thread to be scheduled:
//!   whichever thread holds the step runs it.
//! - **A caller waits only for the work under way.** A caller whose push
//!   found the step held parks until its section has run, on the thread
//!   that holds the step, which is doing the sections queued before it.
//!
//! # Invariants
//!
//! - **ST1, one thread runs sections**, one section at a time: the thread
//!   that holds the step.
//! - **ST2, the step is held exactly while a thread runs sections.** The
//!   list's head word carries `IDLE` when it is empty and nobody holds the
//!   step. The push that clears `IDLE` holds the step from then on; the
//!   holder gives it up with one compare-and-swap that succeeds only on an
//!   empty list. So a section pushed at any moment is either taken by the
//!   holder's next sweep or is the push that takes the step: none is left
//!   behind with nobody to run it.
//! - **ST3, sections run in the order they were pushed**, each to its end
//!   before the next begins.
//! - **ST4, a section has finished before its caller returns.** The caller
//!   parks until its section's own job lands, which the running thread does
//!   after the section returned or unwound. That is what lets a section
//!   borrow from its caller's stack though another thread may run it.
//! - **ST5, a panic in a section is its caller's.** It is caught on the
//!   thread that ran the section and resumed on the thread that asked for
//!   it, so one caller's panic never unwinds the thread serving the rest.

#![allow(unsafe_code)]

use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::sync::Arc;

use super::io::job::Job;
use super::io::stack::{IDLE, Rest, Stack};
use super::take::Take;

/// One section waiting for the step.
struct Request {
    /// Runs the section and keeps what it returned. Taken by the thread
    /// that runs it.
    body: Option<Box<dyn FnOnce() + Send>>,
    /// Landed once the section has run: what its caller parks on (ST4).
    done: Arc<Job>,
}

impl Drop for Request {
    fn drop(&mut self) {
        // ST4: after the body ran, or with a list dropped unrun.
        self.done.release();
    }
}

/// See the module docs.
pub(crate) struct Step {
    /// The sections waiting for the step, and whether it is held (ST2).
    waiting: Stack<Request>,
}

impl Step {
    pub(crate) fn new() -> Self {
        let waiting = Stack::new();
        // Nobody holds the step.
        let rested = waiting.rest_if_empty();
        debug_assert_eq!(rested, Rest::Set);
        Self { waiting }
    }

    /// Run `section` alone and after every section pushed before it, and
    /// return what it returns.
    ///
    /// The section may run on another thread, the one that holds the step,
    /// which is why it is `Send`. It has finished when this returns (ST4).
    pub(crate) fn run<T: Send>(&self, section: impl FnOnce() -> T + Send) -> T {
        let out: Take<std::thread::Result<T>> = Take::empty();
        let done = Job::passive();
        {
            let out = &out;
            let body: Box<dyn FnOnce() + Send + '_> = Box::new(move || {
                // ST5: the panic is this section's caller's.
                out.put(catch_unwind(AssertUnwindSafe(section)));
            });
            // SAFETY (ST4): the lifetime of what `section` and `out` borrow
            // is erased so the body can wait on the list. This call does
            // not return before `done` has landed, and the thread that
            // lands it has by then run the body to its end, or dropped it
            // with the list. So the body never outlives its borrows.
            let body: Box<dyn FnOnce() + Send> = unsafe { std::mem::transmute(body) };
            let request = Request {
                body: Some(body),
                done: Arc::clone(&done),
            };
            // No flag refuses a push here, so `Err` cannot come back.
            if let Ok(flags) = self.waiting.push(request, 0)
                && flags & IDLE != 0
            {
                // ST2: this push took the step.
                self.sweep();
            }
        }
        done.wait_landed();
        match out.take() {
            Some(Ok(value)) => value,
            Some(Err(panic)) => resume_unwind(panic),
            None => unreachable!("a section's job landed before the section ran"),
        }
    }

    /// Run every queued section, as the thread that holds the step, and
    /// give the step up once the list is empty (ST2, ST3).
    fn sweep(&self) {
        loop {
            for mut request in self.waiting.take(0) {
                if let Some(body) = request.body.take() {
                    body();
                }
                // Dropped here: its caller goes on.
            }
            if self.waiting.rest_if_empty() != Rest::Busy {
                return;
            }
        }
    }

    /// Test-only: whether a section is waiting on the list.
    #[cfg(test)]
    pub(crate) fn has_waiting(&self) -> bool {
        !self.waiting.is_empty()
    }
}
