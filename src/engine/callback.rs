//! Containing a panic in code the caller supplied while a commit runs it.
//!
//! A commit is the ordered step: the validation that precedes the write
//! pipeline and the group the pipeline's leader writes, which may rotate and
//! flush a memtable on the way. A panic that unwinds out of a caller's
//! implementation there leaves the shared state of that step half done, so
//! [`contain`] catches it, names the trait, and the step's boundary latches the
//! database read-only. Outside a commit nothing is caught: the panic unwinds
//! into the call that ran the code and fails only that call.
//!
//! Containment is a thread-local mode, [`InCommit`], because the flush that a
//! commit's rotation runs is the same code an explicit flush runs.

use std::cell::Cell;
use std::panic::{AssertUnwindSafe, catch_unwind};

use crate::Error;

thread_local! {
    static IN_COMMIT: Cell<bool> = const { Cell::new(false) };
}

/// The calling thread is inside a commit's ordered step until this drops.
pub(crate) struct InCommit {
    outer: bool,
}

impl InCommit {
    pub(crate) fn enter() -> Self {
        Self {
            outer: IN_COMMIT.replace(true),
        }
    }
}

impl Drop for InCommit {
    fn drop(&mut self) {
        IN_COMMIT.set(self.outer);
    }
}

/// Run `f`, a call into the caller's implementation of the trait `callback`.
///
/// Inside a commit a panic is caught and returned as
/// [`Error::CallbackPanicked`]; the caller of `contain` propagates it to the
/// step's boundary. Elsewhere `f` simply runs. Catching costs nothing when
/// nothing panics, and neither path allocates.
pub(crate) fn contain<T>(callback: &'static str, f: impl FnOnce() -> T) -> Result<T, Error> {
    if !IN_COMMIT.get() {
        return Ok(f());
    }
    catch_unwind(AssertUnwindSafe(f)).map_err(|_| {
        tracing::error!(callback, "a callback panicked while committing");
        // Every caller propagates it to the ordered step's boundary, which
        // latches the database.
        Error::CallbackPanicked {
            callback,
            latched: true,
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_panic_inside_a_commit_is_caught_and_named() {
        let _commit = InCommit::enter();
        let caught = contain("KeyClassifier", || -> u8 { panic!("boom") });
        assert!(matches!(
            caught,
            Err(Error::CallbackPanicked {
                callback: "KeyClassifier",
                latched: true
            })
        ));
        assert_eq!(contain("KeyClassifier", || 7).unwrap(), 7);
    }

    #[test]
    fn a_panic_outside_a_commit_unwinds() {
        let unwound = catch_unwind(|| contain("KeyClassifier", || -> u8 { panic!("boom") }));
        assert!(unwound.is_err());
    }

    #[test]
    fn the_mode_ends_with_the_guard_and_nests() {
        {
            let _outer = InCommit::enter();
            {
                let _inner = InCommit::enter();
            }
            assert!(contain("EventListener", || -> u8 { panic!("boom") }).is_err());
        }
        let unwound = catch_unwind(|| contain("EventListener", || -> u8 { panic!("boom") }));
        assert!(unwound.is_err(), "the mode outlived its guard");
    }
}
