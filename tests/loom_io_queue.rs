//! Loom models of the per-thread I/O queues (plan 4.10, D53).
//!
//! ```text
//! RUSTFLAGS="--cfg loom" cargo test --release --test loom_io_queue
//! ```
//!
//! The models live in `src/engine/loom_model/io_queue.rs`, next to the
//! crate-private types they drive. What each proves:
//!
//! - **One claim, one run**: three threads race one unit's
//!   compare-and-swap; one wins, and the work runs once.
//! - **Exactly one completion per waiting queue**: registrations race the
//!   finish that closes the waiter list; a queue that registered gets one
//!   completion, one that was refused gets none and sees the outcome.
//! - **An idle owner is woken once, a busy one never**: a push races the
//!   owner going idle, and the owner waking up again.
//! - **No lost wakeup on a wait**: a task polls a read's wait, then again
//!   with a new waker, while the owner completes it; the waker it last gave
//!   is woken. A clone polled on another thread is woken through its own.
//!
//! Each is paired with a calibration that writes the one step the wrong way
//! and must fail; without them a search that never reached the bad
//! interleaving would pass for the same reason a broken one does.

#![cfg(loom)]

use regolith::loom_exports::io_queue;

#[test]
fn a_unit_is_claimed_once_and_runs_once() {
    io_queue::a_unit_is_claimed_once_and_runs_once();
}

#[test]
fn every_registered_queue_gets_one_completion() {
    io_queue::every_registered_queue_gets_one_completion();
}

#[test]
fn an_idle_owner_is_woken_once() {
    io_queue::an_idle_owner_is_woken_once();
}

#[test]
fn a_busy_owner_is_never_woken() {
    io_queue::a_busy_owner_is_never_woken();
}

#[test]
fn a_wait_is_never_lost() {
    io_queue::a_wait_is_never_lost();
}

#[test]
fn a_cloned_wait_is_woken_too() {
    io_queue::a_cloned_wait_is_woken_too();
}

#[test]
#[should_panic(expected = "the unit ran twice")]
fn calibration_a_claim_without_a_cas_runs_twice() {
    io_queue::calibration_a_claim_without_a_cas_runs_twice();
}

#[test]
#[should_panic(expected = "a registered queue got no completion")]
fn calibration_a_close_apart_from_the_take_loses_a_completion() {
    io_queue::calibration_a_close_apart_from_the_take_loses_a_completion();
}

#[test]
#[should_panic(expected = "an idle owner slept on a non-empty inbox")]
fn calibration_an_idle_mark_apart_from_the_inbox_loses_a_wakeup() {
    io_queue::calibration_an_idle_mark_apart_from_the_inbox_loses_a_wakeup();
}

#[test]
#[should_panic(expected = "a wait parked with nobody left to wake it")]
fn calibration_a_wait_without_a_second_look_hangs() {
    io_queue::calibration_a_wait_without_a_second_look_hangs();
}
