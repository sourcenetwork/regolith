//! Loom models for the column-family registry (plan 4.6, Phase 7c1).
//!
//! ```text
//! RUSTFLAGS="--cfg loom" cargo test --release --test loom_tables
//! ```
//!
//! The models live in `src/engine/loom_model/families.rs` and are a
//! protocol model of the ordered step: a write racing a drop either lands
//! below the drop's tombstone or is refused, and a family moves unborn,
//! live, dead and never back.
//!
//! Each is paired with a calibration that writes the one step the wrong way
//! and must fail.

#![cfg(loom)]

use regolith::loom_exports::families;

#[test]
fn a_write_racing_a_drop_is_deleted_or_refused() {
    families::a_write_racing_a_drop_is_deleted_or_refused();
}

#[test]
fn a_family_lives_once_in_order() {
    families::a_family_lives_once_in_order();
}

#[test]
#[should_panic(expected = "a write landed after the drop's tombstone")]
fn calibration_a_fence_outside_the_ordered_step_lands_after_the_drop() {
    families::calibration_a_fence_outside_the_ordered_step_lands_after_the_drop();
}
