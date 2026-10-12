//! Loom models of the lock-free commit pipeline (plan 4.7) and of the step
//! the version store's sections run in.
//!
//! ```text
//! RUSTFLAGS="--cfg loom" cargo test --release --test loom_pipeline
//! ```
//!
//! The models live in `src/engine/commit/loom_model.rs` and
//! `src/engine/loom_model/step.rs`, next to the crate-private types they
//! drive. What each proves:
//!
//! - **Reserve and void**: an owner installs the index it reserved while a
//!   helper voids it; exactly one wins, and the descriptor is dropped once.
//! - **A cell's next lap**: a slot is retired while the index one lap later
//!   is installed into its cell; the new descriptor is never taken for the
//!   old one.
//! - **The pin**: a descriptor, or the pipeline's state, loaded while it is
//!   retired or replaced is alive.
//! - **Decide with helping**: two threads decide the same two slots at
//!   once; each slot gets one decision and the sequences are dense.
//! - **The watermark claim**: two commits need the log durable; one claims
//!   the round and syncs, the other parks and is woken, and no two syncs
//!   overlap.
//! - **Publish**: two helpers publish one slot; whoever sees it published
//!   finds the read horizon at its sequence.
//! - **A rollback meeting a decision under way**: the decision computed
//!   from the discarded state never becomes the pipeline's state.
//! - **The version step**: two sections handed over at once never overlap,
//!   both run, and a caller parked on its section is woken.
//!
//! Every model is bounded by a small scenario (a ring of two cells, two
//! threads or two and a reader) and an explicit preemption bound given in
//! the model's own code, never by a time limit. Each is paired with a
//! calibration that writes one step the wrong way and must fail; without
//! them a search that never reached the bad interleaving would pass for the
//! same reason a broken one does.

#![cfg(loom)]

use regolith::loom_exports::{pipeline, step};

#[test]
fn an_index_is_installed_or_voided_never_both() {
    pipeline::an_index_is_installed_or_voided_never_both();
}

#[test]
#[should_panic(expected = "an index was installed and voided")]
fn a_void_that_is_not_a_compare_and_swap_gives_an_index_two_fates() {
    pipeline::a_void_that_is_not_a_compare_and_swap_gives_an_index_two_fates();
}

#[test]
fn a_cell_retired_while_it_takes_the_next_lap_keeps_the_new_descriptor() {
    pipeline::a_cell_retired_while_it_takes_the_next_lap_keeps_the_new_descriptor();
}

#[test]
#[should_panic(expected = "a cleaner took the descriptor of an install under way")]
fn a_cleaner_that_takes_an_install_under_way_empties_a_ready_cell() {
    pipeline::a_cleaner_that_takes_an_install_under_way_empties_a_ready_cell();
}

#[test]
fn a_descriptor_loaded_while_its_slot_is_retired_is_alive() {
    pipeline::a_descriptor_loaded_while_its_slot_is_retired_is_alive();
}

#[test]
#[should_panic(expected = "a loader read a descriptor that was already dropped")]
fn a_loader_that_does_not_pin_reads_a_dropped_descriptor() {
    pipeline::a_loader_that_does_not_pin_reads_a_dropped_descriptor();
}

#[test]
fn a_tip_loaded_while_it_is_replaced_is_alive() {
    pipeline::a_tip_loaded_while_it_is_replaced_is_alive();
}

#[test]
fn two_helpers_decide_two_slots_in_ring_order() {
    pipeline::two_helpers_decide_two_slots_in_ring_order();
}

#[test]
#[should_panic(expected = "two slots took overlapping sequences, or left a hole")]
fn a_frontier_passed_before_the_tip_moved_gives_two_slots_one_sequence() {
    pipeline::a_frontier_passed_before_the_tip_moved_gives_two_slots_one_sequence();
}

#[test]
fn a_round_is_claimed_by_one_commit_and_wakes_the_other() {
    pipeline::a_round_is_claimed_by_one_commit_and_wakes_the_other();
}

/// Loom reports the overlap itself: the two syncs write one tracked cell
/// with nothing ordering them.
#[test]
#[should_panic(expected = "Concurrent write accesses")]
fn a_claim_that_is_a_load_and_a_store_lets_two_syncs_overlap() {
    pipeline::a_claim_that_is_a_load_and_a_store_lets_two_syncs_overlap();
}

#[test]
fn a_published_slot_is_visible_to_whoever_sees_it_published() {
    pipeline::a_published_slot_is_visible_to_whoever_sees_it_published();
}

#[test]
#[should_panic(expected = "a slot was published before the horizon reached it")]
fn a_frontier_passed_before_the_horizon_hides_a_published_slot() {
    pipeline::a_frontier_passed_before_the_horizon_hides_a_published_slot();
}

#[test]
fn a_decision_computed_before_a_rollback_never_becomes_the_tip() {
    pipeline::a_decision_computed_before_a_rollback_never_becomes_the_tip();
}

#[test]
#[should_panic(expected = "a decision of the discarded state became the tip")]
fn a_settle_that_ignores_the_epoch_brings_a_discarded_state_back() {
    pipeline::a_settle_that_ignores_the_epoch_brings_a_discarded_state_back();
}

#[test]
fn sections_never_overlap_and_none_is_left_behind() {
    step::sections_never_overlap_and_none_is_left_behind();
}

#[test]
#[should_panic(expected = "a section was left on the list with nobody to run it")]
fn a_step_given_up_without_looking_leaves_a_section_behind() {
    step::a_step_given_up_without_looking_leaves_a_section_behind();
}
