//! Loom model checks for the arena memtable and the engine's handoffs.
//!
//! The models themselves live in `src/engine/loom_model/`, next to the
//! code they drive, because everything they touch is crate-private. This
//! target is how they are run:
//!
//! ```text
//! RUSTFLAGS="--cfg loom" cargo test --release --test loom_memtable
//! ```
//!
//! Without `--cfg loom` the whole file compiles away, so an ordinary
//! `cargo test --workspace` neither builds loom nor runs these.
//!
//! Each positive model is paired with a calibration model that
//! deliberately gets the ordering wrong and must fail. A model checker
//! whose search never reaches the bad interleaving reports success for
//! the same reason a broken one does, so the calibrations are what make
//! the passes mean something. They are `#[should_panic]`, and the
//! expected message is the assertion the wrong ordering trips.
//!
//! One calibration only exists in a debug build: the skip list's
//! single-writer guard (invariant S2) is a `debug_assert`, so the model
//! that proves it fires on an unserialized insert is compiled out of a
//! release build. Both profiles run in CI for that reason.
//!
//! The arena's single-writer guard (invariant A8) is debug-only the same
//! way, but its calibration runs in both profiles: a debug build proves
//! the guard trips, a release build proves loom's tracked cell catches
//! the same unserialized race once the guard is compiled out, so the
//! expected panic message differs by profile on that one test.

#![cfg(loom)]

use regolith::loom_exports::{arena, handoff, skiplist, slice, version};

#[test]
fn insert_publishes_a_whole_node_to_a_concurrent_reader() {
    skiplist::insert_publishes_a_whole_node_to_a_concurrent_reader();
}

#[test]
fn a_seeded_key_stays_findable_while_a_writer_inserts_before_it() {
    skiplist::a_seeded_key_stays_findable_while_a_writer_inserts_before_it();
}

#[test]
#[should_panic(expected = "the two-step seek lost `c`")]
fn the_two_step_seek_loses_a_key_that_is_present() {
    skiplist::the_two_step_seek_loses_a_key_that_is_present();
}

#[test]
fn two_serialized_writers_and_a_reader_share_one_key() {
    skiplist::two_serialized_writers_and_a_reader_share_one_key();
}

#[test]
fn a_hinted_run_publishes_whole_nodes_to_a_concurrent_reader() {
    skiplist::a_hinted_run_publishes_whole_nodes_to_a_concurrent_reader();
}

/// The S2 guard is a `debug_assert`, so this calibration only exists in
/// a debug build. Run it with `RUSTFLAGS="--cfg loom" cargo test --test
/// loom_memtable`, without `--release`.
#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "insert is single-writer (S2)")]
fn an_unserialized_insert_trips_the_single_writer_guard() {
    skiplist::an_unserialized_insert_trips_the_single_writer_guard();
}

/// Invariant A8: two unserialized `Arena::alloc` calls must never both
/// touch the chunk list. A debug build's guard trips before either
/// thread reaches the state; a release build has no guard, so it is
/// loom's tracked cell that reports the concurrent write, which is the
/// calibration that proves the cell replacing the removed `Mutex` is
/// actually seen by the model.
#[cfg_attr(debug_assertions, should_panic(expected = "single-writer (A8)"))]
#[cfg_attr(
    not(debug_assertions),
    should_panic(expected = "Concurrent write accesses")
)]
#[test]
fn two_unserialized_allocations_race_the_arena() {
    arena::two_unserialized_allocations_race_the_arena();
}

#[test]
fn a_slice_outlives_every_memtable_handle() {
    slice::a_slice_outlives_every_memtable_handle();
}

#[test]
fn a_slice_survives_the_arena_growing_a_new_chunk() {
    slice::a_slice_survives_the_arena_growing_a_new_chunk();
}

#[test]
fn a_flush_never_hides_a_key() {
    handoff::a_flush_never_hides_a_key();
}

#[test]
#[should_panic(expected = "the key went missing")]
fn a_flush_that_retires_before_it_installs_hides_a_key() {
    handoff::a_flush_that_retires_before_it_installs_hides_a_key();
}

#[test]
fn the_read_horizon_never_outruns_the_memtable() {
    handoff::the_read_horizon_never_outruns_the_memtable();
}

#[test]
#[should_panic(expected = "a relaxed horizon advertised a sequence the reader cannot see")]
fn a_relaxed_read_horizon_outruns_the_memtable() {
    handoff::a_relaxed_read_horizon_outruns_the_memtable();
}

#[test]
fn a_reader_pins_one_version_across_a_compaction() {
    version::a_reader_pins_one_version_across_a_compaction();
}

#[test]
#[should_panic(expected = "the split apply hid `k`")]
fn a_split_compaction_apply_hides_a_key() {
    version::a_split_compaction_apply_hides_a_key();
}

#[test]
fn a_flush_and_a_compaction_cannot_lose_each_other() {
    version::a_flush_and_a_compaction_cannot_lose_each_other();
}

#[test]
#[should_panic(expected = "an unserialized version swap lost an edit")]
fn an_unserialized_version_swap_loses_an_edit() {
    version::an_unserialized_version_swap_loses_an_edit();
}
