//! Loom model checks for a memtable's range-tombstone log.
//!
//! The models live in `src/engine/loom_model/tombstones.rs`, next to the
//! crate-private log they drive; this target runs them:
//!
//! ```text
//! RUSTFLAGS="--cfg loom" cargo test --release --test loom_range_tombstones
//! ```
//!
//! Without `--cfg loom` the file compiles away. The calibration plants the
//! defect the log's prefix publication rules out and must fail.

#![cfg(loom)]

use regolith::loom_exports::tombstones;

#[test]
fn a_reader_sees_a_prefix_of_whole_appends() {
    tombstones::a_reader_sees_a_prefix_of_whole_appends();
}

#[test]
fn a_published_range_delete_is_seen_by_every_later_read() {
    tombstones::a_published_range_delete_is_seen_by_every_later_read();
}

#[test]
#[should_panic]
fn a_length_published_before_its_tombstone_is_caught() {
    tombstones::a_length_published_before_its_tombstone_is_caught();
}
