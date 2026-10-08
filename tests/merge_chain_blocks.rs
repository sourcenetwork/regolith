//! A merge chain longer than one SSTable data block reads back whole.
//!
//! A point read collects a key's merge operands newest first down to its
//! base. Within one SSTable the chain used to stop at the end of the first
//! data block it landed in, and the read moved on to the next older file:
//! every operand in the rest of the file, and the base beneath them, was
//! skipped, and a later compaction could write the short sum back as the
//! key's value. A pinned snapshot makes such chains routine, since it keeps
//! compaction from folding operands, so every transaction's snapshot could
//! trigger it.

// Native-only. wasm-pack builds every test target for wasm32, and these use
// the filesystem. The browser suite lives in tests/wasm_opfs*.rs.
#![cfg(not(target_arch = "wasm32"))]

use std::sync::Arc;

use regolith::{Db, MergeOperator, Options};

/// Operands per chain: enough to span many 512-byte blocks.
const OPERANDS: i64 = 2_000;

/// Sums big-endian i64 deltas.
struct CounterMerge;

impl MergeOperator for CounterMerge {
    fn name(&self) -> &'static str {
        "counter"
    }

    fn full_merge(&self, _key: &[u8], base: Option<&[u8]>, operands: &[&[u8]]) -> Option<Vec<u8>> {
        let mut total: i64 = match base {
            Some(bytes) if bytes.len() == 8 => i64::from_be_bytes(bytes.try_into().unwrap()),
            Some(_) => return None,
            None => 0,
        };
        for operand in operands {
            if operand.len() != 8 {
                return None;
            }
            total = total.wrapping_add(i64::from_be_bytes((*operand).try_into().unwrap()));
        }
        Some(total.to_be_bytes().to_vec())
    }
}

fn options() -> Options {
    Options {
        merge_operator: Some(Arc::new(CounterMerge)),
        block_size: 512,
        write_buffer_size: 4 * 1024 * 1024,
        max_background_compactions: 0,
        ..Options::default()
    }
}

fn partitioned() -> Options {
    Options {
        partitioned_index: true,
        metadata_block_size: 512,
        ..options()
    }
}

fn counter(db: &Db) -> i64 {
    i64::from_be_bytes(db.get(b"counter").unwrap().unwrap()[..].try_into().unwrap())
}

fn sst_bytes(db: &Db) -> u64 {
    db.get_int_property("regolith.total-sst-files-size")
        .unwrap()
}

fn merge_operands(db: &Db) {
    db.put(b"counter", &100i64.to_be_bytes()).unwrap();
    for _ in 0..OPERANDS {
        db.merge(b"counter", &1i64.to_be_bytes()).unwrap();
    }
    // A neighbour after the chain, so the block after it is not the end
    // of the file.
    db.put(b"counter~", b"after").unwrap();
}

#[test]
fn a_flushed_chain_spanning_blocks_reads_whole() {
    for opts in [options(), partitioned()] {
        let dir = tempfile::tempdir().unwrap();
        let db = Db::open(dir.path(), opts).unwrap();
        merge_operands(&db);
        db.flush().unwrap();
        assert_eq!(counter(&db), 100 + OPERANDS);
    }
}

#[test]
fn a_chain_a_snapshot_kept_unfolded_reads_whole_and_compacts_whole() {
    for opts in [options(), partitioned()] {
        let dir = tempfile::tempdir().unwrap();
        let db = Db::open(dir.path(), opts).unwrap();
        let snapshot = db.snapshot();
        merge_operands(&db);
        db.flush().unwrap();
        db.compact_range(None, None).unwrap();
        assert_eq!(counter(&db), 100 + OPERANDS, "while the snapshot is held");

        // Folding the chain once the snapshot is gone must fold all of it.
        // A compaction only rewrites the chain when a newer file overlaps
        // it, so one more operand gives the fold an input.
        drop(snapshot);
        let unfolded = sst_bytes(&db);
        db.merge(b"counter", &1i64.to_be_bytes()).unwrap();
        db.flush().unwrap();
        db.compact_range(None, None).unwrap();
        assert!(
            sst_bytes(&db) < unfolded / 4,
            "the chain was folded: {} bytes from {unfolded}",
            sst_bytes(&db)
        );
        assert_eq!(counter(&db), 100 + OPERANDS + 1, "after the fold");
    }
}
