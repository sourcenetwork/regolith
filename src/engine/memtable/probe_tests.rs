//! Tests for the range-tombstone lock-free gate and the sequence-only
//! probe `MemTable::latest_seq` shares with `MemTable::get`.

use super::*;
use proptest::prelude::*;
use std::sync::mpsc::{RecvTimeoutError, channel};
use std::time::Duration;

fn memtable() -> MemTable {
    MemTable::new(&MemTableConfig::default()).expect("memtable")
}

fn probe(key: &[u8], snapshot_seq: u64) -> LookupKey {
    LookupKey::from_prefixed(key, snapshot_seq)
}

#[test]
fn covering_seq_is_zero_before_any_range_delete_and_found_after_one() {
    let mt = memtable();
    assert_eq!(mt.covering_range_tombstone_seq(b"c", 10), 0);
    mt.delete_range(b"b", b"d", 5);
    assert_eq!(mt.covering_range_tombstone_seq(b"c", 10), 5);
    assert_eq!(mt.covering_range_tombstone_seq(b"a", 10), 0);
    assert_eq!(
        mt.covering_range_tombstone_seq(b"d", 10),
        0,
        "end is exclusive"
    );
    assert_eq!(
        mt.covering_range_tombstone_seq(b"c", 4),
        0,
        "invisible to a snapshot older than the tombstone"
    );
}

#[test]
fn a_lookup_on_a_tombstone_free_memtable_takes_no_lock() {
    let mt = memtable();
    let guard = mt.range_tombstones.lock();
    let (tx, rx) = channel();
    std::thread::scope(|scope| {
        scope.spawn(|| {
            let result = mt.covering_range_tombstone_seq(b"k", u64::MAX);
            let _ = tx.send(result);
        });
        match rx.recv_timeout(Duration::from_secs(10)) {
            Ok(result) => assert_eq!(result, 0),
            Err(RecvTimeoutError::Timeout) => {
                // Drop the guard so the spawned thread can finish before the
                // scope tries to join it, then fail with the real cause.
                drop(guard);
                panic!("lookup took the tombstone lock on a memtable with no tombstones");
            }
            Err(RecvTimeoutError::Disconnected) => {
                drop(guard);
                panic!("lookup thread ended without sending a result");
            }
        }
    });
}

#[test]
fn a_lookup_takes_the_lock_once_a_tombstone_exists() {
    let mt = memtable();
    mt.delete_range(b"a", b"z", 1);
    let guard = mt.range_tombstones.lock();
    let (tx, rx) = channel();
    std::thread::scope(|scope| {
        scope.spawn(|| {
            let result = mt.covering_range_tombstone_seq(b"k", u64::MAX);
            let _ = tx.send(result);
        });
        assert_eq!(
            rx.recv_timeout(Duration::from_millis(200)),
            Err(RecvTimeoutError::Timeout),
            "a lookup on a memtable holding a tombstone must take the lock"
        );
        drop(guard);
        assert_eq!(rx.recv().expect("lookup completes once unblocked"), 1);
    });
}

#[test]
fn latest_seq_agrees_with_get() {
    let mt = memtable();
    mt.put(b"k", b"v1", 1);
    mt.put(b"k", b"v2", 2);
    mt.delete(b"k", 3);
    mt.merge(b"k", b"op", 4);
    for snapshot_seq in 0..=5u64 {
        let lk = probe(b"k", snapshot_seq);
        assert_eq!(mt.latest_seq(&lk), mt.get(&lk).map(|(seq, _)| seq));
    }
    assert_eq!(mt.latest_seq(&probe(b"k", 0)), None);
}

fn key_strategy() -> impl Strategy<Value = Vec<u8>> {
    proptest::collection::vec(0u8..4, 0..3)
}

proptest! {
    /// About a third of cases push zero tombstones, exercising the
    /// lock-free gate on an empty set; the rest exercise the locked path.
    #[test]
    fn sequence_probe_and_tombstone_gate_match_a_linear_model(
        entries in proptest::collection::vec((key_strategy(), 1u64..40, 0u8..3), 0..48),
        tombstones in proptest::collection::vec((key_strategy(), key_strategy(), 1u64..40), 0..3),
        probes in proptest::collection::vec((key_strategy(), 0u64..45), 1..16),
    ) {
        let mt = memtable();
        let mut model: Vec<(Vec<u8>, u64, u8)> = Vec::new();
        for (key, seq, kind) in &entries {
            match kind {
                0 => mt.put(key, b"v", *seq),
                1 => mt.delete(key, *seq),
                _ => mt.merge(key, b"op", *seq),
            }
            model.push((key.clone(), *seq, *kind));
        }
        // The skip list keeps duplicate (key, seq) entries; `seek_ge`
        // returns the first in list order and the model takes the max
        // seq, which is the same value, so duplicates need no special
        // casing here.
        let mut pushed_tombstones: Vec<(Vec<u8>, Vec<u8>, u64)> = Vec::new();
        for (start, end, seq) in &tombstones {
            if start < end {
                mt.delete_range(start, end, *seq);
                pushed_tombstones.push((start.clone(), end.clone(), *seq));
            }
        }

        for (key, snapshot_seq) in &probes {
            let expected_latest = model
                .iter()
                .filter(|(k, seq, _)| k == key && *seq <= *snapshot_seq)
                .map(|(_, seq, _)| *seq)
                .max();
            let expected_covering = pushed_tombstones
                .iter()
                .filter(|(start, end, seq)| {
                    start.as_slice() <= key.as_slice()
                        && key.as_slice() < end.as_slice()
                        && *seq <= *snapshot_seq
                })
                .map(|(_, _, seq)| *seq)
                .max()
                .unwrap_or(0);

            let lk = probe(key, *snapshot_seq);
            prop_assert_eq!(mt.latest_seq(&lk), expected_latest);
            prop_assert_eq!(mt.get(&lk).map(|(seq, _)| seq), expected_latest);
            prop_assert_eq!(mt.covering_range_tombstone_seq(key, *snapshot_seq), expected_covering);
        }
    }
}
