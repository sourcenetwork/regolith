//! Tests of the append-only tombstone log: prefix publication under a
//! racing writer, the index against a linear model across rebuilds, and the
//! listing order the memtable has always answered in.

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64};

use proptest::prelude::*;

use super::*;

fn tomb(start: &[u8], end: &[u8], seq: u64) -> RangeTombstone {
    RangeTombstone::new(start.to_vec(), end.to_vec(), seq)
}

/// The answer a linear walk over every tombstone gives.
fn model_covering(all: &[(Vec<u8>, Vec<u8>, u64)], key: &[u8], snapshot: u64) -> u64 {
    all.iter()
        .filter(|(s, e, q)| s.as_slice() <= key && key < e.as_slice() && *q <= snapshot)
        .map(|(_, _, q)| *q)
        .max()
        .unwrap_or(0)
}

#[test]
fn segments_cover_every_position_without_a_gap() {
    let mut expected = 0usize;
    for position in 0..100_000usize {
        let (segment, offset) = locate(position);
        assert!(offset < segment_len(segment), "position {position}");
        if offset == 0 && position != 0 {
            expected += 1;
        }
        assert_eq!(segment, expected, "position {position}");
    }
    assert!(locate(u32::MAX as usize).0 < SEGMENTS);
}

#[test]
fn an_empty_log_answers_nothing_and_holds_nothing() {
    let log = TombstoneLog::new();
    assert_eq!(log.len(), 0);
    assert_eq!(log.bytes(), 0);
    assert_eq!(log.covering_seq(b"k", u64::MAX), 0);
    assert!(log.first_newer_overlap(b"a", b"z", 0).is_none());
    assert!(log.to_sorted_vec().is_empty());
}

#[test]
fn a_rebuild_keeps_every_answer_the_tail_gave() {
    let log = TombstoneLog::new();
    let mut all = Vec::new();
    for i in 0..(REBUILD as u64 * 3 + 5) {
        let start = format!("k{:03}", (i * 7) % 50).into_bytes();
        let end = format!("k{:03}", (i * 7) % 50 + 1 + i % 9).into_bytes();
        log.push(tomb(&start, &end, i + 1));
        all.push((start, end, i + 1));
        for probe in 0..60u64 {
            let key = format!("k{probe:03}").into_bytes();
            for snapshot in [0, i / 2 + 1, u64::MAX] {
                assert_eq!(
                    log.covering_seq(&key, snapshot),
                    model_covering(&all, &key, snapshot),
                    "after {} appends, key {probe}, snapshot {snapshot}",
                    i + 1
                );
            }
        }
    }
    assert!(log.index.load().is_some(), "setup: an index was built");
}

#[test]
fn the_listing_is_sorted_and_deduplicated_as_before() {
    let log = TombstoneLog::new();
    for t in [
        tomb(b"m", b"p", 3),
        tomb(b"a", b"c", 1),
        tomb(b"a", b"c", 1),
        tomb(b"a", b"c", 2),
        tomb(b"a", b"b", 4),
    ] {
        log.push(t);
    }
    let listed: Vec<_> = log
        .to_sorted_vec()
        .into_iter()
        .map(|t| (t.start, t.end, t.seq))
        .collect();
    assert_eq!(
        listed,
        vec![
            (b"a".to_vec(), b"b".to_vec(), 4),
            (b"a".to_vec(), b"c".to_vec(), 2),
            (b"a".to_vec(), b"c".to_vec(), 1),
            (b"m".to_vec(), b"p".to_vec(), 3),
        ]
    );
}

/// The reader's half of T2, under a writer that never stops: every length
/// a reader acquires names whole tombstones, in append order, and a later
/// read never sees fewer.
#[test]
fn readers_see_a_growing_prefix_of_whole_appends_while_a_writer_appends() {
    const APPENDS: u64 = 4_000;
    let log = Arc::new(TombstoneLog::new());
    let done = Arc::new(AtomicBool::new(false));
    let checked = Arc::new(AtomicU64::new(0));
    std::thread::scope(|scope| {
        for _ in 0..4 {
            let (log, done, checked) = (Arc::clone(&log), Arc::clone(&done), Arc::clone(&checked));
            scope.spawn(move || {
                let mut last = 0usize;
                while !done.load(std::sync::atomic::Ordering::Acquire) || last < APPENDS as usize {
                    let len = log.len();
                    assert!(len >= last, "the prefix shrank from {last} to {len}");
                    for position in last..len {
                        let t = log.get(position);
                        let seq = position as u64 + 1;
                        assert_eq!(t.seq, seq, "append {position} out of order");
                        assert_eq!(t.start, format!("s{seq:06}").into_bytes(), "torn append");
                        assert_eq!(t.end, format!("t{seq:06}").into_bytes(), "torn append");
                    }
                    // Every published tombstone covers its own start, and a
                    // lookup never answers a sequence past the prefix.
                    if len > 0 {
                        let key = format!("s{len:06}").into_bytes();
                        let seen = log.covering_seq(&key, u64::MAX);
                        assert!(seen >= len as u64, "a published tombstone was missed");
                    }
                    checked.fetch_add((len - last) as u64, std::sync::atomic::Ordering::Relaxed);
                    last = len;
                }
            });
        }
        for seq in 1..=APPENDS {
            log.push(tomb(
                format!("s{seq:06}").as_bytes(),
                format!("t{seq:06}").as_bytes(),
                seq,
            ));
        }
        done.store(true, std::sync::atomic::Ordering::Release);
    });
    assert_eq!(
        checked.load(std::sync::atomic::Ordering::Relaxed),
        4 * APPENDS,
        "every reader checked every append"
    );
}

/// T1's detector: a second writer inside an append trips the debug guard.
#[test]
#[cfg(debug_assertions)]
fn a_second_concurrent_writer_trips_the_single_writer_guard() {
    let log = TombstoneLog::new();
    let _held = SingleWriterGuard::enter(&log.writing, "held by the test");
    let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        log.push(tomb(b"a", b"b", 1));
    }));
    assert!(caught.is_err(), "the guard did not catch a second writer");
}

fn key() -> impl Strategy<Value = Vec<u8>> {
    proptest::collection::vec(0u8..6, 0..3)
}

proptest! {
    /// Every query the memtable makes of its tombstones, against a linear
    /// model over the same appends, across rebuilds of the index.
    #[test]
    fn every_query_matches_a_linear_model(
        appends in proptest::collection::vec((key(), key(), 1u64..60), 0..80),
        probes in proptest::collection::vec((key(), key(), 0u64..70), 1..24),
    ) {
        let log = TombstoneLog::new();
        let mut all = Vec::new();
        for (start, end, seq) in &appends {
            if start < end {
                log.push(tomb(start, end, *seq));
                all.push((start.clone(), end.clone(), *seq));
            }
        }
        prop_assert_eq!(log.len(), all.len());
        let mut sorted: Vec<RangeTombstone> =
            all.iter().map(|(s, e, q)| tomb(s, e, *q)).collect();
        sort_dedup_tombstones(&mut sorted);
        let listed = log.to_sorted_vec();
        prop_assert_eq!(
            listed.iter().map(|t| (&t.start, &t.end, t.seq)).collect::<Vec<_>>(),
            sorted.iter().map(|t| (&t.start, &t.end, t.seq)).collect::<Vec<_>>()
        );
        for (a, b, n) in &probes {
            prop_assert_eq!(log.covering_seq(a, *n), model_covering(&all, a, *n));
            let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
            let expected = sorted.iter().find(|t| t.seq > *n && t.overlaps(lo, hi));
            let got = log.first_newer_overlap(lo, hi, *n);
            prop_assert_eq!(
                got.map(|t| (&t.start, &t.end, t.seq)),
                expected.map(|t| (&t.start, &t.end, t.seq))
            );
        }
    }
}
