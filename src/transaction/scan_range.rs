//! What a transactional scan records about the keys it walked.
//!
//! A scan does not add a read-set cell per key it yields: that would hold
//! memory and cost commit work per key. It records each unbroken stretch
//! of snapshot keys it yields as one [`ScanRun`], the first and the last
//! key of the stretch, CF-prefixed and inclusive. A stretch ends where the
//! walk passes an entry of the transaction's own write buffer, or a key
//! the transaction already reads past its begin snapshot, since neither
//! was read from the snapshot.
//!
//! Invariant: every key inside a closed run was observed at the begin
//! snapshot, as a value the scan yielded or as an absence the walk passed
//! over. A run whose stream was neither exhausted nor dropped has no last
//! key and reaches the end of the keyspace in the direction it walked, so
//! it still covers at least what was walked.
//!
//! At commit the runs are merged into disjoint intervals (sorted by lower
//! bound, overlapping or touching ones coalesced), and every key the commit
//! validates that lies inside one is validated as a read made no later than
//! the begin snapshot.

use std::collections::BTreeMap;
use std::sync::{Arc, OnceLock};

use crate::engine::ConflictKey;

/// One stretch of snapshot keys a scan yielded, recorded once however many
/// keys it holds.
pub(super) struct ScanRun {
    /// The first key the stretch yielded, CF-prefixed: its lowest key
    /// walking forward, its highest walking in reverse.
    first: Vec<u8>,
    /// The last key it yielded, set once when the stretch closes. Unset
    /// means the stream was never closed, so the stretch is taken to reach
    /// the end of the keyspace in the direction it walked.
    last: OnceLock<Vec<u8>>,
    reverse: bool,
}

/// The stretch a stream is extending. Dropping it closes the stretch at the
/// last key it was extended to.
///
/// It holds no borrow of the transaction, so closing a stretch never
/// touches the transaction: the record was registered when the stretch
/// began, and a stream dropped after its transaction resolved reaches only
/// this `Arc`.
pub(super) struct OpenRun {
    run: Arc<ScanRun>,
    last: Vec<u8>,
}

impl OpenRun {
    /// Begin a stretch at `key` (CF-prefixed). Returns the record for the
    /// transaction to register and the handle that extends and closes it.
    pub(super) fn start(key: &[u8], reverse: bool) -> (Arc<ScanRun>, Self) {
        let run = Arc::new(ScanRun {
            first: key.to_vec(),
            last: OnceLock::new(),
            reverse,
        });
        (
            Arc::clone(&run),
            Self {
                run,
                last: key.to_vec(),
            },
        )
    }

    /// Extend the stretch to `key` (CF-prefixed), the next key in its
    /// direction.
    pub(super) fn extend(&mut self, key: &[u8]) {
        self.last.clear();
        self.last.extend_from_slice(key);
    }
}

impl Drop for OpenRun {
    fn drop(&mut self) {
        // `OpenRun` is the only writer of `last` and is dropped once, so
        // the cell is always empty here.
        self.run.last.get_or_init(|| std::mem::take(&mut self.last));
    }
}

/// A closed key interval; `None` leaves that side unbounded.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Walked<'a> {
    lo: Option<&'a [u8]>,
    hi: Option<&'a [u8]>,
}

/// The runs as disjoint intervals sorted by lower bound.
fn walked(runs: &[Arc<ScanRun>]) -> Vec<Walked<'_>> {
    let mut spans: Vec<Walked<'_>> = runs
        .iter()
        .map(|run| {
            let last = run.last.get().map(Vec::as_slice);
            let first = Some(run.first.as_slice());
            if run.reverse {
                Walked {
                    lo: last,
                    hi: first,
                }
            } else {
                Walked {
                    lo: first,
                    hi: last,
                }
            }
        })
        .collect();
    // `None < Some`, so a span unbounded below sorts first.
    spans.sort_unstable_by(|a, b| a.lo.cmp(&b.lo));
    let mut merged: Vec<Walked<'_>> = Vec::with_capacity(spans.len());
    for span in spans {
        match merged.last_mut() {
            Some(prev) if reaches(prev.hi, span.lo) => {
                prev.hi = match (prev.hi, span.hi) {
                    (Some(a), Some(b)) => Some(a.max(b)),
                    _ => None,
                };
            }
            _ => merged.push(span),
        }
    }
    merged
}

/// Whether an interval ending at `hi` overlaps or touches one starting at
/// `lo` that sorts at or after it.
fn reaches(hi: Option<&[u8]>, lo: Option<&[u8]>) -> bool {
    match (hi, lo) {
        (Some(hi), Some(lo)) => lo <= hi,
        _ => true,
    }
}

/// Whether `key` lies inside one of `walked`, which [`walked`] built.
fn covers(walked: &[Walked<'_>], key: &[u8]) -> bool {
    let after = walked.partition_point(|span| span.lo.is_none_or(|lo| lo <= key));
    after > 0 && walked[after - 1].hi.is_none_or(|hi| key <= hi)
}

/// Anchor every key in `reads` a scan walked no later than `begin_seq`, and
/// append every written or merged key a scan walked that `reads` does not
/// already hold, as a read at `begin_seq`.
///
/// This is what [`crate::Transaction::get`] at the begin snapshot followed
/// by the write would have left: a read that is never elided as an
/// idempotent write, anchored at the earliest sequence the key was
/// observed at. `reads` must be sorted by key with no duplicates on entry,
/// and is again on return. A no-op when `runs` is empty, so a transaction
/// that ran no scan pays nothing here.
pub(super) fn cover(
    reads: &mut Vec<ConflictKey>,
    runs: &[Arc<ScanRun>],
    writes: &BTreeMap<Vec<u8>, Option<Vec<u8>>>,
    merges: &[(Vec<u8>, Vec<u8>)],
    begin_seq: u64,
) {
    if runs.is_empty() {
        return;
    }
    let walked = walked(runs);
    for read in reads.iter_mut() {
        if covers(&walked, &read.key) {
            read.observed_seq = read.observed_seq.min(begin_seq);
        }
    }
    let mut added: Vec<ConflictKey> = writes
        .keys()
        .chain(merges.iter().map(|(key, _)| key))
        .filter(|key| {
            covers(&walked, key)
                && reads
                    .binary_search_by(|read| read.key.as_slice().cmp(key))
                    .is_err()
        })
        .map(|key| ConflictKey {
            key: key.clone(),
            observed_seq: begin_seq,
        })
        .collect();
    if added.is_empty() {
        return;
    }
    added.sort_unstable_by(|a, b| a.key.cmp(&b.key));
    added.dedup_by(|later, first| later.key == first.key);
    reads.append(&mut added);
    // Two sorted runs back to back: the stable sort merges them in one pass.
    reads.sort_by(|a, b| a.key.cmp(&b.key));
}

#[cfg(test)]
mod tests {
    use super::super::*;
    use super::*;
    use proptest::prelude::*;
    use tempfile::TempDir;

    /// A run as `(first, last, reverse)` with the CF prefix stripped.
    type Span<'a> = (&'a [u8], Option<&'a [u8]>, bool);

    fn run(first: &[u8], last: Option<&[u8]>, reverse: bool) -> Arc<ScanRun> {
        let cell = OnceLock::new();
        if let Some(last) = last {
            cell.get_or_init(|| last.to_vec());
        }
        Arc::new(ScanRun {
            first: first.to_vec(),
            last: cell,
            reverse,
        })
    }

    #[test]
    fn walked_merges_overlapping_and_touching_runs_and_keeps_gaps() {
        let runs = [
            run(b"m", Some(b"p"), false),
            run(b"d", Some(b"b"), true),
            run(b"p", Some(b"q"), false),
            run(b"c", Some(b"e"), false),
            run(b"x", Some(b"x"), false),
        ];
        let got = walked(&runs);
        let span = |lo: &'static [u8], hi: &'static [u8]| Walked {
            lo: Some(lo),
            hi: Some(hi),
        };
        assert_eq!(got, [span(b"b", b"e"), span(b"m", b"q"), span(b"x", b"x")]);
        assert!(covers(&got, b"b") && covers(&got, b"e") && covers(&got, b"x"));
        assert!(!covers(&got, b"a") && !covers(&got, b"f") && !covers(&got, b"r"));
        assert!(
            !covers(&got, b"xa"),
            "a key just above an inclusive end is outside"
        );
    }

    #[test]
    fn an_unclosed_run_reaches_the_end_of_the_keyspace_in_its_direction() {
        let forward = [run(b"m", None, false), run(b"x", Some(b"y"), false)];
        let got = walked(&forward);
        assert_eq!(got.len(), 1, "the unbounded run swallows the later one");
        assert!(covers(&got, b"m") && covers(&got, b"\xff\xff"));
        assert!(!covers(&got, b"l"));

        let reverse = [run(b"m", None, true)];
        let got = walked(&reverse);
        assert!(covers(&got, b"") && covers(&got, b"m"));
        assert!(!covers(&got, b"n"));
    }

    #[test]
    fn cover_anchors_walked_reads_and_adds_walked_writes_once() {
        let runs = [run(b"b", Some(b"d"), false)];
        let mut reads = vec![
            ConflictKey {
                key: b"a".to_vec(),
                observed_seq: 9,
            },
            ConflictKey {
                key: b"c".to_vec(),
                observed_seq: 9,
            },
        ];
        let writes: BTreeMap<Vec<u8>, Option<Vec<u8>>> = [
            (b"b".to_vec(), Some(b"v".to_vec())),
            (b"c".to_vec(), None),
            (b"e".to_vec(), None),
        ]
        .into_iter()
        .collect();
        let merges = vec![
            (b"d".to_vec(), b"op".to_vec()),
            (b"d".to_vec(), b"op".to_vec()),
        ];
        cover(&mut reads, &runs, &writes, &merges, 4);
        let got: Vec<(Vec<u8>, u64)> = reads
            .into_iter()
            .map(|read| (read.key, read.observed_seq))
            .collect();
        assert_eq!(
            got,
            [
                (b"a".to_vec(), 9),
                (b"b".to_vec(), 4),
                (b"c".to_vec(), 4),
                (b"d".to_vec(), 4),
            ]
        );
    }

    #[test]
    fn a_scan_below_serializable_records_one_run_per_stretch_and_no_key() {
        let dir = TempDir::new().unwrap();
        let db = OptimisticTransactionDb::open(dir.path(), Options::default()).unwrap();
        for key in [b"a", b"b", b"c"] {
            db.db().put(key, b"0").unwrap();
        }
        let mut tx = db.begin_transaction_with(IsolationLevel::SnapshotIsolation);
        assert_eq!(tx.scan_stream(None, None).count(), 3);
        assert_eq!(tx.tracked.len(), 0, "no key is tracked below Serializable");
        tx.put(b"b", b"pending").unwrap();
        assert_eq!(
            tx.scan_stream_in(None, None, ScanDirection::Reverse)
                .count(),
            3
        );
        let runs = tx.scan_runs.take().map(|runs| drain(&runs)).unwrap();
        let spans: Vec<Span<'_>> = runs
            .iter()
            .map(|run| {
                (
                    &run.first[4..],
                    run.last.get().map(|last| &last[4..]),
                    run.reverse,
                )
            })
            .collect();
        assert_eq!(
            spans,
            [
                (&b"a"[..], Some(&b"c"[..]), false),
                (&b"c"[..], Some(&b"c"[..]), true),
                (&b"a"[..], Some(&b"a"[..]), true),
            ],
            "one run per stretch, split at the buffered b"
        );
        let tracked = tx.tracked.drain();
        let mut checks = tx.validation_set(tracked, &BTreeMap::new(), &[]);
        cover(
            &mut checks.reads,
            &runs,
            &BTreeMap::new(),
            &[],
            tx.snapshot_seq,
        );
        assert!(
            checks.reads.is_empty(),
            "a read-only commit validates nothing"
        );
    }

    proptest! {
        #[test]
        fn covers_agrees_with_checking_every_run(
            specs in proptest::collection::vec((0u8..8, proptest::option::of(0u8..8), any::<bool>()), 0..8),
            probe in 0u8..9,
        ) {
            let runs: Vec<Arc<ScanRun>> = specs
                .iter()
                .map(|(first, last, reverse)| {
                    // A walk yields in its direction, so `last` is never behind `first`.
                    let last = last.map(|last| if *reverse { last.min(*first) } else { last.max(*first) });
                    run(&[*first], last.as_ref().map(std::slice::from_ref), *reverse)
                })
                .collect();
            let key = [probe];
            let naive = runs.iter().any(|run| {
                let first = run.first.as_slice();
                let last = run.last.get().map(Vec::as_slice);
                if run.reverse {
                    key.as_slice() <= first && last.is_none_or(|last| last <= key.as_slice())
                } else {
                    first <= key.as_slice() && last.is_none_or(|last| key.as_slice() <= last)
                }
            });
            let merged = walked(&runs);
            prop_assert!(merged.windows(2).all(|pair| !reaches(pair[0].hi, pair[1].lo)));
            prop_assert_eq!(covers(&merged, &key), naive);
        }
    }
}
