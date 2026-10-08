//! A transaction reads its own buffered merges.
//!
//! A read of a key the transaction merged into answers what the merge
//! operator makes of the value the transaction reads for the key, then its
//! own operands in the order it made them. A put or a delete of the key
//! resets that value, so the operands buffered before it no longer count,
//! and a commit stores exactly what the read answered. Each case runs on
//! both transaction flavours.

// Native-only. wasm-pack builds every test target for wasm32, and these use
// the filesystem. The browser suite lives in tests/wasm_opfs*.rs.
#![cfg(not(target_arch = "wasm32"))]

use std::path::Path;
use std::sync::Arc;

use regolith::{
    Db, IsolationLevel, MergeOperator, OptimisticTransactionDb, Options, Transaction,
    TransactionDb, TransactionError,
};

/// Sums big-endian i64 deltas onto the base.
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

/// Appends every operand to the base in order, so the order the operands
/// were folded in shows in the result.
struct AppendMerge;

impl MergeOperator for AppendMerge {
    fn name(&self) -> &'static str {
        "append"
    }

    fn full_merge(&self, _key: &[u8], base: Option<&[u8]>, operands: &[&[u8]]) -> Option<Vec<u8>> {
        let mut out = base.map(<[u8]>::to_vec).unwrap_or_default();
        for operand in operands {
            out.extend_from_slice(operand);
        }
        Some(out)
    }
}

fn counting() -> Options {
    Options {
        merge_operator: Some(Arc::new(CounterMerge)),
        ..Options::default()
    }
}

fn appending() -> Options {
    Options {
        merge_operator: Some(Arc::new(AppendMerge)),
        ..Options::default()
    }
}

fn delta(n: i64) -> [u8; 8] {
    n.to_be_bytes()
}

/// Either transaction flavour behind one type.
enum Flavour {
    Optimistic(OptimisticTransactionDb),
    Pessimistic(TransactionDb),
}

impl Flavour {
    fn open(optimistic: bool, dir: &Path, options: Options) -> Self {
        if optimistic {
            Self::Optimistic(OptimisticTransactionDb::open(dir, options).unwrap())
        } else {
            Self::Pessimistic(TransactionDb::open(dir, options).unwrap())
        }
    }

    fn begin(&self) -> Transaction<'_> {
        match self {
            Self::Optimistic(db) => db.begin_transaction(),
            Self::Pessimistic(db) => db.begin_transaction(),
        }
    }

    fn db(&self) -> &Db {
        match self {
            Self::Optimistic(db) => db.db(),
            Self::Pessimistic(db) => db.db(),
        }
    }
}

/// Run `check` against a fresh database of each flavour.
fn each_flavour(options: fn() -> Options, check: impl Fn(&Flavour)) {
    for optimistic in [true, false] {
        let dir = tempfile::tempdir().unwrap();
        check(&Flavour::open(optimistic, dir.path(), options()));
    }
}

fn counter(bytes: Option<Vec<u8>>) -> Option<i64> {
    bytes.map(|bytes| i64::from_be_bytes(bytes[..].try_into().unwrap()))
}

/// What the transaction reads for `key` through each of its point reads,
/// which must agree.
fn reads(tx: &Transaction<'_>, key: &[u8]) -> Option<Vec<u8>> {
    let got = tx.get(key).unwrap();
    assert_eq!(
        tx.get_slice(key).unwrap().map(|slice| slice.to_vec()),
        got,
        "get_slice disagrees with get"
    );
    assert_eq!(
        tx.get_for_update(key).unwrap(),
        got,
        "get_for_update disagrees with get"
    );
    got
}

#[test]
fn two_merges_into_a_counter_read_back_as_the_base_plus_both() {
    each_flavour(counting, |flavour| {
        flavour.db().put(b"k", &delta(10)).unwrap();
        let tx = flavour.begin();
        tx.merge(b"k", &delta(1)).unwrap();
        assert_eq!(counter(reads(&tx, b"k")), Some(11));
        tx.merge(b"k", &delta(1)).unwrap();
        assert_eq!(counter(reads(&tx, b"k")), Some(12));
        assert_eq!(
            counter(flavour.db().get(b"k").unwrap()),
            Some(10),
            "nothing is visible outside before the commit"
        );
        tx.commit().unwrap();
        assert_eq!(counter(flavour.db().get(b"k").unwrap()), Some(12));
    });
}

#[test]
fn a_merge_into_an_absent_key_starts_from_nothing() {
    each_flavour(counting, |flavour| {
        let tx = flavour.begin();
        assert_eq!(reads(&tx, b"k"), None);
        tx.merge(b"k", &delta(7)).unwrap();
        assert_eq!(counter(reads(&tx, b"k")), Some(7));
        tx.commit().unwrap();
        assert_eq!(counter(flavour.db().get(b"k").unwrap()), Some(7));
    });
}

#[test]
fn a_merge_made_after_a_put_applies_to_the_put() {
    each_flavour(counting, |flavour| {
        flavour.db().put(b"k", &delta(10)).unwrap();
        let tx = flavour.begin();
        tx.put(b"k", &delta(100)).unwrap();
        tx.merge(b"k", &delta(1)).unwrap();
        assert_eq!(counter(reads(&tx, b"k")), Some(101));
        tx.commit().unwrap();
        assert_eq!(counter(flavour.db().get(b"k").unwrap()), Some(101));
    });
}

#[test]
fn a_put_made_after_a_merge_discards_the_merge() {
    each_flavour(counting, |flavour| {
        flavour.db().put(b"k", &delta(10)).unwrap();
        let tx = flavour.begin();
        tx.merge(b"k", &delta(1)).unwrap();
        tx.put(b"k", &delta(100)).unwrap();
        assert_eq!(counter(reads(&tx, b"k")), Some(100));
        tx.commit().unwrap();
        assert_eq!(
            counter(flavour.db().get(b"k").unwrap()),
            Some(100),
            "the commit stores what the transaction read"
        );
    });
}

#[test]
fn a_delete_resets_the_base_like_a_put() {
    each_flavour(counting, |flavour| {
        flavour.db().put(b"gone", &delta(10)).unwrap();
        flavour.db().put(b"reborn", &delta(10)).unwrap();
        let tx = flavour.begin();

        tx.merge(b"gone", &delta(1)).unwrap();
        tx.delete(b"gone").unwrap();
        assert_eq!(reads(&tx, b"gone"), None);

        tx.delete(b"reborn").unwrap();
        tx.merge(b"reborn", &delta(5)).unwrap();
        assert_eq!(counter(reads(&tx, b"reborn")), Some(5));

        tx.commit().unwrap();
        assert_eq!(flavour.db().get(b"gone").unwrap(), None);
        assert_eq!(counter(flavour.db().get(b"reborn").unwrap()), Some(5));
    });
}

#[test]
fn puts_and_merges_fold_in_the_order_they_were_made() {
    each_flavour(appending, |flavour| {
        flavour.db().put(b"k", b"x").unwrap();
        let tx = flavour.begin();
        tx.merge(b"k", b"a").unwrap();
        assert_eq!(reads(&tx, b"k").as_deref(), Some(&b"xa"[..]));
        tx.put(b"k", b"P").unwrap();
        tx.merge(b"k", b"b").unwrap();
        tx.merge(b"k", b"c").unwrap();
        assert_eq!(reads(&tx, b"k").as_deref(), Some(&b"Pbc"[..]));
        tx.delete(b"k").unwrap();
        tx.merge(b"k", b"d").unwrap();
        tx.merge(b"k", b"e").unwrap();
        assert_eq!(reads(&tx, b"k").as_deref(), Some(&b"de"[..]));
        tx.commit().unwrap();
        assert_eq!(flavour.db().get(b"k").unwrap().as_deref(), Some(&b"de"[..]));
    });
}

#[test]
fn merges_into_different_keys_do_not_mix() {
    each_flavour(appending, |flavour| {
        flavour.db().put(b"a", b"1").unwrap();
        flavour.db().put(b"b", b"2").unwrap();
        let tx = flavour.begin();
        tx.merge(b"a", b"x").unwrap();
        tx.merge(b"b", b"y").unwrap();
        tx.merge(b"a", b"z").unwrap();
        assert_eq!(reads(&tx, b"a").as_deref(), Some(&b"1xz"[..]));
        assert_eq!(reads(&tx, b"b").as_deref(), Some(&b"2y"[..]));
        assert_eq!(reads(&tx, b"c"), None);
    });
}

#[test]
fn a_failing_merge_is_an_error_not_a_stale_value() {
    each_flavour(counting, |flavour| {
        flavour.db().put(b"k", &delta(10)).unwrap();
        let tx = flavour.begin();
        tx.merge(b"k", b"not a delta").unwrap();
        for result in [
            tx.get(b"k").map(|_| ()),
            tx.get_slice(b"k").map(|_| ()),
            tx.get_for_update(b"k").map(|_| ()),
        ] {
            let Err(TransactionError::Io(e)) = result else {
                panic!("expected the merge failure, got {result:?}");
            };
            assert!(e.to_string().contains("counter"), "{e}");
        }
    });
}

#[test]
fn without_a_merge_operator_reads_ignore_buffered_merges() {
    each_flavour(Options::default, |flavour| {
        flavour.db().put(b"committed", b"v").unwrap();
        let tx = flavour.begin();
        tx.merge(b"committed", b"op").unwrap();
        tx.put(b"put", b"p").unwrap();
        tx.merge(b"put", b"op").unwrap();
        tx.merge(b"absent", b"op").unwrap();
        assert_eq!(reads(&tx, b"committed").as_deref(), Some(&b"v"[..]));
        assert_eq!(reads(&tx, b"put").as_deref(), Some(&b"p"[..]));
        assert_eq!(reads(&tx, b"absent"), None);
        let scanned: Vec<_> = tx
            .scan_stream(None, None)
            .map(|(key, value)| (key, value.to_vec()))
            .collect();
        assert_eq!(
            scanned,
            [
                (b"committed".to_vec(), b"v".to_vec()),
                (b"put".to_vec(), b"p".to_vec()),
            ]
        );
    });
}

/// `(key, value)` pairs of a transaction scan as counters.
fn scanned(
    tx: &Transaction<'_>,
    start: Option<&[u8]>,
    end: Option<&[u8]>,
    reverse: bool,
) -> Vec<(Vec<u8>, i64)> {
    let direction = if reverse {
        regolith::ScanDirection::Reverse
    } else {
        regolith::ScanDirection::Forward
    };
    let mut stream = tx.scan_stream_in(start, end, direction);
    let got = stream
        .by_ref()
        .map(|(key, value)| (key, counter(Some(value.to_vec())).unwrap()))
        .collect();
    stream.status().unwrap();
    got
}

#[test]
fn a_scan_lays_the_merges_over_the_snapshot_in_both_directions() {
    each_flavour(counting, |flavour| {
        for (key, value) in [(b"a", 10), (b"c", 30), (b"d", 40), (b"e", 50)] {
            flavour.db().put(key, &delta(value)).unwrap();
        }
        let tx = flavour.begin();
        tx.merge(b"a", &delta(1)).unwrap();
        tx.merge(b"b", &delta(5)).unwrap();
        tx.merge(b"c", &delta(1)).unwrap();
        tx.put(b"c", &delta(100)).unwrap();
        tx.delete(b"d").unwrap();
        tx.merge(b"d", &delta(2)).unwrap();
        tx.merge(b"e", &delta(1)).unwrap();
        tx.delete(b"e").unwrap();
        tx.put(b"f", &delta(7)).unwrap();
        tx.merge(b"f", &delta(1)).unwrap();

        let want: Vec<(Vec<u8>, i64)> = [("a", 11), ("b", 5), ("c", 100), ("d", 2), ("f", 8)]
            .into_iter()
            .map(|(key, value)| (key.as_bytes().to_vec(), value))
            .collect();
        assert_eq!(scanned(&tx, None, None, false), want);

        let mut backwards = want.clone();
        backwards.reverse();
        assert_eq!(scanned(&tx, None, None, true), backwards);

        assert_eq!(
            scanned(&tx, Some(b"b"), Some(b"d"), false),
            want[1..3],
            "a bounded range holds only its keys"
        );
        assert_eq!(scanned(&tx, Some(b"b"), Some(b"d"), true), {
            let mut inner = want[1..3].to_vec();
            inner.reverse();
            inner
        });

        let first: Vec<_> = tx.scan_stream(None, None).take(1).collect();
        assert_eq!(
            first.len(),
            1,
            "a caller that stops early gets what it read"
        );
        assert_eq!(first[0].0, b"a".to_vec());
        assert_eq!(counter(Some(first[0].1.to_vec())), Some(11));
    });
}

#[test]
fn a_savepoint_rollback_restores_the_merges_buffered_before_it() {
    each_flavour(counting, |flavour| {
        flavour.db().put(b"k", &delta(10)).unwrap();
        let mut tx = flavour.begin();
        tx.merge(b"k", &delta(1)).unwrap();
        tx.set_savepoint();
        tx.merge(b"k", &delta(2)).unwrap();
        assert_eq!(counter(reads(&tx, b"k")), Some(13));
        tx.rollback_to_savepoint().unwrap();
        assert_eq!(counter(reads(&tx, b"k")), Some(11));

        tx.set_savepoint();
        tx.put(b"k", &delta(100)).unwrap();
        assert_eq!(counter(reads(&tx, b"k")), Some(100));
        tx.rollback_to_savepoint().unwrap();
        assert_eq!(
            counter(reads(&tx, b"k")),
            Some(11),
            "the merge buffered before the savepoint is back"
        );

        tx.put(b"k", &delta(50)).unwrap();
        tx.set_savepoint();
        tx.merge(b"k", &delta(1)).unwrap();
        tx.rollback_to_savepoint().unwrap();
        assert_eq!(counter(reads(&tx, b"k")), Some(50));
        tx.commit().unwrap();
        assert_eq!(counter(flavour.db().get(b"k").unwrap()), Some(50));
    });
}

#[test]
fn reading_a_merged_key_makes_the_merge_a_read_modify_write() {
    let dir = tempfile::tempdir().unwrap();
    let db = OptimisticTransactionDb::open(dir.path(), counting()).unwrap();
    db.db().put(b"k", &delta(10)).unwrap();

    let tx = db.begin_transaction_with(IsolationLevel::DefraLevel);
    tx.merge(b"k", &delta(1)).unwrap();
    assert_eq!(counter(tx.get(b"k").unwrap()), Some(11));
    db.db().merge(b"k", &delta(1)).unwrap();
    assert!(
        matches!(tx.commit(), Err(TransactionError::Conflict { .. })),
        "the value the transaction read is stale"
    );

    let blind = db.begin_transaction_with(IsolationLevel::DefraLevel);
    blind.merge(b"k", &delta(1)).unwrap();
    db.db().merge(b"k", &delta(1)).unwrap();
    blind.commit().expect("a blind merge still commutes");
}
