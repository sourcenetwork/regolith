//! `IsolationLevel::DefraLevel`: RepeatableRead, relaxed only where the
//! keyspace rules a conflict out.
//!
//! Each relaxation is shown next to the RepeatableRead outcome it replaces,
//! and next to the conflicts it must keep.

// Native-only. wasm-pack builds every test target for wasm32, and these use
// threads and the filesystem. The browser suite lives in tests/wasm_opfs*.rs.
#![cfg(not(target_arch = "wasm32"))]

use std::sync::Arc;

use regolith::prelude::*;

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

/// Keys under `h/` are added under fresh names and never contended.
struct HeadPrefix;

impl KeyClassifier for HeadPrefix {
    fn classify(&self, key: &[u8]) -> KeyClass {
        if key.starts_with(b"h/") {
            KeyClass::CommutativePrefix { len: 2 }
        } else {
            KeyClass::Ordinary
        }
    }
}

fn open(dir: &std::path::Path) -> OptimisticTransactionDb {
    let options = Options {
        merge_operator: Some(Arc::new(CounterMerge)),
        ..Options::default()
    };
    OptimisticTransactionDb::open(dir, options)
        .unwrap()
        .with_policy(Arc::new(HeadPrefix))
}

fn counter(db: &OptimisticTransactionDb) -> i64 {
    i64::from_be_bytes(
        db.db().get(b"counter").unwrap().unwrap()[..]
            .try_into()
            .unwrap(),
    )
}

fn conflicted(result: TxResult<()>) -> bool {
    matches!(result, Err(TransactionError::Conflict { .. }))
}

#[test]
fn point_reads_are_validated_as_at_repeatable_read() {
    let dir = tempfile::tempdir().unwrap();
    let db = open(dir.path());
    db.db().put(b"k", b"old").unwrap();

    let tx = db.begin_transaction_with(IsolationLevel::DefraLevel);
    tx.get(b"k").unwrap();
    db.db().put(b"k", b"new").unwrap();
    tx.put(b"elsewhere", b"x").unwrap();
    assert!(conflicted(tx.commit()));
}

#[test]
fn concurrent_blind_merges_commit_where_repeatable_read_aborts() {
    for flush in [false, true] {
        for (level, both_commit) in [
            (IsolationLevel::DefraLevel, true),
            (IsolationLevel::RepeatableRead, false),
        ] {
            let dir = tempfile::tempdir().unwrap();
            let db = open(dir.path());
            db.db().put(b"counter", &0i64.to_be_bytes()).unwrap();

            let first = db.begin_transaction_with(level);
            let second = db.begin_transaction_with(level);
            first.merge(b"counter", &1i64.to_be_bytes()).unwrap();
            second.merge(b"counter", &1i64.to_be_bytes()).unwrap();
            first.commit().unwrap();
            if flush {
                db.db().flush().unwrap();
            }
            let second = second.commit();
            assert_eq!(
                second.is_ok(),
                both_commit,
                "{level:?} flush={flush}: {second:?}"
            );
            assert_eq!(counter(&db), if both_commit { 2 } else { 1 });
        }
    }
}

#[test]
fn eight_threads_of_blind_merges_never_conflict_and_lose_nothing() {
    const THREADS: i64 = 8;
    const MERGES: i64 = 200;
    let dir = tempfile::tempdir().unwrap();
    let db = open(dir.path());
    db.db().put(b"counter", &0i64.to_be_bytes()).unwrap();

    std::thread::scope(|scope| {
        for _ in 0..THREADS {
            scope.spawn(|| {
                for i in 0..MERGES {
                    let tx = db.begin_transaction_with(IsolationLevel::DefraLevel);
                    tx.merge(b"counter", &1i64.to_be_bytes()).unwrap();
                    tx.commit().expect("a blind merge never conflicts");
                    if i % 50 == 0 {
                        db.db().flush().unwrap();
                    }
                }
            });
        }
    });
    assert_eq!(counter(&db), THREADS * MERGES);
}

/// A write that replaces a key outright instead of building on it.
#[derive(Clone, Copy, Debug)]
enum Replacement {
    Put,
    Delete,
    RangeDelete,
}

impl Replacement {
    fn apply(self, db: &OptimisticTransactionDb) {
        match self {
            Self::Put => db.db().put(b"counter", &5i64.to_be_bytes()).unwrap(),
            Self::Delete => db.db().delete(b"counter").unwrap(),
            Self::RangeDelete => db.db().delete_range(b"c", b"d").unwrap(),
        }
    }
}

#[test]
fn a_blind_merge_still_conflicts_with_a_newer_replacement() {
    for replacement in [
        Replacement::Put,
        Replacement::Delete,
        Replacement::RangeDelete,
    ] {
        for flush in [false, true] {
            let dir = tempfile::tempdir().unwrap();
            let db = open(dir.path());
            db.db().put(b"counter", &0i64.to_be_bytes()).unwrap();

            let tx = db.begin_transaction_with(IsolationLevel::DefraLevel);
            tx.merge(b"counter", &1i64.to_be_bytes()).unwrap();
            replacement.apply(&db);
            // Operands on top of the replacement do not hide it.
            db.db().merge(b"counter", &1i64.to_be_bytes()).unwrap();
            if flush {
                db.db().flush().unwrap();
            }
            assert!(conflicted(tx.commit()), "{replacement:?} flush={flush}");
        }
    }
}

#[test]
fn a_merge_into_a_key_the_transaction_read_is_not_blind() {
    let dir = tempfile::tempdir().unwrap();
    let db = open(dir.path());
    db.db().put(b"counter", &0i64.to_be_bytes()).unwrap();

    let tx = db.begin_transaction_with(IsolationLevel::DefraLevel);
    tx.get(b"counter").unwrap();
    tx.merge(b"counter", &1i64.to_be_bytes()).unwrap();
    db.db().merge(b"counter", &1i64.to_be_bytes()).unwrap();
    assert!(conflicted(tx.commit()));
}

#[test]
fn a_merge_beside_a_put_of_the_same_key_is_not_blind() {
    let dir = tempfile::tempdir().unwrap();
    let db = open(dir.path());
    db.db().put(b"counter", &0i64.to_be_bytes()).unwrap();

    let tx = db.begin_transaction_with(IsolationLevel::DefraLevel);
    tx.put(b"counter", &3i64.to_be_bytes()).unwrap();
    tx.merge(b"counter", &1i64.to_be_bytes()).unwrap();
    db.db().merge(b"counter", &1i64.to_be_bytes()).unwrap();
    assert!(conflicted(tx.commit()));
}

/// Scan the head prefix, then write the marker every writer writes. The
/// marker sorts between the heads, so it lies inside the stretch walked.
fn supersede(tx: &Transaction<'_>, start: &[u8], end: &[u8]) {
    let walked: Vec<_> = tx.scan_stream(Some(start), Some(end)).collect();
    assert!(!walked.is_empty());
    tx.put(b"h/m", b"superseded").unwrap();
}

#[test]
fn an_identical_write_inside_a_scanned_commutative_prefix_commits() {
    for (level, both_commit) in [
        (IsolationLevel::DefraLevel, true),
        (IsolationLevel::RepeatableRead, false),
    ] {
        let dir = tempfile::tempdir().unwrap();
        let db = open(dir.path());
        db.db().put(b"h/a", b"cid").unwrap();
        db.db().put(b"h/z", b"cid").unwrap();

        let first = db.begin_transaction_with(level);
        let second = db.begin_transaction_with(level);
        supersede(&first, b"h/", b"h0");
        supersede(&second, b"h/", b"h0");
        first.commit().unwrap();
        let second = second.commit();
        assert_eq!(second.is_ok(), both_commit, "{level:?}: {second:?}");
    }
}

#[test]
fn a_scan_leaving_the_commutative_prefix_is_still_recorded() {
    let dir = tempfile::tempdir().unwrap();
    let db = open(dir.path());
    db.db().put(b"h/a", b"cid").unwrap();
    db.db().put(b"i/other", b"x").unwrap();

    let first = db.begin_transaction_with(IsolationLevel::DefraLevel);
    let second = db.begin_transaction_with(IsolationLevel::DefraLevel);
    supersede(&first, b"h/", b"j");
    supersede(&second, b"h/", b"j");
    first.commit().unwrap();
    assert!(conflicted(second.commit()));
}

#[test]
fn without_a_policy_scans_are_recorded_as_at_repeatable_read() {
    let dir = tempfile::tempdir().unwrap();
    let db = OptimisticTransactionDb::open(dir.path(), Options::default()).unwrap();
    db.db().put(b"h/a", b"cid").unwrap();
    db.db().put(b"h/z", b"cid").unwrap();

    let first = db.begin_transaction_with(IsolationLevel::DefraLevel);
    let second = db.begin_transaction_with(IsolationLevel::DefraLevel);
    supersede(&first, b"h/", b"h0");
    supersede(&second, b"h/", b"h0");
    first.commit().unwrap();
    assert!(conflicted(second.commit()));
}
