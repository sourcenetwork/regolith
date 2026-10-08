//! `KeyClass::ContentAddressed`: at `DefraLevel` with a classifier installed,
//! no read or write of a key that determines its bytes is validated.
//!
//! A block store keys each block by its content hash and reads every block it
//! is about to write, so two transactions that create documents sharing a
//! block would conflict on it. Declared content-addressed, the key is left out
//! of validation altogether and both commit. Each case sits beside the
//! conflict that stays: on an ordinary key, at another level, or with no
//! classifier installed.

// Native-only. wasm-pack builds every test target for wasm32, and these use
// the filesystem. The browser suite lives in tests/wasm_opfs*.rs.
#![cfg(not(target_arch = "wasm32"))]

use std::path::Path;
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

/// Keys under `b/` are blocks named by their content; keys under `h/` are
/// heads added under fresh names and never contended.
struct Keys;

impl KeyClassifier for Keys {
    fn classify(&self, key: &[u8]) -> KeyClass {
        if key.starts_with(b"b/") {
            KeyClass::ContentAddressed
        } else if key.starts_with(b"h/") {
            KeyClass::CommutativePrefix { len: 2 }
        } else {
            KeyClass::Ordinary
        }
    }
}

fn options() -> Options {
    Options {
        merge_operator: Some(Arc::new(CounterMerge)),
        ..Options::default()
    }
}

fn open(dir: &Path) -> OptimisticTransactionDb {
    OptimisticTransactionDb::open(dir, options())
        .unwrap()
        .with_policy(Arc::new(Keys))
}

fn conflicted(result: TxResult<()>) -> bool {
    matches!(result, Err(TransactionError::Conflict { .. }))
}

/// The key a failed commit named, if it failed on a conflict.
fn conflict_key(result: TxResult<()>) -> Option<Vec<u8>> {
    match result {
        Err(TransactionError::Conflict { key, .. }) => Some(key),
        _ => None,
    }
}

/// Two transactions at `level` that each read `key` and put the same bytes
/// under it, as a block store does for a block it is about to write. Returns
/// what the second commit made of it, the first having committed.
fn both_create(db: &OptimisticTransactionDb, level: IsolationLevel, key: &[u8]) -> TxResult<()> {
    let first = db.begin_transaction_with(level);
    let second = db.begin_transaction_with(level);
    for tx in [&first, &second] {
        assert_eq!(tx.get_for_update(key).unwrap(), None);
        tx.put(key, b"bytes").unwrap();
    }
    first.commit().unwrap();
    second.commit()
}

#[test]
fn two_transactions_that_create_the_same_block_both_commit() {
    for flush in [false, true] {
        let dir = tempfile::tempdir().unwrap();
        let db = open(dir.path());
        let first = db.begin_transaction_with(IsolationLevel::DefraLevel);
        let second = db.begin_transaction_with(IsolationLevel::DefraLevel);
        for tx in [&first, &second] {
            assert_eq!(tx.get_for_update(b"b/shared").unwrap(), None);
            tx.put(b"b/shared", b"bytes").unwrap();
        }
        first.commit().unwrap();
        if flush {
            db.db().flush().unwrap();
        }
        second
            .commit()
            .unwrap_or_else(|e| panic!("flush={flush}: {e:?}"));
        assert_eq!(
            db.db().get(b"b/shared").unwrap().as_deref(),
            Some(&b"bytes"[..])
        );
    }
}

#[test]
fn an_ordinary_key_beside_it_keeps_conflicting() {
    let dir = tempfile::tempdir().unwrap();
    let db = open(dir.path());
    assert_eq!(
        conflict_key(both_create(&db, IsolationLevel::DefraLevel, b"ordinary")),
        Some(b"ordinary".to_vec())
    );
}

#[test]
fn without_a_classifier_the_same_block_conflicts() {
    let dir = tempfile::tempdir().unwrap();
    let db = OptimisticTransactionDb::open(dir.path(), options()).unwrap();
    assert!(conflicted(both_create(
        &db,
        IsolationLevel::DefraLevel,
        b"b/shared"
    )));
}

#[test]
fn other_levels_with_the_same_classifier_conflict_as_before() {
    for level in [
        IsolationLevel::SnapshotIsolation,
        IsolationLevel::RepeatableRead,
        IsolationLevel::Serializable,
    ] {
        let dir = tempfile::tempdir().unwrap();
        let db = open(dir.path());
        assert!(
            conflicted(both_create(&db, level, b"b/shared")),
            "{level:?}"
        );
    }
}

#[test]
fn different_bytes_under_one_key_commit_too_and_the_last_commit_wins() {
    // The caller's contract is that a content-addressed key never holds
    // different bytes. regolith cannot check it, so the rule is "never
    // conflicts" and the later commit decides what the key holds.
    for one_commits_last in [false, true] {
        let dir = tempfile::tempdir().unwrap();
        let db = open(dir.path());
        let one = db.begin_transaction_with(IsolationLevel::DefraLevel);
        let two = db.begin_transaction_with(IsolationLevel::DefraLevel);
        for (tx, bytes) in [(&one, b"one"), (&two, b"two")] {
            tx.get_for_update(b"b/shared").unwrap();
            tx.put(b"b/shared", bytes).unwrap();
        }
        let (earlier, later) = if one_commits_last {
            (two, one)
        } else {
            (one, two)
        };
        earlier.commit().unwrap();
        later.commit().unwrap();
        let want: &[u8] = if one_commits_last { b"one" } else { b"two" };
        assert_eq!(db.db().get(b"b/shared").unwrap().as_deref(), Some(want));
    }
}

#[test]
fn a_delete_of_a_block_beside_a_put_of_it_commits_in_either_order() {
    for delete_first in [false, true] {
        let dir = tempfile::tempdir().unwrap();
        let db = open(dir.path());
        db.db().put(b"b/shared", b"bytes").unwrap();
        let put = db.begin_transaction_with(IsolationLevel::DefraLevel);
        let delete = db.begin_transaction_with(IsolationLevel::DefraLevel);
        put.get_for_update(b"b/shared").unwrap();
        put.put(b"b/shared", b"bytes").unwrap();
        delete.get_for_update(b"b/shared").unwrap();
        delete.delete(b"b/shared").unwrap();
        if delete_first {
            delete.commit().unwrap();
            put.commit().unwrap();
        } else {
            put.commit().unwrap();
            delete.commit().unwrap();
        }
        let want: Option<&[u8]> = if delete_first { Some(b"bytes") } else { None };
        assert_eq!(db.db().get(b"b/shared").unwrap().as_deref(), want);
    }
}

#[test]
fn a_transaction_mixing_both_kinds_conflicts_only_on_the_ordinary_one() {
    let dir = tempfile::tempdir().unwrap();
    let db = open(dir.path());
    let first = db.begin_transaction_with(IsolationLevel::DefraLevel);
    let second = db.begin_transaction_with(IsolationLevel::DefraLevel);
    for tx in [&first, &second] {
        tx.get_for_update(b"b/shared").unwrap();
        tx.put(b"b/shared", b"bytes").unwrap();
        tx.get_for_update(b"ordinary").unwrap();
        tx.put(b"ordinary", b"mine").unwrap();
    }
    first.commit().unwrap();
    // "b/shared" sorts before "ordinary", so a conflict on the block would
    // be the one reported.
    assert_eq!(conflict_key(second.commit()), Some(b"ordinary".to_vec()));

    let first = db.begin_transaction_with(IsolationLevel::DefraLevel);
    let second = db.begin_transaction_with(IsolationLevel::DefraLevel);
    for (tx, own) in [(&first, &b"first"[..]), (&second, &b"second"[..])] {
        tx.get_for_update(b"b/other").unwrap();
        tx.put(b"b/other", b"bytes").unwrap();
        tx.put(own, b"mine").unwrap();
    }
    first.commit().unwrap();
    second
        .commit()
        .expect("sharing only a block is no conflict");
}

/// A transaction at `level` reads `b/block`, which a plain write rewrites
/// before it commits. Returns whether the commit succeeded, with or without a
/// write elsewhere (a read-only commit still validates its reads).
fn reads_a_block_that_changes(
    level: IsolationLevel,
    for_update: bool,
    write_elsewhere: bool,
) -> bool {
    let dir = tempfile::tempdir().unwrap();
    let db = open(dir.path());
    db.db().put(b"b/block", b"bytes").unwrap();
    let tx = db.begin_transaction_with(level);
    if for_update {
        tx.get_for_update(b"b/block").unwrap();
    } else {
        tx.get(b"b/block").unwrap();
    }
    db.db().put(b"b/block", b"bytes").unwrap();
    if write_elsewhere {
        tx.put(b"elsewhere", b"x").unwrap();
    }
    tx.commit().is_ok()
}

#[test]
fn a_read_of_a_block_is_not_validated() {
    for for_update in [false, true] {
        for write_elsewhere in [false, true] {
            assert!(
                reads_a_block_that_changes(IsolationLevel::DefraLevel, for_update, write_elsewhere),
                "for_update={for_update} write_elsewhere={write_elsewhere}"
            );
        }
    }
    assert!(!reads_a_block_that_changes(
        IsolationLevel::RepeatableRead,
        false,
        true
    ));
    assert!(!reads_a_block_that_changes(
        IsolationLevel::RepeatableRead,
        true,
        false
    ));
    assert!(!reads_a_block_that_changes(
        IsolationLevel::SnapshotIsolation,
        true,
        true
    ));
}

/// A transaction at `level` scans `[prefix, end)`, then puts `key` inside the
/// stretch, which a plain write rewrites before it commits. Returns whether
/// the commit succeeded.
fn scans_then_writes(level: IsolationLevel, prefix: &[u8], end: &[u8], key: &[u8]) -> bool {
    let dir = tempfile::tempdir().unwrap();
    let db = open(dir.path());
    for name in [b"1", b"2", b"3"] {
        let mut scanned = prefix.to_vec();
        scanned.extend_from_slice(name);
        db.db().put(&scanned, b"bytes").unwrap();
    }
    let tx = db.begin_transaction_with(level);
    assert_eq!(tx.scan_stream(Some(prefix), Some(end)).count(), 3);
    tx.put(key, b"mine").unwrap();
    db.db().put(key, b"changed").unwrap();
    tx.commit().is_ok()
}

#[test]
fn a_scan_that_returns_a_block_records_no_read_for_it() {
    assert!(scans_then_writes(
        IsolationLevel::DefraLevel,
        b"b/",
        b"b0",
        b"b/2"
    ));
    assert!(
        !scans_then_writes(IsolationLevel::RepeatableRead, b"b/", b"b0", b"b/2"),
        "at RepeatableRead the scanned key the transaction writes is validated as a read"
    );
    assert!(
        !scans_then_writes(IsolationLevel::DefraLevel, b"o/", b"o0", b"o/2"),
        "an ordinary key in a scanned stretch is still validated as a read"
    );
}

#[test]
fn a_commutative_prefix_and_a_block_in_one_commit_each_keep_their_rule() {
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
        for tx in [&first, &second] {
            assert_eq!(tx.scan_stream(Some(b"h/"), Some(b"h0")).count(), 2);
            tx.put(b"h/m", b"superseded").unwrap();
            tx.get_for_update(b"b/shared").unwrap();
            tx.put(b"b/shared", b"bytes").unwrap();
        }
        first.commit().unwrap();
        assert_eq!(second.commit().is_ok(), both_commit, "{level:?}");
    }
}

#[test]
fn a_merge_into_a_block_is_not_validated() {
    for (level, commits) in [
        (IsolationLevel::DefraLevel, true),
        (IsolationLevel::RepeatableRead, false),
    ] {
        let dir = tempfile::tempdir().unwrap();
        let db = open(dir.path());
        db.db().put(b"b/count", &0i64.to_be_bytes()).unwrap();
        let tx = db.begin_transaction_with(level);
        tx.get(b"b/count").unwrap();
        tx.merge(b"b/count", &1i64.to_be_bytes()).unwrap();
        db.db().merge(b"b/count", &1i64.to_be_bytes()).unwrap();
        assert_eq!(tx.commit().is_ok(), commits, "{level:?}");
    }
}

#[test]
fn a_commit_of_many_blocks_validates_none_of_them() {
    const BLOCKS: usize = 500;
    for flush in [false, true] {
        let dir = tempfile::tempdir().unwrap();
        let db = open(dir.path());
        let block = |i: usize| format!("b/{i:04}").into_bytes();
        let first = db.begin_transaction_with(IsolationLevel::DefraLevel);
        let second = db.begin_transaction_with(IsolationLevel::DefraLevel);
        let sides = [
            (&first, 0..BLOCKS, &b"first"[..]),
            (&second, BLOCKS / 2..BLOCKS * 3 / 2, &b"second"[..]),
        ];
        for (tx, range, head) in sides {
            for i in range {
                tx.get_for_update(&block(i)).unwrap();
                tx.put(&block(i), format!("content {i}").as_bytes())
                    .unwrap();
            }
            tx.put(b"head", head).unwrap();
        }
        first.commit().unwrap();
        if flush {
            db.db().flush().unwrap();
        }
        // Half the blocks are in both commits and all of them sort before
        // `head`, which is ordinary and written with different bytes: it
        // is the one conflict the second commit reports.
        assert_eq!(conflict_key(second.commit()), Some(b"head".to_vec()));

        let second = db.begin_transaction_with(IsolationLevel::DefraLevel);
        for i in BLOCKS / 2..BLOCKS * 3 / 2 {
            second
                .put(&block(i), format!("content {i}").as_bytes())
                .unwrap();
        }
        second.commit().unwrap();
        for i in 0..BLOCKS * 3 / 2 {
            assert_eq!(
                db.db().get(&block(i)).unwrap().as_deref(),
                Some(format!("content {i}").as_bytes()),
                "flush={flush} block {i}"
            );
        }
    }
}
