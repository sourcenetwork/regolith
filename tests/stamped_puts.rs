//! Versionstamped puts: a key or value stamped with its commit sequence.

#![cfg(not(target_arch = "wasm32"))]

use std::sync::{Arc, Barrier};
use std::thread;

use regolith::{
    IsolationLevel, MemEnv, OptimisticTransactionDb, Options, STAMP_LEN, Stamp, TransactionError,
};
use tempfile::TempDir;

const LOG: &[u8] = b"log/";

fn placeholder() -> Vec<u8> {
    [LOG, &[0u8; STAMP_LEN][..]].concat()
}

fn stamp_of(key: &[u8]) -> u64 {
    u64::from_be_bytes(key[LOG.len()..].try_into().unwrap())
}

fn log(db: &OptimisticTransactionDb) -> Vec<(Vec<u8>, Vec<u8>)> {
    db.db().scan(Some(LOG), Some(b"log0")).unwrap()
}

fn open(dir: &TempDir) -> OptimisticTransactionDb {
    OptimisticTransactionDb::open(dir.path(), Options::default()).unwrap()
}

#[test]
fn concurrent_key_stamps_under_one_prefix_never_conflict() {
    for level in [
        IsolationLevel::ReadCommitted,
        IsolationLevel::SnapshotIsolation,
        IsolationLevel::RepeatableRead,
        IsolationLevel::Serializable,
    ] {
        let dir = TempDir::new().unwrap();
        let db = Arc::new(open(&dir));
        let writers = 8;
        let begun = Arc::new(Barrier::new(writers));
        let handles: Vec<_> = (0..writers)
            .map(|i| {
                let db = db.clone();
                let begun = begun.clone();
                thread::spawn(move || {
                    let tx = db.begin_transaction_with(level);
                    tx.put(format!("doc/{i}").as_bytes(), b"v").unwrap();
                    tx.put_stamped(&placeholder(), &[i as u8], Stamp::Key(LOG.len()))
                        .unwrap();
                    begun.wait();
                    tx.commit()
                })
            })
            .collect();
        for handle in handles {
            handle
                .join()
                .unwrap()
                .unwrap_or_else(|e| panic!("{level:?}: {e}"));
        }

        let entries = log(&db);
        assert_eq!(entries.len(), writers, "{level:?}");
        let mut writers_seen: Vec<u8> = entries.iter().map(|(_, v)| v[0]).collect();
        writers_seen.sort_unstable();
        assert_eq!(
            writers_seen,
            (0..writers as u8).collect::<Vec<_>>(),
            "{level:?}"
        );
    }
}

#[test]
fn key_stamps_sort_in_commit_order() {
    let dir = TempDir::new().unwrap();
    let db = open(&dir);
    let txns: Vec<_> = (0..3u8)
        .map(|i| {
            let tx = db.begin_transaction();
            tx.put_stamped(&placeholder(), &[i], Stamp::Key(LOG.len()))
                .unwrap();
            tx
        })
        .collect();
    let mut txns: Vec<_> = txns.into_iter().map(Some).collect();
    for i in [2, 0, 1] {
        txns[i].take().unwrap().commit().unwrap();
    }

    let order: Vec<u8> = log(&db).iter().map(|(_, v)| v[0]).collect();
    assert_eq!(order, vec![2, 0, 1]);
}

#[test]
fn stamped_puts_sharing_a_placeholder_in_one_transaction_all_land() {
    let dir = TempDir::new().unwrap();
    let db = open(&dir);
    let tx = db.begin_transaction();
    for i in 0..3u8 {
        tx.put_stamped(&placeholder(), &[i], Stamp::Key(LOG.len()))
            .unwrap();
    }
    tx.commit().unwrap();

    let entries = log(&db);
    let order: Vec<u8> = entries.iter().map(|(_, v)| v[0]).collect();
    assert_eq!(order, vec![0, 1, 2], "stamps follow buffer order");
    let stamps: Vec<u64> = entries.iter().map(|(k, _)| stamp_of(k)).collect();
    assert!(stamps.windows(2).all(|w| w[0] + 1 == w[1]), "{stamps:?}");
}

#[test]
fn a_value_stamp_is_written_and_conflicts_like_any_write() {
    let dir = TempDir::new().unwrap();
    let db = open(&dir);
    let first = db.begin_transaction();
    let second = db.begin_transaction();
    for tx in [&first, &second] {
        tx.put_stamped(b"doc/x", &[0u8; STAMP_LEN], Stamp::Value(0))
            .unwrap();
    }
    first.commit().unwrap();
    assert!(matches!(
        second.commit(),
        Err(TransactionError::Conflict { .. })
    ));

    let value = db.db().get(b"doc/x").unwrap().unwrap();
    let stamp = u64::from_be_bytes(value.try_into().unwrap());
    assert!(stamp > 0);
    assert!(stamp <= db.begin_transaction().snapshot_sequence());
}

#[test]
fn a_key_and_value_stamp_in_one_transaction_carry_their_own_sequences() {
    let dir = TempDir::new().unwrap();
    let db = open(&dir);
    let tx = db.begin_transaction();
    tx.put_stamped(&placeholder(), b"d", Stamp::Key(LOG.len()))
        .unwrap();
    tx.put_stamped(b"doc/d", &[0u8; STAMP_LEN], Stamp::Value(0))
        .unwrap();
    tx.commit().unwrap();

    let row = stamp_of(&log(&db)[0].0);
    let value = db.db().get(b"doc/d").unwrap().unwrap();
    assert_eq!(u64::from_be_bytes(value.try_into().unwrap()), row + 1);
}

#[test]
fn no_commit_after_a_snapshot_is_stamped_at_or_below_it() {
    let dir = TempDir::new().unwrap();
    let db = open(&dir);
    let commit = |v: u8| {
        let tx = db.begin_transaction();
        tx.put_stamped(&placeholder(), &[v], Stamp::Key(LOG.len()))
            .unwrap();
        tx.commit().unwrap();
    };
    commit(0);
    let reader = db.begin_transaction();
    let bound = reader.snapshot_sequence();
    let before: Vec<_> = log(&db);
    assert!(before.iter().all(|(k, _)| stamp_of(k) <= bound));

    commit(1);
    let after = log(&db);
    let below: Vec<_> = after.iter().filter(|(k, _)| stamp_of(k) <= bound).collect();
    assert_eq!(below.len(), before.len());
    assert!(stamp_of(&after.last().unwrap().0) > bound);
}

#[test]
fn stamped_keys_survive_wal_replay_byte_for_byte() {
    let env = Arc::new(MemEnv::new());
    let opts = || Options {
        env: env.clone(),
        max_background_compactions: 0,
        ..Options::default()
    };
    let before = {
        let db = OptimisticTransactionDb::open("/stamped", opts()).unwrap();
        for i in 0..5u8 {
            let tx = db.begin_transaction();
            tx.put_stamped(&placeholder(), &[i], Stamp::Key(LOG.len()))
                .unwrap();
            tx.commit().unwrap();
        }
        let before = log(&db);
        drop(db);
        before
    };

    let db = OptimisticTransactionDb::open("/stamped", opts()).unwrap();
    assert_eq!(log(&db), before);

    let tx = db.begin_transaction();
    tx.put_stamped(&placeholder(), b"x", Stamp::Key(LOG.len()))
        .unwrap();
    tx.commit().unwrap();
    let last = stamp_of(&log(&db).last().unwrap().0);
    assert!(last > stamp_of(&before.last().unwrap().0));
}

#[test]
fn a_stamp_that_does_not_fit_is_refused_when_buffered() {
    let dir = TempDir::new().unwrap();
    let db = open(&dir);
    let tx = db.begin_transaction();
    for (key, value, at) in [
        (&b"short"[..], &b""[..], Stamp::Key(0)),
        (&placeholder()[..], &b""[..], Stamp::Key(LOG.len() + 1)),
        (&b"k"[..], &[0u8; STAMP_LEN - 1][..], Stamp::Value(0)),
        (&b"k"[..], &[0u8; STAMP_LEN][..], Stamp::Value(usize::MAX)),
    ] {
        match tx.put_stamped(key, value, at) {
            Err(TransactionError::Io(e)) => {
                assert_eq!(e.kind(), std::io::ErrorKind::InvalidInput, "{at:?}")
            }
            other => panic!("{at:?}: expected InvalidInput, got {other:?}"),
        }
    }
    tx.commit().unwrap();
    assert!(log(&db).is_empty());
}

#[test]
fn a_savepoint_rollback_discards_stamped_puts() {
    let dir = TempDir::new().unwrap();
    let db = open(&dir);
    let mut tx = db.begin_transaction();
    tx.put_stamped(&placeholder(), b"kept", Stamp::Key(LOG.len()))
        .unwrap();
    tx.set_savepoint();
    tx.put_stamped(&placeholder(), b"dropped", Stamp::Key(LOG.len()))
        .unwrap();
    tx.rollback_to_savepoint().unwrap();
    tx.commit().unwrap();

    let values: Vec<Vec<u8>> = log(&db).into_iter().map(|(_, v)| v).collect();
    assert_eq!(values, vec![b"kept".to_vec()]);
}
