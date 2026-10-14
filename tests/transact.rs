//! `transact`: bounded retries owned by regolith.
//!
//! The closure runs in a fresh transaction, and when its commit loses a race it
//! runs again at once with the conflict that lost. Each case races the closure
//! against a write made around it, from inside the closure, so the outcome of
//! every attempt is decided and no timing is involved.

// Native-only. wasm-pack builds every test target for wasm32, and these use
// threads and the filesystem. The browser suite lives in tests/wasm_opfs*.rs.
#![cfg(not(target_arch = "wasm32"))]

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use regolith::{
    Access, Error, OptimisticTransactionDb, Options, RetryPolicy, Statistics, Ticker,
    TransactError, TransactionDb, TransactionError, WriteKind,
};

fn open(dir: &std::path::Path) -> OptimisticTransactionDb {
    OptimisticTransactionDb::open(dir, Options::default()).unwrap()
}

#[test]
fn a_rerun_gets_the_conflict_the_previous_attempt_lost_to_and_the_receipt_comes_back() {
    let dir = tempfile::tempdir().unwrap();
    let db = open(dir.path());
    db.db().put(b"k", b"start").unwrap();

    let mut seen = Vec::new();
    let (read, receipt) = db
        .transact(&RetryPolicy::new(5), |tx, previous| {
            seen.push(previous.map(|c| (c.key().to_vec(), c.mine(), c.theirs())));
            let read = tx.get_for_update(b"k")?;
            if previous.is_none() {
                db.db().put(b"k", b"racer").unwrap();
            }
            tx.put(b"k", b"mine")?;
            Ok::<_, TransactionError>(read)
        })
        .unwrap();

    assert_eq!(
        seen,
        [
            None,
            Some((b"k".to_vec(), Access::ReadForUpdate, WriteKind::Put))
        ],
        "the first run has no conflict, the re-run has the one that lost"
    );
    assert_eq!(read, Some(b"racer".to_vec()), "the re-run sees the winner");
    assert_eq!(db.db().get(b"k").unwrap(), Some(b"mine".to_vec()));
    assert_eq!(receipt.seq(), db.db().latest_sequence());
}

#[test]
fn it_stops_at_max_attempts_and_returns_the_last_conflict() {
    let dir = tempfile::tempdir().unwrap();
    let stats = Arc::new(Statistics::new());
    let db = OptimisticTransactionDb::open(
        dir.path(),
        Options::default().statistics(Some(Arc::clone(&stats))),
    )
    .unwrap();
    db.db().put(b"k", b"start").unwrap();

    let runs = AtomicU64::new(0);
    let result = db.transact(&RetryPolicy::new(3), |tx, _| {
        let run = runs.fetch_add(1, Ordering::Relaxed);
        tx.get_for_update(b"k")?;
        db.db()
            .put(b"k", format!("racer {run}").as_bytes())
            .unwrap();
        tx.put(b"elsewhere", b"x")?;
        Ok::<_, TransactionError>(())
    });

    assert_eq!(runs.load(Ordering::Relaxed), 3);
    assert_eq!(stats.get_ticker(Ticker::CommitConflicts), 3);
    match result {
        Err(TransactError::Exhausted(conflict)) => {
            assert_eq!(conflict.key(), b"k");
            assert_eq!(
                (conflict.mine(), conflict.theirs()),
                (Access::ReadForUpdate, WriteKind::Put)
            );
        }
        other => panic!("expected the last conflict, got {other:?}"),
    }
    assert_eq!(
        db.db().get(b"elsewhere").unwrap(),
        None,
        "nothing committed"
    );
}

#[test]
fn zero_attempts_still_runs_the_closure_once() {
    assert_eq!(RetryPolicy::new(0).max_attempts(), 1);
    assert!(
        RetryPolicy::default().max_attempts() > 1,
        "a default that never retries would defeat transact"
    );

    let dir = tempfile::tempdir().unwrap();
    let db = open(dir.path());
    db.db().put(b"k", b"start").unwrap();
    let runs = AtomicU64::new(0);
    let result = db.transact(&RetryPolicy::new(0), |tx, _| {
        runs.fetch_add(1, Ordering::Relaxed);
        tx.get_for_update(b"k")?;
        db.db().put(b"k", b"racer").unwrap();
        tx.put(b"elsewhere", b"x")?;
        Ok::<_, TransactionError>(())
    });
    assert_eq!(runs.load(Ordering::Relaxed), 1);
    assert!(
        matches!(result, Err(TransactError::Exhausted(_))),
        "{result:?}"
    );
}

#[test]
fn an_error_from_the_closure_ends_the_attempt_without_a_retry() {
    let dir = tempfile::tempdir().unwrap();
    let db = open(dir.path());

    let runs = AtomicU64::new(0);
    let result = db.transact(&RetryPolicy::new(5), |tx, _| {
        runs.fetch_add(1, Ordering::Relaxed);
        tx.put(b"written", b"x").unwrap();
        Err::<(), _>("boom")
    });
    assert_eq!(runs.load(Ordering::Relaxed), 1);
    match result {
        Err(TransactError::Closure("boom")) => {}
        other => panic!("expected the closure's error, got {other:?}"),
    }
    assert_eq!(
        db.db().get(b"written").unwrap(),
        None,
        "the attempt was rolled back"
    );
}

#[test]
fn the_closure_can_settle_the_race_from_the_conflict() {
    #[derive(Debug, PartialEq, Eq)]
    struct AlreadyDeleted;

    let dir = tempfile::tempdir().unwrap();
    let db = open(dir.path());
    db.db().put(b"doc", b"body").unwrap();

    let mut reasons = Vec::new();
    let result = db.transact(&RetryPolicy::new(5), |tx, previous| {
        reasons.push(previous.map(|c| c.theirs()));
        if tx.get_for_update(b"doc").unwrap().is_none() {
            return Err(AlreadyDeleted);
        }
        if previous.is_none() {
            db.db().delete(b"doc").unwrap();
        }
        tx.delete(b"doc").unwrap();
        Ok(())
    });

    assert_eq!(reasons, [None, Some(WriteKind::Delete)]);
    match result {
        Err(TransactError::Closure(AlreadyDeleted)) => {}
        other => panic!("expected the closure to see the delete, got {other:?}"),
    }
}

#[test]
fn a_commit_that_fails_for_another_reason_is_not_retried() {
    let dir = tempfile::tempdir().unwrap();
    let db =
        OptimisticTransactionDb::open(dir.path(), Options::default().max_value_size(8)).unwrap();

    let runs = AtomicU64::new(0);
    let result = db.transact(&RetryPolicy::new(5), |tx, _| {
        runs.fetch_add(1, Ordering::Relaxed);
        tx.put(b"k", &[0; 64])?;
        Ok::<_, TransactionError>(())
    });
    assert_eq!(runs.load(Ordering::Relaxed), 1);
    assert!(
        matches!(
            result,
            Err(TransactError::Engine(TransactionError::Engine(
                Error::InvalidArgument(_)
            )))
        ),
        "{result:?}"
    );
}

#[test]
fn the_error_prints_the_closures_message_or_the_conflict_without_the_key() {
    fn assert_error<E: std::error::Error + 'static>() {}
    assert_error::<TransactError<std::io::Error>>();

    let closure: TransactError<String> = TransactError::Closure("boom".to_string());
    assert_eq!(closure.to_string(), "boom");

    let dir = tempfile::tempdir().unwrap();
    let db = open(dir.path());
    db.db().put(b"SECRET-key", b"start").unwrap();
    let result = db.transact(&RetryPolicy::new(1), |tx, _| {
        tx.get_for_update(b"SECRET-key")?;
        db.db().put(b"SECRET-key", b"racer").unwrap();
        tx.put(b"elsewhere", b"x")?;
        Ok::<_, TransactionError>(())
    });
    let err = result.unwrap_err();
    for text in [err.to_string(), format!("{err:?}")] {
        assert!(!text.contains("SECRET"), "{text}");
    }
    assert!(err.to_string().contains("10-byte key"), "{err}");
}

#[test]
fn eight_threads_of_transacted_increments_lose_none() {
    const THREADS: u64 = 8;
    const PER_THREAD: u64 = 50;

    let dir = tempfile::tempdir().unwrap();
    let db = open(dir.path());
    db.db().put(b"counter", &0u64.to_le_bytes()).unwrap();

    std::thread::scope(|scope| {
        for _ in 0..THREADS {
            scope.spawn(|| {
                for _ in 0..PER_THREAD {
                    db.transact(&RetryPolicy::new(1_000), |tx, _| {
                        let raw = tx.get_for_update(b"counter")?.unwrap();
                        let current = u64::from_le_bytes(raw.as_slice().try_into().unwrap());
                        tx.put(b"counter", &(current + 1).to_le_bytes())?;
                        Ok::<_, TransactionError>(())
                    })
                    .expect("a one-winner race resolves within the policy");
                }
            });
        }
    });

    let raw = db.db().get(b"counter").unwrap().unwrap();
    assert_eq!(
        u64::from_le_bytes(raw.as_slice().try_into().unwrap()),
        THREADS * PER_THREAD
    );
}

#[test]
fn a_pessimistic_database_transacts_the_same_way() {
    let dir = tempfile::tempdir().unwrap();
    let db = TransactionDb::open(dir.path(), Options::default()).unwrap();
    db.db().put(b"k", b"start").unwrap();

    let mut previous_seen = Vec::new();
    let (read, receipt) = db
        .transact(&RetryPolicy::default(), |tx, previous| {
            previous_seen.push(previous.map(|c| (c.mine(), c.theirs())));
            let read = tx.get_for_update(b"k")?;
            if previous.is_none() {
                // Around the lock manager, so the commit's check catches it.
                db.db().put(b"k", b"racer").unwrap();
            }
            tx.put(b"k", b"mine")?;
            Ok::<_, TransactionError>(read)
        })
        .unwrap();

    assert_eq!(
        previous_seen,
        [None, Some((Access::ReadForUpdate, WriteKind::Put))]
    );
    assert_eq!(read, Some(b"racer".to_vec()));
    assert_eq!(db.db().get(b"k").unwrap(), Some(b"mine".to_vec()));
    assert_eq!(receipt.seq(), db.db().latest_sequence());
}
