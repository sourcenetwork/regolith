//! `transact_async` (plan 3.10, D39): an attempt that misses the cache is
//! suspended on its wait, not ended; the commit goes through `commit_nowait`;
//! a conflict re-runs the closure with its reason, up to the policy's bound.
#![cfg(not(target_arch = "wasm32"))]

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use regolith::{
    DurabilityMode, OptimisticTransactionDb, Options, RetryPolicy, TransactError, TransactionDb,
    TxnOptions, ready,
};
use tempfile::TempDir;

const KEYS: u32 = 2_000;

fn key(i: u32) -> Vec<u8> {
    format!("k{i:05}").into_bytes()
}

/// A database whose keys all live in tables, reopened with a cold cache.
fn cold(dir: &TempDir) -> OptimisticTransactionDb {
    let options = || Options::default().block_size(256);
    {
        let db = OptimisticTransactionDb::open(dir.path(), options()).unwrap();
        for i in 0..KEYS {
            db.db()
                .put(&key(i), format!("value-{i}").as_bytes())
                .unwrap();
        }
        db.db().flush().unwrap();
        db.db().close().unwrap();
    }
    OptimisticTransactionDb::open(dir.path(), options().durability(DurabilityMode::Immediate))
        .unwrap()
}

/// Reads that miss suspend the attempt on their waits; the closure runs once,
/// keeps what it did before each miss, and its commit lands through the
/// queue.
#[test]
fn misses_suspend_the_attempt_instead_of_ending_it() {
    let dir = TempDir::new().unwrap();
    let db = cold(&dir);
    let mut queue = db.db().io_queue();
    let runs = AtomicUsize::new(0);
    let reads = AtomicUsize::new(0);
    let (sum, receipt) = queue
        .block_on(db.transact_async(
            queue.id(),
            &RetryPolicy::default(),
            async |txn, previous| {
                assert!(previous.is_none());
                runs.fetch_add(1, Ordering::SeqCst);
                let mut sum = Vec::new();
                for i in [100u32, 900, 1_700] {
                    let value = ready(|| {
                        reads.fetch_add(1, Ordering::SeqCst);
                        txn.get(&key(i))
                    })
                    .await?;
                    sum.extend(value.expect("the key exists"));
                }
                txn.put(b"sum", &sum)?;
                Ok::<_, regolith::TransactionError>(sum)
            },
        ))
        .unwrap();
    assert_eq!(
        runs.load(Ordering::SeqCst),
        1,
        "a miss never ends the attempt"
    );
    assert!(
        reads.load(Ordering::SeqCst) > 3,
        "at least one read missed and ran again"
    );
    assert_eq!(db.db().get(b"sum").unwrap(), Some(sum));
    assert!(receipt.seq() > 0);
}

/// A conflict re-runs the closure in a fresh transaction, handing it the
/// conflict; the re-run sees the winner and commits.
#[test]
fn a_conflict_reruns_the_closure_with_its_reason() {
    let dir = TempDir::new().unwrap();
    let db = cold(&dir);
    let mut queue = db.db().io_queue();
    let runs = AtomicUsize::new(0);
    let reasons = Arc::new(std::sync::Mutex::new(Vec::new()));
    let (seen, _) = queue
        .block_on(
            db.transact_async(queue.id(), &RetryPolicy::new(3), async |txn, previous| {
                reasons
                    .lock()
                    .unwrap()
                    .push(previous.map(|c| c.key().to_vec()));
                let run = runs.fetch_add(1, Ordering::SeqCst);
                let value = ready(|| txn.get_for_update(&key(5))).await?;
                if run == 0 {
                    // A rival commits the same key between the read and the
                    // commit: this attempt loses.
                    db.db().put(&key(5), b"rival").unwrap();
                }
                txn.put(&key(5), b"mine")?;
                Ok::<_, regolith::TransactionError>(value)
            }),
        )
        .unwrap();
    assert_eq!(runs.load(Ordering::SeqCst), 2);
    assert_eq!(seen, Some(b"rival".to_vec()), "the re-run sees the winner");
    assert_eq!(*reasons.lock().unwrap(), vec![None, Some(key(5))]);
    assert_eq!(db.db().get(&key(5)).unwrap(), Some(b"mine".to_vec()));
}

#[test]
fn the_policy_bounds_the_reruns() {
    let dir = TempDir::new().unwrap();
    let db = cold(&dir);
    let mut queue = db.db().io_queue();
    let runs = AtomicUsize::new(0);
    let outcome =
        queue.block_on(
            db.transact_async(queue.id(), &RetryPolicy::new(2), async |txn, _| {
                runs.fetch_add(1, Ordering::SeqCst);
                ready(|| txn.get_for_update(&key(7))).await?;
                db.db().put(&key(7), b"rival").unwrap();
                txn.put(&key(7), b"mine")?;
                Ok::<_, regolith::TransactionError>(())
            }),
        );
    assert!(matches!(outcome, Err(TransactError::Exhausted(_))));
    assert_eq!(runs.load(Ordering::SeqCst), 2);
}

#[test]
fn an_error_from_the_closure_ends_the_attempt_unretried() {
    let dir = TempDir::new().unwrap();
    let db = cold(&dir);
    let mut queue = db.db().io_queue();
    let runs = AtomicUsize::new(0);
    let outcome =
        queue.block_on(
            db.transact_async(queue.id(), &RetryPolicy::default(), async |txn, _| {
                runs.fetch_add(1, Ordering::SeqCst);
                txn.put(b"k", b"v").map_err(|_| "put")?;
                Err::<(), _>("business rule")
            }),
        );
    assert!(matches!(
        outcome,
        Err(TransactError::Closure("business rule"))
    ));
    assert_eq!(runs.load(Ordering::SeqCst), 1);
    assert_eq!(db.db().get(b"k").unwrap(), None);
}

/// `before_commit` callbacks whose reads miss are prepared by the attempt,
/// which waits out each miss instead of failing the commit.
#[test]
fn a_before_commit_read_that_misses_is_waited_out() {
    let dir = TempDir::new().unwrap();
    let db = cold(&dir);
    let mut queue = db.db().io_queue();
    let calls = Arc::new(AtomicUsize::new(0));
    let counted = Arc::clone(&calls);
    queue
        .block_on(
            db.transact_async(queue.id(), &RetryPolicy::default(), async move |txn, _| {
                let counted = Arc::clone(&counted);
                txn.before_commit(move |txn| {
                    counted.fetch_add(1, Ordering::SeqCst);
                    let value = txn.get(&key(1_234))?.expect("the key exists");
                    txn.put(b"copy", &value)
                });
                txn.put(b"k", b"v")?;
                Ok::<_, regolith::TransactionError>(())
            }),
        )
        .unwrap();
    assert!(
        calls.load(Ordering::SeqCst) >= 2,
        "the callback missed, waited, and ran again"
    );
    assert_eq!(db.db().get(b"copy").unwrap(), Some(b"value-1234".to_vec()));
}

#[test]
fn a_pessimistic_database_runs_the_same_contract() {
    let dir = TempDir::new().unwrap();
    drop(cold(&dir));
    let db = TransactionDb::open(
        dir.path(),
        Options::default()
            .block_size(256)
            .durability(DurabilityMode::Immediate),
    )
    .unwrap();
    let mut queue = db.db().io_queue();
    let (value, _) = queue
        .block_on(
            db.transact_async(queue.id(), &RetryPolicy::default(), async |txn, _| {
                let value = ready(|| txn.get_for_update(&key(42))).await?;
                txn.put(b"copy", value.as_deref().unwrap_or_default())?;
                Ok::<_, regolith::TransactionError>(value)
            }),
        )
        .unwrap();
    assert_eq!(value, Some(b"value-42".to_vec()));
    assert_eq!(db.db().get(b"copy").unwrap(), Some(b"value-42".to_vec()));
    let _ = TxnOptions::new();
}
