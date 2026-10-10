//! The `close` contract (plan 3.0): close resolves every ticket the final
//! sync covers, delivers `Closed` to every queue with a pending unit, runs
//! the `on_abort` callbacks of transactions still open on the closing
//! thread, then joins regolith's threads.
#![cfg(not(target_arch = "wasm32"))]

mod common;

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread::ThreadId;

use common::device_env::cold_db;
use regolith::{
    AbortReason, Db, DurabilityMode, Error, IoBudget, OptimisticTransactionDb, Options, ReadMode,
    TransactionError, TxnOptions, WouldBlock,
};
use tempfile::TempDir;

/// A commit whose group still owed its fsync when close began is resolved
/// by close: it committed, its ticket says so at the queue's next poll, and
/// the commit survives a reopen.
#[test]
fn close_resolves_every_ticket_the_final_sync_covers() {
    let dir = TempDir::new().unwrap();
    {
        let db = OptimisticTransactionDb::open(
            dir.path(),
            Options::default().durability(DurabilityMode::Immediate),
        )
        .unwrap();
        let mut queue = db.db().io_queue();
        let txn = db.begin(&TxnOptions::new().io_queue(queue.id()));
        txn.put(b"k", b"v").unwrap();
        let ticket = txn.commit_nowait();
        assert!(!ticket.is_ready());
        db.db().close().unwrap();
        queue.poll(IoBudget::ALL);
        assert!(ticket.is_ready());
        let receipt = queue.block_on(ticket).expect("the final sync covered it");
        assert!(receipt.seq() > 0);
    }
    let db = Db::open(dir.path(), Options::default()).unwrap();
    assert_eq!(db.get(b"k").unwrap(), Some(b"v".to_vec()));
}

/// Every queue with a pending unit is told at close: a read's wait, after
/// which the read answers `Closed`; a foreground job's ticket, which fails
/// with `Closed`; a stalled write's wait.
#[test]
fn close_delivers_closed_to_every_queue_with_a_pending_unit() {
    let (_dir, db, _device) = cold_db(
        |env| {
            Options::default()
                .env(env)
                .block_size(256)
                .max_background_compactions(0)
        },
        |db| {
            for i in 0..2_000u32 {
                db.put(format!("k{i:05}").as_bytes(), b"value").unwrap();
            }
        },
    );
    let mut queue = db.io_queue();
    let snapshot = db
        .snapshot()
        .with_read_mode(ReadMode::CacheOnly(queue.id()));
    let read = match snapshot.get(b"k01000") {
        Err(Error::WouldBlock(WouldBlock::Io(wait))) => wait,
        other => panic!("a cold read must miss, got {other:?}"),
    };
    let job = db.compact_range(None, None);
    assert!(!read.is_ready() && !job.is_ready());

    db.close().unwrap();
    queue.poll(IoBudget::ALL);
    assert!(read.is_ready(), "the read's wait was told");
    assert!(matches!(snapshot.get(b"k01000"), Err(Error::Closed)));
    assert!(job.is_ready());
    assert!(matches!(job.wait(), Err(Error::Closed)));
}

/// A transaction still open when close begins ends there: its `on_abort`
/// callbacks run on the closing thread, with `Closed`, and its later
/// `commit_nowait` fails with `Closed` and runs nothing more.
#[test]
fn close_runs_the_on_abort_of_open_transactions_on_the_closing_thread() {
    let dir = TempDir::new().unwrap();
    let db = OptimisticTransactionDb::open(dir.path(), Options::default()).unwrap();
    let mut txn = db.begin(&TxnOptions::new());
    txn.put(b"k", b"v").unwrap();
    let ran: Arc<std::sync::Mutex<Vec<ThreadId>>> = Arc::default();
    let seen = Arc::clone(&ran);
    txn.on_abort(move |reason| {
        assert!(matches!(reason, AbortReason::Closed));
        seen.lock().unwrap().push(std::thread::current().id());
    });
    let closing_thread = std::thread::scope(|scope| {
        scope
            .spawn(|| {
                db.db().close().unwrap();
                std::thread::current().id()
            })
            .join()
            .unwrap()
    });
    assert_eq!(*ran.lock().unwrap(), vec![closing_thread]);
    let mut queue = db.db().io_queue();
    assert!(matches!(
        queue.block_on(txn.commit_nowait()),
        Err(TransactionError::Engine(Error::Closed))
    ));
    assert_eq!(ran.lock().unwrap().len(), 1, "exactly one outcome");
}

/// Close joins regolith's threads only after the rest: a foreground job the
/// worker never ran fails with `Closed`, and no job runs after close.
#[test]
fn close_settles_the_jobs_the_worker_did_not_run() {
    let dir = TempDir::new().unwrap();
    let db = Db::open(dir.path(), Options::default()).unwrap();
    db.put(b"k", b"v").unwrap();
    let ran = Arc::new(AtomicUsize::new(0));
    let tickets: Vec<_> = (0..8)
        .map(|_| {
            let ticket = db.compact_range(None, None);
            let count = Arc::clone(&ran);
            ticket.on_complete(move |_| {
                count.fetch_add(1, Ordering::SeqCst);
            });
            ticket
        })
        .collect();
    db.close().unwrap();
    for ticket in tickets {
        // Run before close, or settled with `Closed`: never left pending.
        assert!(ticket.is_ready());
        let _ = ticket.wait();
    }
    assert_eq!(ran.load(Ordering::SeqCst), 8, "every callback ran once");
    assert!(matches!(
        db.compact_range(None, None).wait(),
        Err(Error::Closed)
    ));
}
