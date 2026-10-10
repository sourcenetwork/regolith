//! `commit_nowait` and its `CommitTicket` (plan 3.0, 3.16, 4.10; D43, D53):
//! the ticket completes on the committing transaction's own queue, a busy
//! committer is never woken, the callbacks run once on the delivering thread,
//! and dropping a ticket or a queue loses nothing.
#![cfg(not(target_arch = "wasm32"))]

use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, Wake, Waker};
use std::thread::ThreadId;

use regolith::{
    AbortReason, CommitInfo, DurabilityMode, Error, IoBudget, IoQueue, OptimisticTransactionDb,
    Options, ReadMode, TransactionDb, TransactionError, TransactionHooks, TxnOptions, WouldBlock,
};
use tempfile::TempDir;

fn open(dir: &TempDir, durability: DurabilityMode) -> OptimisticTransactionDb {
    OptimisticTransactionDb::open(dir.path(), Options::default().durability(durability)).unwrap()
}

fn on(queue: &IoQueue) -> TxnOptions {
    TxnOptions::new().io_queue(queue.id())
}

/// Counts wakes, as a `Waker`.
struct Wakes(AtomicUsize);

impl Wake for Wakes {
    fn wake(self: Arc<Self>) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }

    fn wake_by_ref(self: &Arc<Self>) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}

fn counting_waker() -> (Arc<Wakes>, Waker) {
    let wakes = Arc::new(Wakes(AtomicUsize::new(0)));
    (Arc::clone(&wakes), Waker::from(Arc::clone(&wakes)))
}

/// What ran, in order, and on which thread.
#[derive(Clone, Default)]
struct Log(Arc<Mutex<Vec<(&'static str, ThreadId)>>>);

impl Log {
    fn push(&self, what: &'static str) {
        self.0
            .lock()
            .unwrap()
            .push((what, std::thread::current().id()));
    }

    fn entries(&self) -> Vec<(&'static str, ThreadId)> {
        self.0.lock().unwrap().clone()
    }

    fn names(&self) -> Vec<&'static str> {
        self.entries().into_iter().map(|(name, _)| name).collect()
    }
}

struct Hooks(Log);

impl TransactionHooks for Hooks {
    fn on_commit(&self, _: &CommitInfo) {
        self.0.push("hook on_commit");
    }

    fn on_abort(&self, _: &AbortReason<'_>) {
        self.0.push("hook on_abort");
    }
}

#[test]
fn without_a_queue_the_commit_syncs_inline_and_the_ticket_is_ready() {
    let dir = TempDir::new().unwrap();
    let db = open(&dir, DurabilityMode::Immediate);
    let txn = db.begin(&TxnOptions::new());
    txn.put(b"k", b"v").unwrap();
    let ticket = txn.commit_nowait();
    assert!(ticket.is_ready());
    assert_eq!(db.db().get(b"k").unwrap(), Some(b"v".to_vec()));
    let mut queue = db.db().io_queue();
    let receipt = queue.block_on(ticket).unwrap();
    assert!(receipt.seq() > 0);
}

#[test]
fn at_eventual_a_commit_on_a_queue_is_ready_when_it_returns() {
    let dir = TempDir::new().unwrap();
    let db = open(&dir, DurabilityMode::Eventual);
    let queue = db.db().io_queue();
    let txn = db.begin(&on(&queue));
    txn.put(b"k", b"v").unwrap();
    let ticket = txn.commit_nowait();
    assert!(
        ticket.is_ready(),
        "at Eventual a commit is ready once applied"
    );
    assert_eq!(db.db().get(b"k").unwrap(), Some(b"v".to_vec()));
}

#[test]
fn at_immediate_a_commit_is_visible_only_once_its_queue_lands_it() {
    let dir = TempDir::new().unwrap();
    let db = open(&dir, DurabilityMode::Immediate);
    let mut queue = db.db().io_queue();
    let txn = db.begin(&on(&queue));
    txn.put(b"k", b"v").unwrap();
    let ticket = txn.commit_nowait();
    assert!(!ticket.is_ready());
    assert_eq!(
        db.db().get(b"k").unwrap(),
        None,
        "visible only after the sync"
    );
    let progress = queue.poll(IoBudget::ALL);
    assert_eq!(progress.completed, 1);
    assert!(!progress.more_pending);
    assert!(ticket.is_ready());
    assert_eq!(db.db().get(b"k").unwrap(), Some(b"v".to_vec()));
    let receipt = queue.block_on(ticket).unwrap();
    assert_eq!(receipt.seq(), db.db().latest_sequence());
}

/// Another thread's blocking write lands the group the commit left owing (it
/// helps), yet the ticket becomes ready only at its own queue's poll; another
/// queue's poll does nothing for it.
#[test]
fn a_ticket_completes_only_at_its_own_queue_poll() {
    let dir = TempDir::new().unwrap();
    let db = open(&dir, DurabilityMode::Immediate);
    let mut mine = db.db().io_queue();
    let mut other = db.db().io_queue();
    let txn = db.begin(&on(&mine));
    txn.put(b"k", b"v").unwrap();
    let ticket = txn.commit_nowait();
    std::thread::scope(|scope| {
        scope
            .spawn(|| db.db().put(b"other", b"w").unwrap())
            .join()
            .unwrap();
    });
    assert_eq!(
        db.db().get(b"k").unwrap(),
        Some(b"v".to_vec()),
        "the blocking writer landed the owed group first"
    );
    assert!(!ticket.is_ready(), "landed is not delivered");
    other.poll(IoBudget::ALL);
    assert!(
        !ticket.is_ready(),
        "another queue's poll does not deliver it"
    );
    assert_eq!(mine.poll(IoBudget::ALL).completed, 1);
    assert!(ticket.is_ready());
}

/// A task awaiting a ticket is not woken while its owner is busy, even when
/// another thread lands the group; it is woken once, by the owner's poll.
#[test]
fn a_busy_committer_is_never_woken() {
    let dir = TempDir::new().unwrap();
    let db = open(&dir, DurabilityMode::Immediate);
    let mut queue = db.db().io_queue();
    let txn = db.begin(&on(&queue));
    txn.put(b"k", b"v").unwrap();
    let mut ticket = txn.commit_nowait();
    let (wakes, waker) = counting_waker();
    let mut cx = Context::from_waker(&waker);
    assert!(Pin::new(&mut ticket).poll(&mut cx).is_pending());
    std::thread::scope(|scope| {
        scope
            .spawn(|| db.db().put(b"other", b"w").unwrap())
            .join()
            .unwrap();
    });
    assert_eq!(
        wakes.0.load(Ordering::SeqCst),
        0,
        "a busy owner is not woken"
    );
    queue.poll(IoBudget::ALL);
    assert_eq!(
        wakes.0.load(Ordering::SeqCst),
        1,
        "woken by its own poll, once"
    );
    assert!(matches!(
        Pin::new(&mut ticket).poll(&mut cx),
        Poll::Ready(Ok(_))
    ));
}

/// The transaction's callbacks, the hooks and the ticket's `on_complete` run
/// once each, in that order, on the thread whose poll delivers the outcome;
/// one registered after delivery runs at once.
#[test]
fn the_callbacks_run_once_in_order_on_the_delivering_thread() {
    let dir = TempDir::new().unwrap();
    let log = Log::default();
    let db = OptimisticTransactionDb::open(
        dir.path(),
        Options::default()
            .durability(DurabilityMode::Immediate)
            .transaction_hooks(Arc::new(Hooks(log.clone()))),
    )
    .unwrap();
    let mut queue = db.db().io_queue();
    let mut txn = db.begin(&on(&queue));
    txn.put(b"k", b"v").unwrap();
    let seen = log.clone();
    txn.on_commit(move |_| seen.push("on_commit"));
    let seen = log.clone();
    txn.on_abort(move |_| seen.push("on_abort"));
    let ticket = txn.commit_nowait();
    let seen = log.clone();
    ticket.on_complete(move |outcome| {
        assert!(outcome.is_ok());
        seen.push("on_complete");
    });
    assert!(log.names().is_empty(), "nothing runs before delivery");
    let owner = std::thread::current().id();
    queue.poll(IoBudget::ALL);
    assert_eq!(
        log.entries(),
        vec![
            ("on_commit", owner),
            ("hook on_commit", owner),
            ("on_complete", owner)
        ]
    );
    let seen = log.clone();
    ticket.on_complete(move |_| seen.push("late on_complete"));
    assert_eq!(log.names().last(), Some(&"late on_complete"));
    assert_eq!(log.names().len(), 4);
}

#[test]
fn a_conflict_comes_through_the_ticket_and_runs_on_abort() {
    let dir = TempDir::new().unwrap();
    let db = open(&dir, DurabilityMode::Immediate);
    let mut queue = db.db().io_queue();
    let first = db.begin(&on(&queue));
    let mut second = db.begin(&on(&queue));
    first.put(b"k", b"first").unwrap();
    second.put(b"k", b"second").unwrap();
    let aborted = Arc::new(AtomicUsize::new(0));
    let count = Arc::clone(&aborted);
    second.on_abort(move |reason| {
        assert!(matches!(reason, AbortReason::Conflict(_)));
        count.fetch_add(1, Ordering::SeqCst);
    });
    let won = first.commit_nowait();
    let lost = second.commit_nowait();
    queue.poll(IoBudget::ALL);
    assert!(queue.block_on(won).is_ok());
    assert!(matches!(
        queue.block_on(lost),
        Err(TransactionError::Conflict(_))
    ));
    assert_eq!(aborted.load(Ordering::SeqCst), 1);
    assert_eq!(db.db().get(b"k").unwrap(), Some(b"first".to_vec()));
}

#[test]
fn dropping_a_ticket_never_cancels_the_commit() {
    let dir = TempDir::new().unwrap();
    let db = open(&dir, DurabilityMode::Immediate);
    let mut queue = db.db().io_queue();
    let mut txn = db.begin(&on(&queue));
    txn.put(b"k", b"v").unwrap();
    let committed = Arc::new(AtomicUsize::new(0));
    let count = Arc::clone(&committed);
    txn.on_commit(move |_| {
        count.fetch_add(1, Ordering::SeqCst);
    });
    drop(txn.commit_nowait());
    queue.poll(IoBudget::ALL);
    assert_eq!(committed.load(Ordering::SeqCst), 1);
    assert_eq!(db.db().get(b"k").unwrap(), Some(b"v".to_vec()));
}

/// A queue dropped while it still holds a ticket lands the group (no thread
/// ran it yet) and delivers the ticket on the dropping thread.
#[test]
fn dropping_the_queue_delivers_its_tickets_on_the_dropping_thread() {
    let dir = TempDir::new().unwrap();
    let db = open(&dir, DurabilityMode::Immediate);
    let queue = db.db().io_queue();
    let mut txn = db.begin(&on(&queue));
    txn.put(b"k", b"v").unwrap();
    let log = Log::default();
    let seen = log.clone();
    txn.on_commit(move |_| seen.push("on_commit"));
    let ticket = txn.commit_nowait();
    let seen = log.clone();
    ticket.on_complete(move |_| seen.push("on_complete"));
    let dropper = std::thread::spawn(move || {
        drop(queue);
        std::thread::current().id()
    })
    .join()
    .unwrap();
    assert!(ticket.is_ready());
    assert_eq!(
        log.entries(),
        vec![("on_commit", dropper), ("on_complete", dropper)]
    );
    assert_eq!(db.db().get(b"k").unwrap(), Some(b"v".to_vec()));
}

#[test]
fn a_queue_not_open_on_the_database_ends_the_commit() {
    let dir = TempDir::new().unwrap();
    let db = open(&dir, DurabilityMode::Immediate);
    let gone = db.db().io_queue().id();
    let mut txn = db.begin(&TxnOptions::new().io_queue(gone));
    txn.put(b"k", b"v").unwrap();
    let aborted = Arc::new(AtomicUsize::new(0));
    let count = Arc::clone(&aborted);
    txn.on_abort(move |_| {
        count.fetch_add(1, Ordering::SeqCst);
    });
    let ticket = txn.commit_nowait();
    assert!(ticket.is_ready());
    let mut queue = db.db().io_queue();
    assert!(matches!(
        queue.block_on(ticket),
        Err(TransactionError::Engine(Error::InvalidArgument(_)))
    ));
    assert_eq!(aborted.load(Ordering::SeqCst), 1);
    assert_eq!(db.db().get(b"k").unwrap(), None);
}

/// A bare `commit_nowait` on a `CacheOnly` transaction whose `before_commit`
/// read misses the cache resolves its ticket with that wait, and the
/// transaction's `on_abort` callbacks run.
#[test]
fn a_prepare_that_would_block_resolves_the_ticket_with_its_wait() {
    let dir = TempDir::new().unwrap();
    let options = || Options::default().block_size(256);
    {
        let db = OptimisticTransactionDb::open(dir.path(), options()).unwrap();
        for i in 0..2_000u32 {
            db.db().put(format!("k{i:05}").as_bytes(), b"x").unwrap();
        }
        db.db().flush().unwrap();
        db.db().close().unwrap();
    }
    let db =
        OptimisticTransactionDb::open(dir.path(), options().durability(DurabilityMode::Immediate))
            .unwrap();
    let mut queue = db.db().io_queue();
    let mut txn = db.begin(&TxnOptions::new().read_mode(ReadMode::CacheOnly(queue.id())));
    txn.put(b"k", b"v").unwrap();
    txn.before_commit(|txn| txn.get(b"k01000").map(|_| ()));
    let aborted = Arc::new(AtomicUsize::new(0));
    let count = Arc::clone(&aborted);
    txn.on_abort(move |reason| {
        assert!(matches!(
            reason,
            AbortReason::Error(TransactionError::WouldBlock(WouldBlock::Io(_)))
        ));
        count.fetch_add(1, Ordering::SeqCst);
    });
    let ticket = txn.commit_nowait();
    assert!(ticket.is_ready());
    assert!(matches!(
        queue.block_on(ticket),
        Err(TransactionError::WouldBlock(WouldBlock::Io(_)))
    ));
    assert_eq!(aborted.load(Ordering::SeqCst), 1);
    assert_eq!(db.db().get(b"k").unwrap(), None);
}

/// A pessimistic commit keeps its key locks until its outcome is delivered,
/// so a second transaction cannot lock the key and read past a commit that is
/// written but not yet visible.
#[test]
fn a_pessimistic_nowait_commit_holds_its_locks_until_delivered() {
    let dir = TempDir::new().unwrap();
    let db = TransactionDb::open(
        dir.path(),
        Options::default().durability(DurabilityMode::Immediate),
    )
    .unwrap()
    .with_lock_timeout(std::time::Duration::from_millis(20));
    let mut queue = db.db().io_queue();
    let txn = db.begin(&on(&queue));
    txn.get_for_update(b"k").unwrap();
    txn.put(b"k", b"v").unwrap();
    let ticket = txn.commit_nowait();
    let rival = db.begin(&TxnOptions::new());
    assert!(matches!(
        rival.get_for_update(b"k"),
        Err(TransactionError::Busy(_))
    ));
    queue.poll(IoBudget::ALL);
    assert!(ticket.is_ready());
    let rival = db.begin(&TxnOptions::new());
    assert_eq!(rival.get_for_update(b"k").unwrap(), Some(b"v".to_vec()));
}

/// The ticket is `Send + Sync`: its callbacks may be registered from any
/// thread, and it can be awaited on another.
#[test]
fn the_ticket_is_send_and_sync() {
    fn shared<T: Send + Sync>() {}
    shared::<regolith::CommitTicket>();
    shared::<regolith::JobTicket>();
    shared::<regolith::StallWait>();
}
