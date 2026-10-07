//! Concurrent read-write (RW) and read-write-read (RWR) transactions, eight
//! threads each, at every isolation level: the gate the isolation work has
//! to clear before anything builds on the levels.
//!
//! Every scenario forces the interleaving it is about rather than hoping a
//! scheduler produces it. A barrier lines the threads up inside their
//! transactions, or a helper thread commits between two reads and
//! acknowledges before the second one, so each invariant is checked
//! against a history that actually contains the hazard. Where a scenario
//! also runs freely, it requires evidence that the free run overlapped.
//!
//! 1. Lost update. Eight transactions read one counter at the same value,
//!    then all commit `value + 1`. Exactly one may commit at every level and
//!    on both flavours; the rest retry, and the counter ends at exactly the
//!    number of increments.
//! 2. Snapshot sum. An auditor reads part of a set of accounts, a transfer
//!    out of a read account into an unread one commits, and the auditor
//!    reads the rest: its total is still the initial total. Then eight
//!    writers transfer freely until an audit has seen a commit land inside
//!    it, and every audit and the final state hold the total.
//! 3. Repeatable point read. Each of eight readers reads a shared key, a
//!    writer commits a new value and acknowledges, and the reader reads the
//!    key again: the same value, at every level. It then writes its own key
//!    and reads it back. The commit aborts exactly at the levels that
//!    validate a plain point read.
//! 4. Repeatable scan. Each of eight readers scans a prefix, an inserter
//!    commits a new key into it and acknowledges, and the reader scans
//!    again: the same keys, every seeded key among them. A transaction
//!    begun afterwards sees the insertion.

// Native-only. wasm-pack builds every test target for wasm32, and these use
// threads and the filesystem. The browser suite lives in tests/wasm_opfs*.rs.
#![cfg(not(target_arch = "wasm32"))]

use std::collections::BTreeSet;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc;
use std::sync::{Barrier, Mutex};
use std::thread;
use std::time::Duration;

use regolith::{
    Db, IsolationLevel, OptimisticTransactionDb, Options, Transaction, TransactionDb,
    TransactionError, TxResult,
};
use tempfile::TempDir;

/// Threads per scenario.
const THREADS: usize = 8;

/// Retry budget per transaction: bounded so a livelock fails loudly.
const MAX_ATTEMPTS: usize = 2_000;

/// How long a forced handoff may take before the test fails instead of
/// hanging.
const HANDOFF: Duration = Duration::from_secs(30);

const LEVELS: [IsolationLevel; 5] = [
    IsolationLevel::ReadCommitted,
    IsolationLevel::SnapshotIsolation,
    IsolationLevel::RepeatableRead,
    IsolationLevel::Serializable,
    IsolationLevel::DefraLevel,
];

/// Whether a plain point read is validated at commit.
fn validates_point_reads(level: IsolationLevel) -> bool {
    matches!(
        level,
        IsolationLevel::RepeatableRead | IsolationLevel::Serializable | IsolationLevel::DefraLevel
    )
}

fn encode(value: u64) -> [u8; 8] {
    value.to_le_bytes()
}

fn decode(raw: Option<Vec<u8>>) -> u64 {
    raw.map_or(0, |bytes| {
        u64::from_le_bytes(bytes.as_slice().try_into().expect("8-byte value"))
    })
}

fn retryable(result: &TxResult<()>) -> bool {
    matches!(
        result,
        Err(TransactionError::Busy(_) | TransactionError::Conflict { .. })
    )
}

/// Run `attempt` until it commits, retrying only conflicts and lock
/// timeouts. Returns how many attempts were refused.
fn commit_with_retry(what: &str, mut attempt: impl FnMut() -> TxResult<()>) -> u64 {
    for refused in 0..MAX_ATTEMPTS {
        match attempt() {
            Ok(()) => return refused as u64,
            result if retryable(&result) => thread::yield_now(),
            Err(e) => panic!("{what}: unexpected transaction error: {e}"),
        }
    }
    panic!("{what}: did not commit within {MAX_ATTEMPTS} attempts");
}

/// Sets `stop` when dropped, so background threads in a scope wind down
/// even when an assertion panics on the scope's main thread.
struct StopOnDrop<'a>(&'a AtomicBool);

impl Drop for StopOnDrop<'_> {
    fn drop(&mut self) {
        self.0.store(true, Ordering::Release);
    }
}

/// Both transaction flavours behind one interface.
trait Flavour: Sync {
    fn begin(&self, level: IsolationLevel) -> Transaction<'_>;
    fn raw(&self) -> &Db;
}

impl Flavour for OptimisticTransactionDb {
    fn begin(&self, level: IsolationLevel) -> Transaction<'_> {
        self.begin_transaction_with(level)
    }
    fn raw(&self) -> &Db {
        self.db()
    }
}

impl Flavour for TransactionDb {
    fn begin(&self, level: IsolationLevel) -> Transaction<'_> {
        self.begin_transaction_with(level)
    }
    fn raw(&self) -> &Db {
        self.db()
    }
}

fn optimistic(dir: &TempDir) -> OptimisticTransactionDb {
    OptimisticTransactionDb::open(dir.path(), Options::default()).unwrap()
}

fn pessimistic(dir: &TempDir) -> TransactionDb {
    TransactionDb::open(dir.path(), Options::default())
        .unwrap()
        .with_lock_timeout(Duration::from_millis(200))
}

// ---- 1. lost update -------------------------------------------------------

/// All readers read the counter at 0 before any of them writes, so every
/// commit after the first carries a stale read of a key it writes.
fn lost_update(db: &impl Flavour, level: IsolationLevel) {
    db.raw().put(b"counter", &encode(0)).unwrap();
    let all_read = Barrier::new(THREADS);
    let first_round_commits = AtomicU64::new(0);

    thread::scope(|scope| {
        for _ in 0..THREADS {
            scope.spawn(|| {
                let tx = db.begin(level);
                // Arrive at the barrier whatever the read did, so one failed
                // reader cannot strand the other seven; judge it after.
                let read = tx.get(b"counter");
                all_read.wait();
                let seen = decode(read.unwrap());
                assert_eq!(seen, 0, "{level:?}: every reader starts from 0");
                // A pessimistic put can time out on the winner's lock: that
                // is a lost race like a refused commit.
                let result = match tx.put(b"counter", &encode(seen + 1)) {
                    Ok(()) => tx.commit(),
                    Err(e) => {
                        drop(tx);
                        Err(e)
                    }
                };
                if result.is_ok() {
                    first_round_commits.fetch_add(1, Ordering::Relaxed);
                } else {
                    assert!(retryable(&result), "{level:?}: {result:?}");
                    // The stale write lost; increment again from a fresh read.
                    commit_with_retry("counter retry", || {
                        let tx = db.begin(level);
                        let value = decode(tx.get(b"counter")?);
                        tx.put(b"counter", &encode(value + 1))?;
                        tx.commit()
                    });
                }
            });
        }
    });

    assert_eq!(
        first_round_commits.load(Ordering::Relaxed),
        1,
        "{level:?}: of {THREADS} transactions that read the same value, exactly one may commit"
    );
    assert_eq!(
        decode(db.raw().get(b"counter").unwrap()),
        THREADS as u64,
        "{level:?}: no increment is lost"
    );
}

#[test]
fn a_stale_read_modify_write_never_commits_optimistic() {
    for level in LEVELS {
        let dir = tempfile::tempdir().unwrap();
        lost_update(&optimistic(&dir), level);
    }
}

#[test]
fn a_stale_read_modify_write_never_commits_pessimistic() {
    for level in LEVELS {
        let dir = tempfile::tempdir().unwrap();
        lost_update(&pessimistic(&dir), level);
    }
}

// ---- 2. snapshot sum ------------------------------------------------------

const ACCOUNTS: u64 = 8;
const BALANCE: u64 = 100;
const TOTAL: u64 = ACCOUNTS * BALANCE;

fn account(i: u64) -> Vec<u8> {
    format!("account/{i}").into_bytes()
}

fn transfer(db: &impl Flavour, level: IsolationLevel, from: u64, to: u64) -> TxResult<()> {
    let tx = db.begin(level);
    let a = decode(tx.get(&account(from))?);
    let b = decode(tx.get(&account(to))?);
    if a == 0 {
        return Ok(());
    }
    tx.put(&account(from), &encode(a - 1))?;
    tx.put(&account(to), &encode(b + 1))?;
    tx.commit()
}

fn audit(tx: &Transaction<'_>) -> u64 {
    (0..ACCOUNTS)
        .map(|i| decode(tx.get(&account(i)).unwrap()))
        .sum()
}

fn snapshot_sum(db: &impl Flavour, level: IsolationLevel) {
    for i in 0..ACCOUNTS {
        db.raw().put(&account(i), &encode(BALANCE)).unwrap();
    }

    // Forced: a transfer out of an account the audit already read, into
    // one it has not, commits in the middle of the audit.
    let auditor = db.begin(level);
    let first = decode(auditor.get(&account(0)).unwrap());
    commit_with_retry("forced transfer", || transfer(db, level, 0, ACCOUNTS - 1));
    let rest: u64 = (1..ACCOUNTS)
        .map(|i| decode(auditor.get(&account(i)).unwrap()))
        .sum();
    assert_eq!(
        first + rest,
        TOTAL,
        "{level:?}: an audit reads one snapshot"
    );
    drop(auditor);

    // Free: writers keep transferring until an audit has seen a commit land
    // inside it. An audit overlapped when the engine's sequence advanced
    // between just after its transaction began and its last read: a write
    // committed strictly inside it. A transfer that moves nothing writes
    // nothing, so it cannot fake one.
    let overlapped = AtomicBool::new(false);
    let stop = AtomicBool::new(false);
    thread::scope(|scope| {
        let _stop = StopOnDrop(&stop);
        for t in 0..THREADS as u64 {
            let (overlapped, stop) = (&overlapped, &stop);
            scope.spawn(move || {
                // A writer that panics stops the auditor too.
                let _stop = StopOnDrop(stop);
                let mut n = 0u64;
                while !stop.load(Ordering::Acquire)
                    && (!overlapped.load(Ordering::Acquire) || n < 50)
                {
                    let (from, to) = ((t + n) % ACCOUNTS, (t + n + 3) % ACCOUNTS);
                    commit_with_retry("transfer", || transfer(db, level, from, to));
                    n += 1;
                }
            });
        }
        let deadline = std::time::Instant::now() + HANDOFF;
        let mut audits = 0u64;
        while !overlapped.load(Ordering::Acquire) || audits < 20 {
            assert!(
                !stop.load(Ordering::Acquire) || overlapped.load(Ordering::Acquire),
                "{level:?}: the writers stopped before any audit overlapped a commit"
            );
            assert!(
                std::time::Instant::now() < deadline,
                "{level:?}: no audit overlapped a commit within {HANDOFF:?}"
            );
            let tx = db.begin(level);
            let began = db.raw().snapshot().sequence();
            assert_eq!(audit(&tx), TOTAL, "{level:?}: audit {audits}");
            if db.raw().snapshot().sequence() > began {
                overlapped.store(true, Ordering::Release);
            }
            audits += 1;
        }
    });

    let tx = db.begin(level);
    assert_eq!(audit(&tx), TOTAL, "{level:?}: final total");
}

#[test]
fn an_audit_reads_one_snapshot_while_transfers_commit_optimistic() {
    for level in LEVELS {
        let dir = tempfile::tempdir().unwrap();
        snapshot_sum(&optimistic(&dir), level);
    }
}

#[test]
fn an_audit_reads_one_snapshot_while_transfers_commit_pessimistic() {
    for level in LEVELS {
        let dir = tempfile::tempdir().unwrap();
        snapshot_sum(&pessimistic(&dir), level);
    }
}

// ---- 3 and 4. repeatable reads --------------------------------------------

/// A helper thread that commits on request and acknowledges once the commit
/// is visible: the forced write between a reader's two reads.
fn serve_commits(
    requests: mpsc::Receiver<usize>,
    acks: &[mpsc::Sender<()>],
    stop: &AtomicBool,
    mut commit: impl FnMut(usize),
) {
    while !stop.load(Ordering::Acquire) {
        match requests.recv_timeout(Duration::from_millis(50)) {
            Ok(reader) => {
                commit(reader);
                acks[reader].send(()).unwrap();
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {}
            Err(mpsc::RecvTimeoutError::Disconnected) => return,
        }
    }
}

/// Run `reader` on eight threads against one helper thread that commits
/// `write` between a reader's two reads when asked.
fn with_forced_writes<D: Flavour>(
    db: &D,
    write: impl Fn(&D, usize) + Sync,
    reader: impl Fn(usize, &dyn Fn()) + Sync,
) {
    let (request, requests) = mpsc::channel::<usize>();
    let (acks, ack_rx): (Vec<_>, Vec<_>) = (0..THREADS).map(|_| mpsc::channel::<()>()).unzip();
    let ack_rx: Vec<Mutex<mpsc::Receiver<()>>> = ack_rx.into_iter().map(Mutex::new).collect();
    let stop = AtomicBool::new(false);
    thread::scope(|scope| {
        let _stop = StopOnDrop(&stop);
        let (acks, stop, write) = (&acks, &stop, &write);
        scope.spawn(move || serve_commits(requests, acks, stop, |r| write(db, r)));
        let readers: Vec<_> = (0..THREADS)
            .map(|r| {
                let (request, ack_rx, reader) = (request.clone(), &ack_rx, &reader);
                scope.spawn(move || {
                    let force = || {
                        request.send(r).unwrap();
                        ack_rx[r]
                            .lock()
                            .unwrap()
                            .recv_timeout(HANDOFF)
                            .expect("the forced commit was acknowledged");
                    };
                    reader(r, &force);
                })
            })
            .collect();
        // Join the readers first and only then let the guard stop the
        // helper, so a reader's panic propagates instead of hanging.
        let outcomes: Vec<_> = readers.into_iter().map(|h| h.join()).collect();
        drop(_stop);
        for outcome in outcomes {
            if let Err(panic) = outcome {
                std::panic::resume_unwind(panic);
            }
        }
    });
}

fn shared(r: usize) -> Vec<u8> {
    format!("shared/{r}").into_bytes()
}

fn own(r: usize) -> Vec<u8> {
    format!("own/{r}").into_bytes()
}

#[test]
fn a_point_read_repeats_while_its_key_changes() {
    for level in LEVELS {
        let dir = tempfile::tempdir().unwrap();
        let db = optimistic(&dir);
        for r in 0..THREADS {
            db.db().put(&shared(r), &encode(1)).unwrap();
        }
        with_forced_writes(
            &db,
            |db, r| {
                let value = decode(db.db().get(&shared(r)).unwrap());
                db.db().put(&shared(r), &encode(value + 1)).unwrap();
            },
            |r, force| {
                let tx = db.begin_transaction_with(level);
                let first = decode(tx.get(&shared(r)).unwrap());
                force();
                assert_eq!(
                    decode(db.db().get(&shared(r)).unwrap()),
                    first + 1,
                    "the forced commit is visible outside the transaction"
                );
                let second = decode(tx.get(&shared(r)).unwrap());
                assert_eq!(first, second, "{level:?}: reader {r} read one snapshot");
                tx.put(&own(r), &encode(first)).unwrap();
                assert_eq!(decode(tx.get(&own(r)).unwrap()), first, "read your writes");
                let result = tx.commit();
                if validates_point_reads(level) {
                    assert!(
                        matches!(result, Err(TransactionError::Conflict { .. })),
                        "{level:?}: a validated read overtaken by a commit aborts: {result:?}"
                    );
                } else {
                    assert!(
                        result.is_ok(),
                        "{level:?}: an unvalidated read commits: {result:?}"
                    );
                }
            },
        );
    }
}

const SEEDED: usize = 4;

fn scanned(tx: &Transaction<'_>) -> BTreeSet<Vec<u8>> {
    tx.scan_stream(Some(b"row/"), Some(b"row0"))
        .map(|(key, _)| key)
        .collect()
}

#[test]
fn a_scan_repeats_while_its_range_grows() {
    for level in LEVELS {
        let dir = tempfile::tempdir().unwrap();
        let db = optimistic(&dir);
        let seeded: BTreeSet<Vec<u8>> = (0..SEEDED)
            .map(|i| format!("row/seed-{i}").into_bytes())
            .collect();
        for key in &seeded {
            db.db().put(key, b"x").unwrap();
        }
        with_forced_writes(
            &db,
            |db, r| {
                db.db()
                    .put(format!("row/new-{r}").as_bytes(), b"x")
                    .unwrap()
            },
            |r, force| {
                let tx = db.begin_transaction_with(level);
                let first = scanned(&tx);
                assert!(
                    first.is_superset(&seeded),
                    "{level:?}: reader {r} sees every seeded row"
                );
                force();
                let second = scanned(&tx);
                assert_eq!(first, second, "{level:?}: reader {r} scanned one snapshot");
                let inserted = format!("row/new-{r}").into_bytes();
                assert!(!second.contains(&inserted));
                assert!(
                    scanned(&db.begin_transaction_with(level)).contains(&inserted),
                    "{level:?}: a later transaction sees the insertion"
                );
            },
        );
    }
}
