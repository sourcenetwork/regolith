//! Optimistic transactions share commit groups (E10, `GroupCommit.tla`),
//! through the public API.
//!
//! Many threads run read-modify-write transactions over a few hot keys at
//! Immediate durability, so commits queue behind each other's fsync and
//! share groups. The history is then checked against a run of the committed
//! transactions one at a time in receipt order: every value a committed
//! transaction read through `get_for_update` is the value that run holds at
//! its turn, and the database ends where that run ends. A group that let a
//! member commit over an earlier member's write would show a read the serial
//! run contradicts (RED ViewOnly), and a lost update would show in the final
//! counters.
#![cfg(not(target_arch = "wasm32"))]

use std::collections::BTreeMap;
use std::sync::{Arc, Barrier};
use std::thread;

use regolith::{
    DurabilityMode, IsolationLevel, OptimisticTransactionDb, Options, Statistics, Ticker,
    TransactionError, TxnOptions,
};
use tempfile::TempDir;

const KEYS: usize = 6;
const THREADS: usize = 12;
const COMMITS_PER_THREAD: usize = 40;
const MAX_ATTEMPTS: usize = 10_000;

fn key(i: usize) -> Vec<u8> {
    format!("counter/{i}").into_bytes()
}

fn number(bytes: Option<Vec<u8>>) -> u64 {
    bytes.map_or(0, |b| String::from_utf8(b).unwrap().parse().unwrap())
}

/// One committed transaction: its receipt sequence, what it read, what it wrote.
struct Committed {
    seq: u64,
    reads: Vec<(usize, u64)>,
    writes: Vec<(usize, u64)>,
}

/// A small deterministic generator per thread.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

/// Run the workload once, check its history against the one-at-a-time run,
/// and return how many fsyncs its commits took.
fn run_once(isolation: IsolationLevel) -> u64 {
    let dir = TempDir::new().unwrap();
    let stats = Arc::new(Statistics::new());
    let db = Arc::new(
        OptimisticTransactionDb::open(
            dir.path(),
            Options::default()
                .durability(DurabilityMode::Immediate)
                .statistics(Some(Arc::clone(&stats))),
        )
        .unwrap(),
    );
    let barrier = Arc::new(Barrier::new(THREADS));
    let handles: Vec<_> = (0..THREADS)
        .map(|t| {
            let (db, barrier) = (Arc::clone(&db), Arc::clone(&barrier));
            thread::spawn(move || {
                let mut rng = Rng(0xC0FF_EE00 ^ t as u64);
                let mut committed = Vec::with_capacity(COMMITS_PER_THREAD);
                barrier.wait();
                for _ in 0..COMMITS_PER_THREAD {
                    let a = rng.next() as usize % KEYS;
                    let b = (a + 1 + rng.next() as usize % (KEYS - 1)) % KEYS;
                    let mut attempts = 0;
                    loop {
                        attempts += 1;
                        assert!(attempts < MAX_ATTEMPTS, "thread {t} never committed");
                        let tx = db.begin(&TxnOptions::new().isolation(isolation));
                        let va = number(tx.get_for_update(&key(a)).unwrap());
                        let vb = number(tx.get_for_update(&key(b)).unwrap());
                        // `a` takes a value derived from both reads that never
                        // repeats one of them, so every commit depends on both.
                        let next =
                            (va.wrapping_mul(31).wrapping_add(vb).wrapping_add(1)) % 1_000_000_007;
                        tx.put(&key(a), next.to_string().as_bytes()).unwrap();
                        match tx.commit() {
                            Ok(receipt) => {
                                committed.push(Committed {
                                    seq: receipt.seq(),
                                    reads: vec![(a, va), (b, vb)],
                                    writes: vec![(a, next)],
                                });
                                break;
                            }
                            Err(TransactionError::Conflict(_)) => continue,
                            Err(other) => panic!("thread {t}: {other}"),
                        }
                    }
                }
                committed
            })
        })
        .collect();
    let mut history: Vec<Committed> = handles
        .into_iter()
        .flat_map(|h| h.join().expect("a writer panicked"))
        .collect();
    history.sort_by_key(|c| c.seq);
    assert!(
        history.windows(2).all(|w| w[0].seq < w[1].seq),
        "every commit that wrote took a sequence of its own"
    );

    let mut state: BTreeMap<usize, u64> = (0..KEYS).map(|k| (k, 0)).collect();
    for (turn, commit) in history.iter().enumerate() {
        for &(k, v) in &commit.reads {
            assert_eq!(
                state[&k], v,
                "commit {turn} (seq {}) read key {k} as {v}; committing one at a time \
                 in receipt order it holds {}",
                commit.seq, state[&k]
            );
        }
        for &(k, v) in &commit.writes {
            state.insert(k, v);
        }
    }
    for (k, v) in &state {
        assert_eq!(number(db.db().get(&key(*k)).unwrap()), *v, "key {k}");
    }

    assert_eq!(
        stats.get_ticker(Ticker::CommitCount),
        (THREADS * COMMITS_PER_THREAD) as u64
    );
    stats.get_ticker(Ticker::WalSyncCount)
}

/// Every run is checked against the serial run. Sharing is a scheduling
/// outcome: on a loaded host every commit can legitimately land in a group of
/// its own, so the workload runs until a commit shares a group's fsync, and
/// fails only if none ever does.
fn run(isolation: IsolationLevel) {
    const RUNS: usize = 5;
    let commits = (THREADS * COMMITS_PER_THREAD) as u64;
    let mut fewest = u64::MAX;
    for _ in 0..RUNS {
        fewest = fewest.min(run_once(isolation));
        if fewest < commits {
            return;
        }
    }
    panic!(
        "{commits} Immediate commits by {THREADS} threads took {fewest} fsyncs at best \
         in {RUNS} runs: no commit ever shared a group"
    );
}

#[test]
fn concurrent_transactions_in_groups_equal_a_serial_run_in_commit_order() {
    run(IsolationLevel::SnapshotIsolation);
}

#[test]
fn serializable_transactions_in_groups_equal_a_serial_run_in_commit_order() {
    run(IsolationLevel::Serializable);
}
