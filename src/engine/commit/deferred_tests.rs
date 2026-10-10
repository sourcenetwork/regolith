//! A group's fsync as one claimable unit (`deferred.rs`, D53).
//!
//! Groups are built by hand, ticket by ticket, so which members share a group
//! is fixed rather than left to timing; each member's queue is a real
//! `IoQueue`, polled by its owner.

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering as Counting};
use std::sync::{Barrier, Mutex as StdMutex};
use std::thread::ThreadId;

use tempfile::TempDir;

use super::super::io::job::Delivery;
use super::super::wal::{fault, ops_record_len};
use super::super::{EngineOptions, ValidationSet, grouped_batch_ops};
use super::early::EarlyVerdict;
use super::*;
use crate::column_family::{DEFAULT_CF_ID, prefix_key};
use crate::{IoBudget, IoQueue, PerfLevel};

fn open() -> (
    TempDir,
    Arc<RegolithEngine>,
    Arc<crate::statistics::Statistics>,
) {
    let dir = TempDir::new().unwrap();
    let stats = Arc::new(crate::statistics::Statistics::new());
    let engine = RegolithEngine::open(
        dir.path(),
        EngineOptions {
            statistics: Some(Arc::clone(&stats)),
            ..EngineOptions::default()
        },
    )
    .unwrap();
    (dir, engine, stats)
}

fn key_of(name: &[u8]) -> Vec<u8> {
    prefix_key(DEFAULT_CF_ID, name)
}

fn read_now(engine: &RegolithEngine, name: &[u8]) -> Option<Vec<u8>> {
    engine.get(&key_of(name), engine.snapshot_seq()).unwrap()
}

/// A transaction's commit that puts `name`, as `commit_nowait` hands it over
/// when `nowait`, or as `commit` does.
fn txn_put(
    engine: &RegolithEngine,
    name: &[u8],
    durability: DurabilityMode,
    nowait: bool,
) -> WriteRequest {
    let snapshot = engine.snapshot_seq();
    let ops = grouped_batch_ops(
        BTreeMap::from([(key_of(name), Some(b"v".to_vec()))]),
        Vec::new(),
        Vec::new(),
    );
    let checks = ValidationSet {
        reads: Vec::new(),
        writes_at: Some(snapshot),
        blind_merges_commute: false,
        exempt: Vec::new(),
        ranges: Vec::new(),
    };
    let early = match engine.check_early(&checks, &ops).unwrap() {
        EarlyVerdict::Marks(early) => early,
        EarlyVerdict::Conflict(conflict) => panic!("no conflict expected: {conflict:?}"),
    };
    WriteRequest::Txn(TxnRequest {
        checks,
        record_bound: ops_record_len(&ops),
        cost_bound: ops.iter().map(batch_op_memtable_cost).sum(),
        ops,
        appends: Vec::new(),
        durability,
        perf: PerfLevel::Disable,
        early,
        nowait,
    })
}

/// Run `requests` as one group, in order, and return what each learned.
fn run_group(engine: &RegolithEngine, requests: Vec<WriteRequest>) -> Vec<io::Result<Settled>> {
    let slots: Vec<Arc<WriteSlot>> = requests
        .into_iter()
        .map(|request| {
            let slot = Arc::new(WriteSlot::new());
            slot.arm(request).expect("a fresh slot arms");
            slot
        })
        .collect();
    let mut pipe = engine.pipeline.lock();
    pipe.group.clear();
    for slot in &slots {
        let request = slot.take_request();
        pipe.group
            .push(GroupTicket::new(Some(Arc::clone(slot)), request));
    }
    assert!(
        engine
            .run_and_complete(&mut pipe, engine.view.load())
            .is_none()
    );
    drop(pipe);
    slots.iter().map(|slot| slot.finish_settled()).collect()
}

fn pending(settled: &io::Result<Settled>) -> (Arc<GroupSync>, usize) {
    match settled {
        Ok(Settled::Pending { group, member }) => (Arc::clone(group), *member),
        other => panic!("expected a pending member, got {other:?}"),
    }
}

/// Counts how often it is told, and on which threads.
#[derive(Default)]
struct Told {
    count: AtomicUsize,
    threads: StdMutex<Vec<ThreadId>>,
}

impl Delivery for Told {
    fn deliver(&self) {
        self.count.fetch_add(1, Counting::SeqCst);
        self.threads
            .lock()
            .unwrap()
            .push(std::thread::current().id());
    }
}

fn wait_on(engine: &RegolithEngine, queue: &IoQueue, group: &GroupSync) -> Arc<Told> {
    let told = Arc::new(Told::default());
    let shared = engine.io().queue(queue.id()).expect("the queue is open");
    assert!(engine.io().wait_on(
        &shared,
        Arc::clone(group.job()),
        Some(Arc::clone(&told) as Arc<dyn Delivery>)
    ));
    told
}

/// Nothing of a group owing its fsync is visible; the first member queue to
/// poll lands it, and the others are told without a second sync.
#[test]
fn the_first_member_to_poll_lands_the_group_and_the_rest_are_told() {
    let (_dir, engine, stats) = open();
    let horizon = engine.snapshot_seq();
    let settled = run_group(
        &engine,
        vec![
            txn_put(&engine, b"a", DurabilityMode::Immediate, true),
            txn_put(&engine, b"b", DurabilityMode::Immediate, true),
            txn_put(&engine, b"c", DurabilityMode::Immediate, true),
        ],
    );
    let (group, _) = pending(&settled[0]);
    for member in &settled {
        assert!(
            Arc::ptr_eq(&pending(member).0, &group),
            "one unit per group"
        );
    }
    assert!(!group.is_landed());
    assert_eq!(
        engine.snapshot_seq(),
        horizon,
        "nothing visible before the sync"
    );
    assert_eq!(read_now(&engine, b"a"), None);
    assert_eq!(stats.get_ticker(Ticker::WalSyncCount), 0);

    let mut queues: Vec<IoQueue> = (0..3).map(|_| engine.io_queue()).collect();
    let told: Vec<Arc<Told>> = queues
        .iter()
        .map(|queue| wait_on(&engine, queue, &group))
        .collect();

    // Only the second member's owner polls: it runs the sync itself.
    let progress = queues[1].poll(IoBudget::ALL);
    assert_eq!(progress.completed, 1);
    assert!(group.is_landed());
    assert_eq!(stats.get_ticker(Ticker::WalSyncCount), 1);
    assert_eq!(read_now(&engine, b"a"), Some(b"v".to_vec()));
    assert_eq!(read_now(&engine, b"c"), Some(b"v".to_vec()));
    assert_eq!(told[1].count.load(Counting::SeqCst), 1);
    assert_eq!(
        told[0].count.load(Counting::SeqCst),
        0,
        "told only at its own poll"
    );

    for (queue, told) in queues.iter_mut().zip(&told) {
        queue.poll(IoBudget::ALL);
        assert_eq!(told.count.load(Counting::SeqCst), 1);
    }
    assert_eq!(
        stats.get_ticker(Ticker::WalSyncCount),
        1,
        "one sync for the group"
    );
    for (member, settled) in settled.iter().enumerate() {
        let (group, at) = pending(settled);
        assert_eq!(at, member);
        assert!(matches!(
            group.take(at),
            Some(Ok(Settled::Committed { .. }))
        ));
    }
}

/// However many members poll at once, the group's sync runs once and each
/// member's queue is told once, on its own thread.
#[test]
fn many_members_polling_at_once_run_the_sync_once() {
    const MEMBERS: usize = 8;
    let (_dir, engine, stats) = open();
    let settled = run_group(
        &engine,
        (0..MEMBERS)
            .map(|i| {
                txn_put(
                    &engine,
                    format!("k{i}").as_bytes(),
                    DurabilityMode::Immediate,
                    true,
                )
            })
            .collect(),
    );
    let (group, _) = pending(&settled[0]);
    let barrier = Barrier::new(MEMBERS);
    let told: Vec<(Arc<Told>, ThreadId)> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..MEMBERS)
            .map(|_| {
                let (engine, group, barrier) = (&engine, &group, &barrier);
                scope.spawn(move || {
                    let mut queue = engine.io_queue();
                    let told = wait_on(engine, &queue, group);
                    barrier.wait();
                    while told.count.load(Counting::SeqCst) == 0 {
                        queue.poll(IoBudget::ALL);
                        std::thread::yield_now();
                    }
                    (told, std::thread::current().id())
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    assert_eq!(stats.get_ticker(Ticker::WalSyncCount), 1);
    for (told, owner) in told {
        assert_eq!(told.count.load(Counting::SeqCst), 1);
        assert_eq!(*told.threads.lock().unwrap(), vec![owner]);
    }
}

/// A sync that fails fails every member, applies nothing and leaves nothing
/// in the log (G2), exactly as a group landed inline.
#[test]
fn a_failed_sync_fails_every_member_and_lands_nothing() {
    let (dir, engine, _stats) = open();
    let horizon = engine.snapshot_seq();
    let offset = || {
        engine
            .active_wal
            .lock()
            .as_ref()
            .map(|wal| wal.offset())
            .unwrap()
    };
    let before = offset();
    let settled = run_group(
        &engine,
        vec![
            txn_put(&engine, b"a", DurabilityMode::Immediate, true),
            txn_put(&engine, b"b", DurabilityMode::Immediate, true),
        ],
    );
    let (group, _) = pending(&settled[0]);
    assert!(offset() > before, "the group's records are in the log");
    fault::arm_sync_failure(dir.path());
    let mut queue = engine.io_queue();
    wait_on(&engine, &queue, &group);
    queue.poll(IoBudget::ALL);
    fault::disarm_sync_failure(dir.path());
    assert!(group.is_landed());
    for member in 0..2 {
        assert!(
            group.take(member).unwrap().is_err(),
            "member {member} must fail"
        );
    }
    assert_eq!(engine.snapshot_seq(), horizon);
    assert_eq!(read_now(&engine, b"a"), None);
    assert_eq!(offset(), before, "the group's bytes are rolled back");
}

/// The next writer to take the pipeline lands the group the last leader left
/// owing before its own, so groups land in the order they were written.
#[test]
fn the_next_pipeline_holder_lands_the_owed_group_first() {
    let (_dir, engine, stats) = open();
    let settled = run_group(
        &engine,
        vec![txn_put(&engine, b"first", DurabilityMode::Immediate, true)],
    );
    let (group, member) = pending(&settled[0]);
    let after = engine
        .apply_batch(
            vec![WriteBatchOp::Put {
                key: key_of(b"second"),
                value: b"v".to_vec(),
            }],
            DurabilityMode::Eventual,
            false,
        )
        .unwrap();
    assert!(group.is_landed(), "the blocking writer landed it first");
    let Some(Ok(Settled::Committed {
        seq: Some(first), ..
    })) = group.take(member)
    else {
        panic!("the owed member committed");
    };
    assert!(first < after, "the owed group took the earlier sequence");
    assert_eq!(read_now(&engine, b"first"), Some(b"v".to_vec()));
    assert_eq!(stats.get_ticker(Ticker::WalSyncCount), 1);
}

/// A member that committed with a blocking call lands its group itself: the
/// blocking calls do their own I/O.
#[test]
fn a_blocking_member_lands_its_own_group() {
    let (_dir, engine, stats) = open();
    let settled = run_group(
        &engine,
        vec![
            txn_put(&engine, b"nowait", DurabilityMode::Immediate, true),
            txn_put(&engine, b"blocking", DurabilityMode::Immediate, false),
        ],
    );
    let (group, member) = pending(&settled[1]);
    let landed = group.settle(&engine, member).unwrap();
    assert!(matches!(landed, Settled::Committed { seq: Some(_), .. }));
    assert_eq!(read_now(&engine, b"nowait"), Some(b"v".to_vec()));
    assert_eq!(stats.get_ticker(Ticker::WalSyncCount), 1);
}

/// A group that needs no sync lands inline, nowait member or not: at
/// `Eventual` a commit is ready once applied.
#[test]
fn an_eventual_group_lands_inline_even_with_a_nowait_member() {
    let (_dir, engine, _stats) = open();
    let settled = run_group(
        &engine,
        vec![txn_put(&engine, b"k", DurabilityMode::Eventual, true)],
    );
    assert!(matches!(
        settled[0],
        Ok(Settled::Committed { seq: Some(_), .. })
    ));
    assert!(engine.pipeline.lock().pending.is_none());
    assert_eq!(read_now(&engine, b"k"), Some(b"v".to_vec()));
}

/// A group with no nowait member syncs inline as it always did: the blocking
/// path is unchanged.
#[test]
fn a_group_with_no_nowait_member_syncs_inline() {
    let (_dir, engine, stats) = open();
    let settled = run_group(
        &engine,
        vec![txn_put(&engine, b"k", DurabilityMode::Immediate, false)],
    );
    assert!(matches!(
        settled[0],
        Ok(Settled::Committed { seq: Some(_), .. })
    ));
    assert_eq!(stats.get_ticker(Ticker::WalSyncCount), 1);
    assert!(engine.pipeline.lock().pending.is_none());
}

/// Close lands the group the last leader left owing: the final sync covers
/// it, and its members learn they committed.
#[test]
fn close_lands_the_owed_group() {
    let (_dir, engine, _stats) = open();
    let settled = run_group(
        &engine,
        vec![txn_put(&engine, b"k", DurabilityMode::Immediate, true)],
    );
    let (group, member) = pending(&settled[0]);
    engine.close().unwrap();
    assert!(group.is_landed());
    assert!(matches!(
        group.take(member),
        Some(Ok(Settled::Committed { .. }))
    ));
}
