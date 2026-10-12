//! The column-family fence on every path a write takes into a commit group.
//!
//! Each test makes a write reach the ordered step after the drop of the
//! family it names retired that family: the test holds the pipeline mutex
//! while the write queues behind it, and runs the drop's ordered step under
//! that same hold, so the write passed every check made before it queued
//! (the database's own handle check included) and meets the drop only in
//! the ordered step. The write must be refused with `InvalidColumnFamily`,
//! take no sequence and leave nothing in the family's key range, while a
//! write to a live family in the same group lands.

use std::collections::BTreeMap;
use std::io;
use std::sync::atomic::Ordering;
use std::time::{Duration, Instant};

use tempfile::TempDir;

use super::super::super::{DurabilityMode, RegolithEngine, ValidationSet};
use super::super::{NowaitCommit, Settled, TxnCommit, WriteRequest};
use crate::column_family::{ColumnFamilyHandle, DEFAULT_CF_ID, cf_lower_bound, cf_upper_bound};
use crate::{Db, Error, IngestOptions, Options, SstFileWriter, WriteBatchOp, prefix_key};

/// A database with no worker, so no background thread takes the pipeline or
/// the compaction gate, and one live family to drop.
fn open() -> (TempDir, Db, ColumnFamilyHandle) {
    let dir = TempDir::new().unwrap();
    let db = Db::open(dir.path(), Options::default().max_background_compactions(0)).unwrap();
    let cf = db.create_column_family("doomed").unwrap();
    (dir, db, cf)
}

fn put(id: u32, key: &[u8]) -> Vec<WriteBatchOp> {
    vec![WriteBatchOp::Put {
        key: prefix_key(id, key),
        value: b"v".to_vec(),
    }]
}

/// Entries visible at the newest sequence in family `id`'s key range, read
/// below the column-family layer: the only place a write that slipped past
/// a drop could still be seen.
fn in_family(engine: &RegolithEngine, id: u32) -> usize {
    crate::collect_range(
        engine.new_iter_latest(),
        Some(&cf_lower_bound(id)),
        Some(&cf_upper_bound(id)),
    )
    .unwrap()
    .len()
}

fn assert_refused(outcome: io::Result<impl std::fmt::Debug>, path: &str) {
    match outcome.map_err(Error::from) {
        Err(Error::InvalidColumnFamily(_)) => {}
        other => panic!("{path}: a write to a dropped family was not refused: {other:?}"),
    }
}

/// Wait, with a deadline and bounded backoff, until a writer's ticket is in
/// the commit ring.
fn await_queued(engine: &RegolithEngine) {
    let deadline = Instant::now() + Duration::from_secs(30);
    let mut backoff = Duration::from_micros(50);
    while engine.commit_ring.is_empty() {
        assert!(Instant::now() < deadline, "the writer never queued");
        std::thread::sleep(backoff);
        backoff = (backoff * 2).min(Duration::from_millis(5));
    }
}

/// Run the drop's ordered step under the pipeline the caller holds.
fn drop_under(engine: &RegolithEngine, pipe: &mut super::super::Pipeline, cf: &ColumnFamilyHandle) {
    engine
        .drop_family_locked(
            pipe,
            engine.families().unwrap(),
            cf,
            DurabilityMode::Eventual,
        )
        .unwrap();
}

/// The leader's own request (`lead_with`): a write that passed the handle
/// check before the drop leads its own group after it.
#[test]
fn the_leaders_own_write_to_a_dropped_family_is_refused() {
    let (_dir, db, cf) = open();
    let engine = &db.engine;
    let id = cf.id();
    db.drop_column_family(cf).unwrap();
    let before = engine.latest_seq.load(Ordering::Acquire);
    assert_refused(
        engine.apply_batch(put(id, b"late"), DurabilityMode::Eventual, false),
        "lead_with",
    );
    assert_eq!(
        engine.latest_seq.load(Ordering::Acquire),
        before,
        "a refused write took a sequence"
    );
    assert_eq!(in_family(engine, id), 0);
}

/// A follower's ticket (`admit_from_ring`), in a group with a write to a
/// live family: the one is refused, the other lands, and the group takes
/// one sequence.
#[test]
fn a_queued_write_admitted_after_the_drop_is_refused_and_its_group_lands() {
    let (_dir, db, cf) = open();
    let engine = &db.engine;
    let id = cf.id();
    let mut pipe = engine.pipeline.lock();
    std::thread::scope(|scope| {
        let late =
            scope.spawn(|| engine.apply_batch(put(id, b"late"), DurabilityMode::Eventual, false));
        await_queued(engine);
        drop_under(engine, &mut pipe, &cf);
        let before = engine.latest_seq.load(Ordering::Acquire);
        let mine = engine.lead_with(
            &mut pipe,
            WriteRequest::Batch {
                ops: put(DEFAULT_CF_ID, b"live"),
                durability: DurabilityMode::Eventual,
                disable_wal: false,
            },
        );
        assert!(
            matches!(mine, Ok(Settled::Write(seq)) if seq == before + 1),
            "the live write in the same group did not land alone: {mine:?}"
        );
        assert!(
            engine.commit_ring.is_empty(),
            "the queued write was not admitted"
        );
        drop(pipe);
        assert_refused(late.join().unwrap(), "admit_from_ring");
    });
    assert_eq!(in_family(engine, id), 0);
    assert_eq!(
        engine
            .get(&prefix_key(DEFAULT_CF_ID, b"live"), u64::MAX)
            .unwrap(),
        Some(b"v".to_vec())
    );
}

/// The ticket the bounded leader hands the pipeline to (`hand_off`): held
/// across the drop, it is fenced when the group it heads runs.
#[test]
fn the_ticket_the_hand_off_holds_is_fenced_when_its_group_runs() {
    let (_dir, db, cf) = open();
    let engine = &db.engine;
    let id = cf.id();
    let mut pipe = engine.pipeline.lock();
    std::thread::scope(|scope| {
        let late =
            scope.spawn(|| engine.apply_batch(put(id, b"late"), DurabilityMode::Eventual, false));
        await_queued(engine);
        engine.hand_off(&mut pipe);
        assert!(pipe.held.is_some(), "setup: the hand-off holds the ticket");
        drop_under(engine, &mut pipe, &cf);
        assert!(pipe.held.is_some(), "the drop's group took the held ticket");
        // Released: the writer, woken by the hand-off, leads its own group.
        drop(pipe);
        assert_refused(late.join().unwrap(), "hand_off");
    });
    assert_eq!(in_family(engine, id), 0);
}

/// An optimistic transaction's commit, a group member decided in group
/// order: fenced before the decide stage validates it.
#[test]
fn a_queued_transaction_admitted_after_the_drop_is_refused() {
    let (_dir, db, cf) = open();
    let engine = &db.engine;
    let id = cf.id();
    let snapshot = engine.visible_seq.visible();
    let mut pipe = engine.pipeline.lock();
    std::thread::scope(|scope| {
        let late = scope.spawn(|| {
            let mut points = BTreeMap::new();
            points.insert(prefix_key(id, b"txn"), Some(b"v".to_vec()));
            engine.commit_optimistic(
                ValidationSet {
                    reads: Vec::new(),
                    writes_at: Some(snapshot),
                    blind_merges_commute: false,
                    exempt: Vec::new(),
                    ranges: Vec::new(),
                },
                points,
                Vec::new(),
                Vec::new(),
                Vec::new(),
                DurabilityMode::Eventual,
            )
        });
        await_queued(engine);
        drop_under(engine, &mut pipe, &cf);
        drop(pipe);
        assert_refused(late.join().unwrap(), "transaction member");
    });
    assert_eq!(in_family(engine, id), 0);
}

/// The counter `allocate` reserves, logged through `lead_with`.
#[test]
fn an_allocation_in_a_dropped_family_is_refused() {
    let (_dir, db, cf) = open();
    let engine = &db.engine;
    let id = cf.id();
    db.drop_column_family(cf).unwrap();
    assert_refused(engine.allocate(prefix_key(id, b"counter"), 3), "allocate");
    assert_eq!(in_family(engine, id), 0);
}

/// An ingest whose table was validated while the family was live, and whose
/// install reaches the ordered step after the drop.
#[test]
fn an_ingest_installed_after_the_drop_is_refused() {
    let (dir, db, cf) = open();
    let engine = &db.engine;
    let id = cf.id();
    let source = dir.path().join("external.sst");
    let mut writer = SstFileWriter::create(&source, &Options::default()).unwrap();
    writer.put_cf(&cf, b"ingested", b"v").unwrap();
    writer.finish().unwrap();
    let tables_before = engine
        .published_version()
        .levels
        .iter()
        .map(Vec::len)
        .sum::<usize>();

    let mut pipe = engine.pipeline.lock();
    std::thread::scope(|scope| {
        let ingest = scope.spawn(|| {
            db.ingest_external_files(std::slice::from_ref(&source), IngestOptions::default())
                .wait()
        });
        // The ingest takes the compaction gate once its table is staged and
        // validated, then waits here for the pipeline.
        let deadline = Instant::now() + Duration::from_secs(30);
        while engine.compaction_gate().try_shared().is_some() {
            assert!(
                Instant::now() < deadline,
                "the ingest never finished staging"
            );
            std::thread::sleep(Duration::from_millis(1));
        }
        drop_under(engine, &mut pipe, &cf);
        drop(pipe);
        match ingest.join().unwrap() {
            Err(Error::InvalidColumnFamily(_)) => {}
            other => panic!("ingest: a table for a dropped family was not refused: {other:?}"),
        }
    });
    assert_eq!(in_family(engine, id), 0);
    assert_eq!(
        engine
            .published_version()
            .levels
            .iter()
            .map(Vec::len)
            .sum::<usize>(),
        tables_before,
        "the refused table was installed"
    );
}

/// A transaction committed with `commit_nowait` that writes `key` in family
/// `id` at `Immediate` durability: its group needs an fsync and carries a
/// nowait member, so the group is written and left owing its landing.
fn nowait_txn(engine: &RegolithEngine, id: u32, key: &[u8]) -> io::Result<NowaitCommit> {
    let mut points = BTreeMap::new();
    points.insert(prefix_key(id, key), Some(b"v".to_vec()));
    engine.commit_optimistic_nowait(TxnCommit {
        checks: ValidationSet {
            reads: Vec::new(),
            writes_at: Some(engine.visible_seq.visible()),
            blind_merges_commute: false,
            exempt: Vec::new(),
            ranges: Vec::new(),
        },
        point_ops: points,
        range_deletes: Vec::new(),
        merges: Vec::new(),
        appends: Vec::new(),
        durability: DurabilityMode::Immediate,
    })
}

/// A group left owing its fsync (the commit side's deferred group): a nowait
/// transaction to a live family and, admitted after the drop, a plain write
/// to the dropped family, in one group. The fence runs before the group is
/// written, so the plain write takes no sequence and is settled refused from
/// its verdict when the owed group lands (here, by the plain writer itself,
/// as a blocking member lands an owed group); the nowait member lands.
#[test]
fn a_member_fenced_in_an_owed_group_is_refused_when_the_group_lands() {
    let (_dir, db, cf) = open();
    let engine = &db.engine;
    let id = cf.id();
    let mut pipe = engine.pipeline.lock();
    std::thread::scope(|scope| {
        let nowait = scope.spawn(|| nowait_txn(engine, DEFAULT_CF_ID, b"nowait"));
        await_queued(engine);
        // The nowait ticket heads the next group; the plain write queues
        // behind it.
        engine.hand_off(&mut pipe);
        let late =
            scope.spawn(|| engine.apply_batch(put(id, b"late"), DurabilityMode::Eventual, false));
        await_queued(engine);
        drop_under(engine, &mut pipe, &cf);
        let before = engine.latest_seq.load(Ordering::Acquire);
        engine.lead_one(&mut pipe);
        assert!(
            pipe.pending.is_some(),
            "setup: the group was left owing its fsync"
        );
        assert_eq!(
            engine.latest_seq.load(Ordering::Acquire),
            before + 1,
            "the fenced member took a sequence in the owed group"
        );
        drop(pipe);
        assert_refused(late.join().unwrap(), "owed group");
        match nowait.join().unwrap().unwrap() {
            NowaitCommit::Pending { group, member } => {
                let settled = group.settle(engine, member).unwrap();
                assert!(
                    matches!(settled, Settled::Committed { seq: Some(_), .. }),
                    "the live member of the owed group did not land: {settled:?}"
                );
            }
            NowaitCommit::Done(outcome) => {
                panic!("setup: the nowait member's group was not left owing: {outcome:?}")
            }
        }
    });
    assert_eq!(in_family(engine, id), 0);
    assert_eq!(
        engine
            .get(&prefix_key(DEFAULT_CF_ID, b"nowait"), u64::MAX)
            .unwrap(),
        Some(b"v".to_vec())
    );
}

/// A group left owing its landing that wrote to a family is landed before
/// the family's drop runs its own group: create and drop take the pipeline
/// as every administrative caller does (`lock_pipeline`), and their group of
/// one lands what the last leader left owing first (`lead_alone`). So the
/// owed write is applied and published below the tombstone, before the
/// drop's group publishes past it.
#[test]
fn a_drop_lands_the_group_left_owing_before_it_runs() {
    let (_dir, db, cf) = open();
    let engine = &db.engine;
    let id = cf.id();
    let (group, member) = match nowait_txn(engine, id, b"owed").unwrap() {
        NowaitCommit::Pending { group, member } => (group, member),
        NowaitCommit::Done(outcome) => {
            panic!("setup: the nowait commit's group was not left owing: {outcome:?}")
        }
    };
    assert!(
        !group.is_landed(),
        "setup: nothing landed the owed group yet"
    );
    let owed_seq = engine.latest_seq.load(Ordering::Acquire);
    db.drop_column_family(cf).unwrap();
    assert!(
        group.is_landed(),
        "the drop ran with a group left owing ahead of it"
    );
    let settled = group
        .take(member)
        .expect("the owed group settled its member");
    assert!(
        matches!(settled, Ok(Settled::Committed { seq: Some(seq), .. }) if seq == owed_seq),
        "the owed member did not land at its own sequence: {settled:?}"
    );
    // Visible at its own sequence, below the tombstone, and deleted above it.
    assert_eq!(
        engine.get(&prefix_key(id, b"owed"), owed_seq).unwrap(),
        Some(b"v".to_vec())
    );
    assert_eq!(in_family(engine, id), 0);
}
