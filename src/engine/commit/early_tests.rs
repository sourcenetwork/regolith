//! Validation outside the pipeline mutex (`early_check_split` in
//! `GroupCommit.lean`): checking a commit up to a horizon `h` before it
//! queues, and only above `h` under the mutex, decides as one check of every
//! version does.

use std::sync::mpsc;
use std::time::Duration;

use proptest::prelude::*;
use tempfile::TempDir;

use super::super::wal::ops_record_len;
use super::super::{ConflictKey, EngineOptions, RangeCheck, ReadRule, ValidationSet};
use super::early::EarlyVerdict;
use super::*;
use crate::Access;
use crate::column_family::{DEFAULT_CF_ID, prefix_key};

/// Keeps the newest operand on top of the base, so operands and bases both
/// show in a value.
struct Concat;

impl crate::MergeOperator for Concat {
    fn name(&self) -> &'static str {
        "concat"
    }

    fn full_merge(&self, _: &[u8], base: Option<&[u8]>, operands: &[&[u8]]) -> Option<Vec<u8>> {
        let mut out = base.map(<[u8]>::to_vec).unwrap_or_default();
        for operand in operands {
            out.extend_from_slice(operand);
        }
        Some(out)
    }
}

fn open() -> (TempDir, Arc<RegolithEngine>) {
    let dir = TempDir::new().unwrap();
    let engine = RegolithEngine::open(
        dir.path(),
        EngineOptions {
            merge_operator: Some(Arc::new(Concat)),
            ..EngineOptions::default()
        },
    )
    .unwrap();
    (dir, engine)
}

const NAMES: [&[u8]; 4] = [b"a", b"b", b"c", b"d"];

fn key_of(name: &[u8]) -> Vec<u8> {
    prefix_key(DEFAULT_CF_ID, name)
}

/// One step of a history: a write of one key, a range delete, or a flush.
#[derive(Clone, Debug)]
enum Step {
    Put(usize, u8),
    Delete(usize),
    Merge(usize, u8),
    DeleteRange(usize, usize),
    Flush,
}

fn step() -> impl Strategy<Value = Step> {
    prop_oneof![
        4 => (0..NAMES.len(), 0u8..2).prop_map(|(k, v)| Step::Put(k, v)),
        2 => (0..NAMES.len()).prop_map(Step::Delete),
        3 => (0..NAMES.len(), 0u8..2).prop_map(|(k, v)| Step::Merge(k, v)),
        1 => (0..NAMES.len(), 1..=NAMES.len()).prop_map(|(a, b)| Step::DeleteRange(a, b)),
        1 => Just(Step::Flush),
    ]
}

fn apply(engine: &RegolithEngine, step: &Step) {
    let op = match *step {
        Step::Put(k, v) => WriteBatchOp::Put {
            key: key_of(NAMES[k]),
            value: vec![b'0' + v],
        },
        Step::Delete(k) => WriteBatchOp::Delete {
            key: key_of(NAMES[k]),
        },
        Step::Merge(k, v) => WriteBatchOp::Merge {
            key: key_of(NAMES[k]),
            operand: vec![b'm', b'0' + v],
        },
        Step::DeleteRange(a, b) => {
            let (lo, end) = (a.min(b), a.max(b).min(NAMES.len() - 1));
            if lo >= end {
                return;
            }
            WriteBatchOp::DeleteRange {
                start: key_of(NAMES[lo]),
                end: key_of(NAMES[end]),
            }
        }
        Step::Flush => {
            engine.flush_active_memtable().unwrap();
            return;
        }
    };
    engine
        .apply_batch(vec![op], DurabilityMode::Eventual, false)
        .unwrap();
}

/// A generated transaction: what it read and how, what it scanned, what it
/// writes, and which keys a classifier exempted.
#[derive(Clone, Debug)]
struct Shape {
    reads: Vec<(usize, u8)>,
    scan: Option<(usize, usize)>,
    writes: Vec<(usize, Step)>,
    blind: bool,
    exempt: Option<usize>,
}

fn shape() -> impl Strategy<Value = Shape> {
    let write = prop_oneof![
        (0u8..2).prop_map(|v| Step::Put(0, v)),
        Just(Step::Delete(0)),
        (0u8..2).prop_map(|v| Step::Merge(0, v)),
    ];
    (
        proptest::collection::vec((0..NAMES.len(), 0u8..3), 0..3),
        proptest::option::of((0..NAMES.len(), 1..=NAMES.len())),
        proptest::collection::vec((0..NAMES.len(), write), 0..3),
        any::<bool>(),
        proptest::option::of(0..NAMES.len()),
    )
        .prop_map(|(reads, scan, writes, blind, exempt)| Shape {
            reads,
            scan,
            writes,
            blind,
            exempt,
        })
}

/// The commit `shape` makes from a snapshot at `snapshot`.
fn commit_of(shape: &Shape, snapshot: u64) -> (ValidationSet, Vec<WriteBatchOp>) {
    let mut points = std::collections::BTreeMap::new();
    let mut merges = Vec::new();
    for (k, w) in &shape.writes {
        match w {
            Step::Put(_, v) => {
                points.insert(key_of(NAMES[*k]), Some(vec![b'0' + v]));
            }
            Step::Delete(_) => {
                points.insert(key_of(NAMES[*k]), None);
            }
            Step::Merge(_, v) => merges.push((key_of(NAMES[*k]), vec![b'm', b'0' + v])),
            _ => {}
        }
    }
    let exempt: Vec<Vec<u8>> = shape
        .exempt
        .map(|k| key_of(NAMES[k]))
        .filter(|key| {
            // A classifier never exempts a key the commit deletes.
            !matches!(points.get(key), Some(None))
        })
        .into_iter()
        .collect();
    let mut reads: Vec<ConflictKey> = shape
        .reads
        .iter()
        .map(|&(k, how)| ConflictKey {
            key: key_of(NAMES[k]),
            observed_seq: snapshot,
            found: false,
            access: if how == 2 {
                Access::ReadPresence
            } else {
                Access::Read
            },
            rule: if how == 1 {
                ReadRule::Value
            } else {
                ReadRule::Seq
            },
        })
        .filter(|read| !exempt.contains(&read.key))
        .collect();
    reads.sort_by(|a, b| a.key.cmp(&b.key));
    reads.dedup_by(|a, b| a.key == b.key);
    let ranges = shape
        .scan
        .and_then(|(a, b)| {
            let (lo, hi) = (a.min(b), a.max(b));
            (lo < hi).then(|| RangeCheck {
                lo: key_of(NAMES[lo]),
                hi: key_of(NAMES[hi.min(NAMES.len() - 1)]),
                observed_seq: snapshot,
            })
        })
        .filter(|range| range.lo < range.hi)
        .into_iter()
        .collect();
    let checks = ValidationSet {
        reads,
        writes_at: Some(snapshot),
        blind_merges_commute: shape.blind,
        exempt,
        ranges,
    };
    (checks, grouped_batch_ops(points, Vec::new(), merges))
}

/// What a commit decided, in a form both engines report.
#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    Landed {
        seq: Option<u64>,
        commuted: u64,
        elided: u64,
    },
    Lost {
        key: Vec<u8>,
        mine: Access,
        latest: u64,
    },
    Refused(String),
}

/// Check `checks` and `ops` at the current horizon, then run `between` and
/// commit what the check left to the group. Returns the outcome and whether
/// the check at the horizon settled it.
fn split_commit(
    engine: &RegolithEngine,
    checks: ValidationSet,
    ops: Vec<WriteBatchOp>,
    between: impl FnOnce(),
) -> (Outcome, bool) {
    let early = match engine.check_early(&checks, &ops).unwrap() {
        EarlyVerdict::Conflict(conflict) => {
            between();
            return (
                Outcome::Lost {
                    key: conflict.key().to_vec(),
                    mine: conflict.mine(),
                    latest: conflict.latest_seq(),
                },
                true,
            );
        }
        EarlyVerdict::Marks(early) => early,
    };
    between();
    let request = WriteRequest::Txn(TxnRequest {
        record_bound: ops_record_len(&ops),
        cost_bound: ops.iter().map(batch_op_memtable_cost).sum(),
        checks,
        ops,
        appends: Vec::new(),
        durability: DurabilityMode::Eventual,
        perf: crate::PerfLevel::Disable,
        early,
        nowait: false,
    });
    let mut pipe = engine.pipeline.lock();
    let settled = engine
        .lead_with(&mut pipe, request)
        .map_err(|e| e.to_string());
    let outcome = match settled {
        Ok(Settled::Committed {
            seq,
            merges_commuted,
            writes_elided,
            ..
        }) => Outcome::Landed {
            seq,
            commuted: merges_commuted,
            elided: writes_elided,
        },
        Ok(Settled::Conflict { conflict, .. }) => Outcome::Lost {
            key: conflict.key().to_vec(),
            mine: conflict.mine(),
            latest: conflict.latest_seq(),
        },
        Ok(Settled::Write(_)) => panic!("a transaction settled as a plain write"),
        Ok(Settled::Pending { .. }) => panic!("a blocking commit was left pending"),
        Err(e) => Outcome::Refused(e),
    };
    (outcome, false)
}

fn read_all(engine: &RegolithEngine) -> Vec<Option<Vec<u8>>> {
    NAMES
        .iter()
        .map(|name| engine.get(&key_of(name), u64::MAX).unwrap())
        .collect()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// The commit checked up to a horizon taken partway through the writes
    /// that follow its snapshot, and above it under the mutex, decides as the
    /// same commit checked in full once every write has landed. When the
    /// check at the horizon settles the commit, the outcome is the same and
    /// only which conflicting key it names may differ.
    #[test]
    fn checking_up_to_a_horizon_then_above_it_decides_as_one_check(
        before in proptest::collection::vec(step(), 0..5),
        until_horizon in proptest::collection::vec(step(), 0..5),
        after_horizon in proptest::collection::vec(step(), 0..5),
        shape in shape(),
    ) {
        let (_split_dir, split) = open();
        let (_whole_dir, whole) = open();
        for engine in [&split, &whole] {
            for s in &before {
                apply(engine, s);
            }
        }
        let snapshot = split.snapshot_seq();
        prop_assert_eq!(snapshot, whole.snapshot_seq());
        for engine in [&split, &whole] {
            for s in &until_horizon {
                apply(engine, s);
            }
        }
        let (checks, ops) = commit_of(&shape, snapshot);
        let (split_outcome, settled_early) =
            split_commit(&split, checks, ops, || {
                for s in &after_horizon {
                    apply(&split, s);
                }
            });
        for s in &after_horizon {
            apply(&whole, s);
        }
        let (checks, ops) = commit_of(&shape, snapshot);
        // Every write has landed: the check at the horizon sees them all and
        // nothing lands above it, so this is one check of every version.
        let (whole_outcome, _) = split_commit(&whole, checks, ops, || {});
        match (&split_outcome, &whole_outcome) {
            (Outcome::Lost { .. }, Outcome::Lost { .. }) if settled_early => {}
            _ => prop_assert_eq!(&split_outcome, &whole_outcome),
        }
        prop_assert_eq!(read_all(&split), read_all(&whole));
    }
}

/// A commit the check at the horizon settles never waits for the pipeline:
/// it aborts while another thread holds the mutex.
#[test]
fn a_conflict_found_at_the_horizon_does_not_wait_for_the_pipeline() {
    let (_dir, engine) = open();
    let snapshot = engine.snapshot_seq();
    apply(&engine, &Step::Put(0, 1));
    let checks = ValidationSet {
        reads: vec![ConflictKey {
            key: key_of(b"a"),
            observed_seq: snapshot,
            found: false,
            access: Access::ReadForUpdate,
            rule: ReadRule::Seq,
        }],
        writes_at: Some(snapshot),
        blind_merges_commute: false,
        exempt: Vec::new(),
        ranges: Vec::new(),
    };
    let held = engine.pipeline.lock();
    let (done, outcome) = mpsc::channel();
    std::thread::scope(|scope| {
        scope.spawn(|| {
            let mut points = std::collections::BTreeMap::new();
            points.insert(key_of(b"a"), Some(b"mine".to_vec()));
            let committed = engine.commit_optimistic(
                checks,
                points,
                Vec::new(),
                Vec::new(),
                Vec::new(),
                DurabilityMode::Eventual,
            );
            done.send(committed).unwrap();
        });
        let committed = outcome
            .recv_timeout(Duration::from_secs(30))
            .expect("the commit waited for the pipeline mutex");
        drop(held);
        let CommitOutcome::Conflict(conflict) = committed.unwrap() else {
            panic!("a stale read for update conflicts");
        };
        assert_eq!(conflict.key(), key_of(b"a").as_slice());
        assert_eq!(conflict.mine(), Access::ReadForUpdate);
    });
}

/// With nothing committed since the snapshot the check at the horizon reads
/// nothing, and the leader looks only at the memtables: a key whose versions
/// all sit in a table is never looked up there.
#[test]
fn a_commit_nothing_landed_under_never_reads_a_table() {
    let (_dir, engine) = open();
    apply(&engine, &Step::Put(0, 0));
    engine.flush_active_memtable().unwrap();
    let snapshot = engine.snapshot_seq();
    let (checks, ops) = commit_of(
        &Shape {
            reads: vec![(0, 0)],
            scan: Some((0, 3)),
            writes: vec![(0, Step::Put(0, 1)), (1, Step::Merge(0, 0))],
            blind: true,
            exempt: None,
        },
        snapshot,
    );
    crate::PerfContext::set_level(crate::PerfLevel::EnableCount);
    crate::PerfContext::reset();
    let (outcome, settled_early) = split_commit(&engine, checks, ops, || {});
    let lookups = crate::PerfContext::capture().block_cache_lookup_count;
    crate::PerfContext::set_level(crate::PerfLevel::Disable);
    assert!(!settled_early);
    assert!(matches!(outcome, Outcome::Landed { .. }), "{outcome:?}");
    assert_eq!(lookups, 0, "the commit read a table block");
}
