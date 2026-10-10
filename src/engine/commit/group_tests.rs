//! Optimistic transactions in commit groups (E10, `GroupCommit.tla`).
//!
//! A group is built by hand here, ticket by ticket, so which members share a
//! group is fixed rather than left to timing. The headline is the property
//! test: a group decides and lands exactly what committing its members one at
//! a time, in group order, decides and lands (`group_eq_serial` in
//! `GroupCommit.lean`), with every per-key refinement the transaction layer
//! uses (value reads, identical-write elision, blind merges).

use std::collections::BTreeMap;

use proptest::prelude::*;
use tempfile::TempDir;

use super::super::wal::{fault, ops_record_len};
use super::super::{ConflictKey, EngineOptions, ReadRule, ValidationSet};
use super::early::EarlyVerdict;
use super::*;
use crate::column_family::{DEFAULT_CF_ID, prefix_key};
use crate::{Access, WriteKind};

/// Concatenates operands onto the base, so the order operands apply in shows.
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

fn key_of(name: &[u8]) -> Vec<u8> {
    prefix_key(DEFAULT_CF_ID, name)
}

fn read_now(engine: &RegolithEngine, name: &[u8]) -> Option<Vec<u8>> {
    engine.get(&key_of(name), u64::MAX).unwrap()
}

fn put_now(engine: &RegolithEngine, name: &[u8], value: &[u8]) -> u64 {
    engine
        .apply_batch(
            vec![WriteBatchOp::Put {
                key: key_of(name),
                value: value.to_vec(),
            }],
            DurabilityMode::Eventual,
            false,
        )
        .unwrap()
}

/// One transaction's commit, as `Transaction::commit` hands it over.
#[derive(Clone, Debug)]
struct Txn {
    snapshot: u64,
    /// `(key, value rule)`: a read validated by sequence or by value.
    reads: Vec<(Vec<u8>, bool)>,
    points: BTreeMap<Vec<u8>, Option<Vec<u8>>>,
    merges: Vec<(Vec<u8>, Vec<u8>)>,
    blind: bool,
    /// Keys a classifier exempted from validation.
    exempt: Vec<Vec<u8>>,
    durability: DurabilityMode,
}

impl Txn {
    fn at(snapshot: u64) -> Self {
        Self {
            snapshot,
            reads: Vec::new(),
            points: BTreeMap::new(),
            merges: Vec::new(),
            blind: false,
            exempt: Vec::new(),
            durability: DurabilityMode::Eventual,
        }
    }

    fn put(mut self, name: &[u8], value: &[u8]) -> Self {
        self.points.insert(key_of(name), Some(value.to_vec()));
        self
    }

    fn merge(mut self, name: &[u8], operand: &[u8]) -> Self {
        self.merges.push((key_of(name), operand.to_vec()));
        self
    }

    fn read(mut self, name: &[u8]) -> Self {
        self.reads.push((key_of(name), false));
        self
    }

    fn blind(mut self) -> Self {
        self.blind = true;
        self
    }

    fn immediate(mut self) -> Self {
        self.durability = DurabilityMode::Immediate;
        self
    }

    fn checks(&self) -> ValidationSet {
        let mut reads: Vec<ConflictKey> = self
            .reads
            .iter()
            .map(|(key, by_value)| ConflictKey {
                key: key.clone(),
                observed_seq: self.snapshot,
                found: false,
                access: Access::Read,
                rule: if *by_value {
                    ReadRule::Value
                } else {
                    ReadRule::Seq
                },
            })
            .collect();
        reads.sort_by(|a, b| a.key.cmp(&b.key));
        reads.dedup_by(|a, b| a.key == b.key);
        ValidationSet {
            reads,
            writes_at: Some(self.snapshot),
            blind_merges_commute: self.blind,
            exempt: self.exempt.clone(),
            ranges: Vec::new(),
        }
    }

    /// The request the pipeline carries for this commit, after the check a
    /// transaction runs at the horizon before it queues, or the conflict
    /// that check settled it with.
    fn request(&self, engine: &RegolithEngine) -> Result<WriteRequest, Conflict> {
        let ops = grouped_batch_ops(self.points.clone(), Vec::new(), self.merges.clone());
        let checks = self.checks();
        let early = match engine.check_early(&checks, &ops).unwrap() {
            EarlyVerdict::Conflict(conflict) => return Err(conflict),
            EarlyVerdict::Marks(early) => early,
        };
        Ok(WriteRequest::Txn(TxnRequest {
            checks,
            record_bound: ops_record_len(&ops),
            cost_bound: ops.iter().map(batch_op_memtable_cost).sum(),
            ops,
            appends: Vec::new(),
            durability: self.durability,
            perf: crate::PerfContext::level(),
            early,
            nowait: false,
        }))
    }

    /// Commit alone, as the one-at-a-time run does.
    fn commit_alone(&self, engine: &RegolithEngine) -> io::Result<CommitOutcome> {
        engine.commit_optimistic(
            self.checks(),
            self.points.clone(),
            Vec::new(),
            self.merges.clone(),
            Vec::new(),
            self.durability,
        )
    }
}

/// A member of a hand-built group: a transaction or a plain batch.
#[derive(Clone, Debug)]
enum Member {
    Txn(Txn),
    Plain(Vec<(&'static [u8], Write)>),
}

impl Member {
    fn request(&self, engine: &RegolithEngine) -> Result<WriteRequest, Conflict> {
        match self {
            Member::Txn(txn) => txn.request(engine),
            Member::Plain(writes) => Ok(WriteRequest::Batch {
                ops: plain_ops(writes),
                durability: DurabilityMode::Eventual,
                disable_wal: false,
            }),
        }
    }
}

fn plain_ops(writes: &[(&'static [u8], Write)]) -> Vec<WriteBatchOp> {
    writes.iter().map(|(name, w)| op_of(name, w)).collect()
}

/// Commit `members` as one group, in order, and return what each learned.
/// Every member queues: none may be settled by its check at the horizon.
fn commit_as_group(engine: &RegolithEngine, members: &[Member]) -> Vec<io::Result<Settled>> {
    let requests = members
        .iter()
        .map(|member| member.request(engine).expect("queues for the group"))
        .collect();
    commit_requests(engine, requests)
}

/// Commit `requests` as one group, in order, and return what each learned.
fn commit_requests(
    engine: &RegolithEngine,
    requests: Vec<WriteRequest>,
) -> Vec<io::Result<Settled>> {
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
            .is_none(),
        "the group carries no leader request"
    );
    drop(pipe);
    slots
        .iter()
        .map(|slot| {
            assert!(slot.is_done(), "every member is completed");
            slot.finish_settled()
        })
        .collect()
}

fn conflict_of(settled: &io::Result<Settled>) -> &Conflict {
    match settled {
        Ok(Settled::Conflict { conflict, .. }) => conflict,
        other => panic!("expected a conflict, got {other:?}"),
    }
}

fn committed_seq(settled: &io::Result<Settled>) -> u64 {
    match settled {
        Ok(Settled::Committed { seq: Some(seq), .. }) => *seq,
        other => panic!("expected a commit that wrote, got {other:?}"),
    }
}

/// RED ViewOnly: two members that write one key from one snapshot both commit
/// when each is validated against the view alone. The second conflicts with
/// the first, exactly as it would committing after it.
#[test]
fn a_member_conflicts_with_an_earlier_member_of_its_group() {
    let (_dir, engine) = open();
    let snapshot = put_now(&engine, b"k", b"v0");
    let settled = commit_as_group(
        &engine,
        &[
            Member::Txn(Txn::at(snapshot).put(b"k", b"first")),
            Member::Txn(Txn::at(snapshot).put(b"k", b"second")),
        ],
    );
    let first = committed_seq(&settled[0]);
    let conflict = conflict_of(&settled[1]);
    assert_eq!(conflict.key(), key_of(b"k").as_slice());
    assert_eq!(conflict.mine(), Access::Put);
    assert_eq!(conflict.theirs(), WriteKind::Put);
    assert_eq!(conflict.observed_seq(), snapshot);
    assert_eq!(
        conflict.latest_seq(),
        first,
        "the conflict names the sequence the earlier member took"
    );
    assert_eq!(read_now(&engine, b"k"), Some(b"first".to_vec()));
}

#[test]
fn a_read_conflicts_with_an_earlier_members_write_of_its_key() {
    let (_dir, engine) = open();
    let snapshot = put_now(&engine, b"k", b"v0");
    let settled = commit_as_group(
        &engine,
        &[
            Member::Txn(Txn::at(snapshot).put(b"k", b"new")),
            Member::Txn(Txn::at(snapshot).read(b"k").put(b"other", b"x")),
        ],
    );
    committed_seq(&settled[0]);
    assert_eq!(conflict_of(&settled[1]).mine(), Access::Read);
    assert_eq!(read_now(&engine, b"other"), None);
}

/// A plain write in the group is not validated but counts as committed for
/// every transaction behind it, and for none ahead of it.
#[test]
fn a_plain_write_counts_for_the_members_after_it_only() {
    let (_dir, engine) = open();
    let snapshot = put_now(&engine, b"k", b"v0");
    let plain = Member::Plain(vec![(b"k", Write::Put(1))]);
    let behind = commit_as_group(
        &engine,
        &[
            plain.clone(),
            Member::Txn(Txn::at(snapshot).put(b"k", b"txn")),
        ],
    );
    assert!(matches!(behind[0], Ok(Settled::Write(_))));
    assert_eq!(conflict_of(&behind[1]).theirs(), WriteKind::Put);
    assert_eq!(read_now(&engine, b"k"), Some(b"1".to_vec()));

    let snapshot = engine.snapshot_seq();
    let ahead = commit_as_group(
        &engine,
        &[Member::Txn(Txn::at(snapshot).put(b"k", b"txn")), plain],
    );
    let txn = committed_seq(&ahead[0]);
    let Ok(Settled::Write(plain_seq)) = ahead[1] else {
        panic!("the plain write lands: {:?}", ahead[1]);
    };
    assert!(txn < plain_seq);
    assert_eq!(read_now(&engine, b"k"), Some(b"1".to_vec()));
}

/// Identical-write elision judges an earlier member's write as it judges any
/// committed one: a second put of the same bytes is no conflict.
#[test]
fn an_identical_write_behind_an_earlier_member_is_elided() {
    let (_dir, engine) = open();
    let snapshot = put_now(&engine, b"k", b"v0");
    let settled = commit_as_group(
        &engine,
        &[
            Member::Txn(Txn::at(snapshot).put(b"k", b"same")),
            Member::Txn(Txn::at(snapshot).put(b"k", b"same")),
        ],
    );
    committed_seq(&settled[0]);
    assert!(
        matches!(
            settled[1],
            Ok(Settled::Committed {
                writes_elided: 1,
                ..
            })
        ),
        "{:?}",
        settled[1]
    );
}

/// Blind merges commute inside a group as across groups: both commit, and the
/// operands apply in group order.
#[test]
fn blind_merges_in_one_group_commute() {
    let (_dir, engine) = open();
    let snapshot = put_now(&engine, b"k", b"base:");
    let settled = commit_as_group(
        &engine,
        &[
            Member::Txn(Txn::at(snapshot).merge(b"k", b"a").blind()),
            Member::Txn(Txn::at(snapshot).merge(b"k", b"b").blind()),
            Member::Txn(Txn::at(snapshot).merge(b"k", b"c").blind()),
        ],
    );
    committed_seq(&settled[0]);
    for later in &settled[1..] {
        assert!(
            matches!(
                later,
                Ok(Settled::Committed {
                    merges_commuted: 1,
                    ..
                })
            ),
            "{later:?}"
        );
    }
    assert_eq!(read_now(&engine, b"k"), Some(b"base:abc".to_vec()));

    // A blind merge behind a put of its key in the group still conflicts.
    let snapshot = engine.snapshot_seq();
    let settled = commit_as_group(
        &engine,
        &[
            Member::Txn(Txn::at(snapshot).put(b"k", b"replaced")),
            Member::Txn(Txn::at(snapshot).merge(b"k", b"d").blind()),
        ],
    );
    assert_eq!(conflict_of(&settled[1]).theirs(), WriteKind::Put);
}

/// An aborted member takes no sequence: the member after it takes the one
/// after the last member that landed, and the horizon covers the group.
#[test]
fn an_aborted_member_takes_no_sequence() {
    let (_dir, engine) = open();
    let snapshot = put_now(&engine, b"k", b"v0");
    let settled = commit_as_group(
        &engine,
        &[
            Member::Txn(Txn::at(snapshot).put(b"k", b"a")),
            Member::Txn(Txn::at(snapshot).put(b"k", b"b")),
            Member::Txn(Txn::at(snapshot).put(b"j", b"c")),
        ],
    );
    let first = committed_seq(&settled[0]);
    conflict_of(&settled[1]);
    assert_eq!(committed_seq(&settled[2]), first + 1);
    assert_eq!(engine.snapshot_seq(), first + 1);
}

/// G2 for transactions: a failed sync fails every member, the one the leader
/// decided to abort included, and nothing of the group is applied, published
/// or left in the log. At Immediate a commit is visible only once durable
/// (RED PublishBeforeSync): a group whose fsync failed shows nothing.
#[test]
fn a_failed_sync_fails_every_transaction_in_the_group() {
    let (dir, engine) = open();
    let snapshot = put_now(&engine, b"k", b"v0");
    let horizon = engine.snapshot_seq();
    let latest = engine.latest_seq.load(Ordering::Acquire);
    fault::arm_sync_failure(dir.path());
    let settled = commit_as_group(
        &engine,
        &[
            Member::Txn(Txn::at(snapshot).put(b"k", b"a").immediate()),
            Member::Txn(Txn::at(snapshot).put(b"k", b"b").immediate()),
            Member::Txn(Txn::at(snapshot).put(b"j", b"c").immediate()),
        ],
    );
    fault::disarm_sync_failure(dir.path());
    for (i, outcome) in settled.iter().enumerate() {
        assert!(outcome.is_err(), "member {i} must learn the group failed");
    }
    assert_eq!(engine.snapshot_seq(), horizon, "nothing was published");
    assert_eq!(read_now(&engine, b"k"), Some(b"v0".to_vec()));
    assert_eq!(read_now(&engine, b"j"), None);
    // The drawn sequences are never used, as for a plain group.
    assert!(engine.latest_seq.load(Ordering::Acquire) > latest);

    // The next group decides afresh against the view.
    let snapshot = engine.snapshot_seq();
    let settled = commit_as_group(
        &engine,
        &[Member::Txn(
            Txn::at(snapshot).put(b"k", b"after").immediate(),
        )],
    );
    committed_seq(&settled[0]);
    assert_eq!(read_now(&engine, b"k"), Some(b"after".to_vec()));
}

/// A member whose own check fails writes nothing and fails alone: the others
/// in its group land.
#[test]
fn a_member_whose_own_check_fails_fails_alone() {
    let (_dir, engine) = open();
    let snapshot = put_now(&engine, b"k", b"v0");
    put_now(&engine, b"addressed", b"other bytes");
    // A content-addressed key put beside different bytes breaks its contract.
    let mut addressed = Txn::at(snapshot).put(b"addressed", b"mine");
    addressed.exempt = vec![key_of(b"addressed")];
    let settled = commit_as_group(
        &engine,
        &[
            Member::Txn(addressed),
            Member::Txn(Txn::at(snapshot).put(b"j", b"lands")),
        ],
    );
    let mut settled = settled.into_iter();
    let err = settled.next().unwrap().unwrap_err();
    assert!(
        matches!(crate::Error::from(err), crate::Error::ContentMismatch),
        "the content-addressed put is refused"
    );
    committed_seq(&settled.next().unwrap());
    assert_eq!(
        read_now(&engine, b"addressed"),
        Some(b"other bytes".to_vec())
    );
    assert_eq!(read_now(&engine, b"j"), Some(b"lands".to_vec()));
}

// -- group_eq_serial ----------------------------------------------------

const NAMES: [&[u8]; 3] = [b"a", b"b", b"c"];

fn name() -> impl Strategy<Value = &'static [u8]> {
    proptest::sample::select(NAMES.to_vec())
}

/// A write a generated transaction or plain batch makes: a put of one of two
/// values (so identical writes happen), a delete, or a merge.
#[derive(Clone, Debug)]
enum Write {
    Put(u8),
    Delete,
    Merge(u8),
}

fn write() -> impl Strategy<Value = Write> {
    prop_oneof![
        (0u8..2).prop_map(Write::Put),
        Just(Write::Delete),
        (0u8..2).prop_map(Write::Merge),
    ]
}

#[derive(Clone, Debug)]
struct GenTxn {
    /// Which point of the history the snapshot is at.
    snapshot_at: usize,
    reads: Vec<(&'static [u8], bool)>,
    writes: Vec<(&'static [u8], Write)>,
    blind: bool,
}

#[derive(Clone, Debug)]
enum GenMember {
    Txn(GenTxn),
    Plain(Vec<(&'static [u8], Write)>),
}

fn gen_member() -> impl Strategy<Value = GenMember> {
    let txn = (
        0usize..8,
        proptest::collection::vec((name(), any::<bool>()), 0..3),
        proptest::collection::vec((name(), write()), 0..3),
        any::<bool>(),
    )
        .prop_map(|(snapshot_at, reads, writes, blind)| {
            GenMember::Txn(GenTxn {
                snapshot_at,
                reads,
                writes,
                blind,
            })
        });
    let plain = proptest::collection::vec((name(), write()), 1..3).prop_map(GenMember::Plain);
    prop_oneof![4 => txn, 1 => plain]
}

fn op_of(name: &[u8], write: &Write) -> WriteBatchOp {
    match write {
        Write::Put(v) => WriteBatchOp::Put {
            key: key_of(name),
            value: vec![b'0' + v],
        },
        Write::Delete => WriteBatchOp::Delete { key: key_of(name) },
        Write::Merge(v) => WriteBatchOp::Merge {
            key: key_of(name),
            operand: vec![b'm', b'0' + v],
        },
    }
}

/// The member a generated one stands for, against the history's sequences.
fn member_of(generated: &GenMember, seqs: &[u64]) -> Member {
    match generated {
        GenMember::Plain(writes) => Member::Plain(writes.clone()),
        GenMember::Txn(txn) => {
            let mut built = Txn::at(seqs[txn.snapshot_at % seqs.len()]);
            built.blind = txn.blind;
            built.reads = txn
                .reads
                .iter()
                .map(|(name, by_value)| (key_of(name), *by_value))
                .collect();
            for (name, w) in &txn.writes {
                match w {
                    Write::Put(v) => {
                        built.points.insert(key_of(name), Some(vec![b'0' + v]));
                    }
                    Write::Delete => {
                        built.points.insert(key_of(name), None);
                    }
                    Write::Merge(v) => built.merges.push((key_of(name), vec![b'm', b'0' + v])),
                }
            }
            Member::Txn(built)
        }
    }
}

/// What a member decided, in a form both runs report.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Decided {
    Wrote(u64),
    Landed(Option<u64>),
    Lost {
        key: Vec<u8>,
        mine: Access,
        theirs: WriteKind,
        observed: u64,
        latest: u64,
    },
}

fn lost(conflict: &Conflict) -> Decided {
    Decided::Lost {
        key: conflict.key().to_vec(),
        mine: conflict.mine(),
        theirs: conflict.theirs(),
        observed: conflict.observed_seq(),
        latest: conflict.latest_seq(),
    }
}

proptest! {
    // Each case opens two databases.
    #![proptest_config(ProptestConfig::with_cases(192))]

    /// `group_eq_serial`: committing members as one group decides and lands
    /// exactly what committing them one at a time, in group order, does.
    #[test]
    fn a_group_decides_as_committing_its_members_one_at_a_time(
        history in proptest::collection::vec((name(), write()), 0..6),
        members in proptest::collection::vec(gen_member(), 1..7),
    ) {
        let (_group_dir, grouped) = open();
        let (_serial_dir, serial) = open();
        let mut seqs = vec![grouped.snapshot_seq()];
        for (name, w) in &history {
            for engine in [&grouped, &serial] {
                engine
                    .apply_batch(vec![op_of(name, w)], DurabilityMode::Eventual, false)
                    .unwrap();
            }
            seqs.push(grouped.snapshot_seq());
        }
        let members: Vec<Member> = members.iter().map(|m| member_of(m, &seqs)).collect();

        // Each transaction checks itself at the horizon before it queues. One
        // that conflicts there is decided then, ahead of the whole group: the
        // order decisions are made in is the order to commit one at a time.
        let mut decided_early = Vec::new();
        let mut queued = Vec::new();
        let mut requests = Vec::new();
        for member in &members {
            match member.request(&grouped) {
                Ok(request) => {
                    requests.push(request);
                    queued.push(member);
                }
                Err(conflict) => decided_early.push((member, lost(&conflict))),
            }
        }
        let in_group: Vec<Decided> = decided_early
            .iter()
            .map(|(_, decided)| decided.clone())
            .chain(
                commit_requests(&grouped, requests)
                    .into_iter()
                    .map(|settled| match settled.unwrap() {
                        Settled::Write(seq) => Decided::Wrote(seq),
                        Settled::Committed { seq, .. } => Decided::Landed(seq),
                        Settled::Conflict { conflict, .. } => lost(&conflict),
                        Settled::Pending { .. } => panic!("a blocking group was left pending"),
                    }),
            )
            .collect();
        let decision_order = decided_early.iter().map(|(member, _)| *member).chain(queued);
        let one_at_a_time: Vec<Decided> = decision_order
            .map(|member| match member {
                Member::Plain(writes) => Decided::Wrote(
                    serial
                        .apply_batch(plain_ops(writes), DurabilityMode::Eventual, false)
                        .unwrap(),
                ),
                Member::Txn(txn) => match txn.commit_alone(&serial).unwrap() {
                    CommitOutcome::Ok { seq } => Decided::Landed(seq),
                    CommitOutcome::Conflict(conflict) => lost(&conflict),
                },
            })
            .collect();
        prop_assert_eq!(in_group, one_at_a_time);
        for name in NAMES {
            prop_assert_eq!(read_now(&grouped, name), read_now(&serial, name));
        }
        prop_assert_eq!(grouped.snapshot_seq(), serial.snapshot_seq());
    }
}

fn wal_offset(engine: &RegolithEngine) -> u64 {
    engine
        .active_wal
        .lock()
        .as_ref()
        .map(|wal| wal.offset())
        .unwrap()
}

/// Encryption meets group commit (#266 x #265): the members of a group land
/// as one record, and on an encrypted database that record is one sealed
/// frame for the whole group, so a group pays one seal however many members
/// it carries. Unsealed, the same group is one plain record.
#[test]
fn a_group_lands_as_one_record_sealed_or_not() {
    let writes: [Vec<(&'static [u8], Write)>; 3] = [
        vec![(b"a", Write::Put(1))],
        vec![(b"b", Write::Put(2)), (b"c", Write::Delete)],
        vec![(b"d", Write::Merge(3))],
    ];
    let stage: usize = writes.iter().map(|w| ops_record_len(&plain_ops(w))).sum();
    for sealed in [false, true] {
        let dir = TempDir::new().unwrap();
        let engine = RegolithEngine::open(
            dir.path(),
            EngineOptions {
                merge_operator: Some(Arc::new(Concat)),
                keyring: sealed.then(|| crate::engine::seal::test_keys::keyring(&[1])),
                ..EngineOptions::default()
            },
        )
        .unwrap();
        let before = wal_offset(&engine);
        let members: Vec<Member> = writes.iter().cloned().map(Member::Plain).collect();
        let settled = commit_as_group(&engine, &members);
        assert!(settled.iter().all(Result::is_ok), "{settled:?}");
        let frame = if sealed {
            crate::engine::seal::OVERHEAD
        } else {
            0
        };
        assert_eq!(
            wal_offset(&engine) - before,
            (super::super::wal_frame::HEADER_LEN + frame + stage) as u64,
            "sealed {sealed}: the group is one record of one frame"
        );
        assert_eq!(read_now(&engine, b"b").as_deref(), Some(&b"2"[..]));
    }
}
