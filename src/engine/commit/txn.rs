//! An optimistic transaction as a member of a commit group (E10).
//!
//! A transaction's commit joins the same commit groups plain writes use, so a
//! group shares one WAL append and at most one fsync. The leader decides each
//! member in group order: it validates the member against the view plus the
//! writes of the members before it in the group, and only a member that
//! passes takes sequences, positions for its appends, and a record. This is
//! `GroupCommit.tla` and `group_eq_serial` in `GroupCommit.lean`: each member
//! gets the verdict committing the members one at a time, in group order,
//! would give it. A member validated against the view alone would commit over
//! an earlier member's write of the same key (RED ViewOnly).
//!
//! The check of one member is the check a transaction committing alone
//! always ran: [`RegolithEngine::validate`] runs it against whatever view it
//! is given, and the group hands it a view whose newest source holds the
//! earlier members' writes at the sequences they will take (see `group.rs`).

use std::io;

use super::super::{DurabilityMode, ReadView, RegolithEngine, ValidationSet};
use super::append::PendingAppend;
use super::early::{Early, Mark};
use super::replaced::Replaced;
use super::write_check::WriteCheck;
use crate::perf_context::{PerfContextSnapshot, PerfLevel};
use crate::statistics::Ticker;
use crate::{Access, Conflict, WriteBatchOp};

/// An optimistic transaction's commit, handed to the commit pipeline.
pub(crate) struct TxnRequest {
    /// What the commit validates beyond its written keys.
    pub(crate) checks: ValidationSet,
    /// Its writes, laid out as `grouped_batch_ops` lays them out.
    pub(crate) ops: Vec<WriteBatchOp>,
    /// Its appends, numbered only if it validates.
    pub(crate) appends: Vec<PendingAppend>,
    pub(crate) durability: DurabilityMode,
    /// Framed WAL bytes the member can stage at most: its record with every
    /// append counted at the bound its layout declares.
    pub(crate) record_bound: usize,
    /// Memtable bytes the member can add at most, appends counted the same way.
    pub(crate) cost_bound: usize,
    /// The committing thread's perf level: the leader counts the member's
    /// validation at it, on that thread's behalf.
    pub(crate) perf: PerfLevel,
    /// The check the transaction ran at a horizon before it queued; the
    /// leader checks only what landed above it.
    pub(crate) early: Early,
    /// Committed by `commit_nowait`: the commit must not wait for its
    /// group's fsync, so a group carrying it that needs one is left owing it
    /// (`deferred.rs`).
    pub(crate) nowait: bool,
}

/// The leader's verdict on one transaction member.
#[derive(Debug)]
pub(crate) enum Verdict {
    /// It validated. The counts are recorded once the group lands.
    Accept {
        merges_commuted: u64,
        writes_elided: u64,
    },
    /// It lost a race; the key still carries its column-family prefix.
    Conflict(Conflict),
}

/// What one ticket of a commit group learns when its group completes.
#[derive(Debug)]
pub(crate) enum Settled {
    /// A plain write landed; the last sequence its operations took.
    Write(u64),
    /// A transaction validated and its writes landed. `seq` is the last
    /// sequence they took, `None` when it wrote nothing.
    Committed {
        seq: Option<u64>,
        merges_commuted: u64,
        writes_elided: u64,
        /// What the leader counted validating it, when its thread counts.
        perf: Option<Box<PerfContextSnapshot>>,
    },
    /// A transaction lost a race and wrote nothing.
    Conflict {
        conflict: Conflict,
        /// What the leader counted validating it, when its thread counts.
        perf: Option<Box<PerfContextSnapshot>>,
    },
    /// The group was written and still owes its fsync: what the member
    /// learns is taken from `group` once it lands, as member `member`.
    Pending {
        group: std::sync::Arc<super::GroupSync>,
        member: usize,
    },
}

impl Settled {
    /// The sequence a plain write landed at. A plain write only ever settles
    /// as [`Settled::Write`] once its group landed; anything else is
    /// reported, not trusted.
    pub(crate) fn into_seq(self) -> io::Result<u64> {
        match self {
            Settled::Write(seq) => Ok(seq),
            other => Err(io::Error::other(format!(
                "a plain write settled as a transaction ({other:?})"
            ))),
        }
    }
}

impl RegolithEngine {
    /// Validate one optimistic commit against `view`, exactly as committing
    /// it alone against that view would: its reads, then its validated
    /// scans, then its written keys in operation order, so a multi-key
    /// conflict names the same key on every run.
    ///
    /// `early` is the check the transaction ran at a horizon before it
    /// queued: an item it found clean is checked here only if something
    /// landed on it above that horizon, and then in full (`early.rs`).
    /// `ceiling` is the newest sequence `view` holds, the earlier members of
    /// the group included; a content-addressed put looks itself up only when
    /// something landed above the transaction's snapshot.
    pub(super) fn validate(
        &self,
        checks: &ValidationSet,
        ops: &[WriteBatchOp],
        early: &Early,
        view: &ReadView,
        ceiling: u64,
    ) -> io::Result<Verdict> {
        let mut merges_commuted = 0u64;
        let mut writes_elided = 0u64;
        let horizon = early.horizon;
        // No table holds a sequence above the horizon, so whatever landed
        // above it is in a memtable of the view.
        let memtables_only = view.version.last_seq <= horizon;
        let landed = |key: &[u8], mark: Mark| -> io::Result<bool> {
            Ok(mark == Mark::Dirty
                || self.landed_above_horizon(key, horizon, view, memtables_only)?)
        };
        for (at, check) in checks.reads.iter().enumerate() {
            if !landed(&check.key, early.mark(at))? {
                continue;
            }
            if let Some((latest_seq, newest)) = self.latest_version_in_view(&check.key, view)?
                && latest_seq > check.observed_seq
                // Only a newer version can have changed what the read
                // decided, and the read's rule says whether this one did: a
                // presence-only read needs the key gone, a value read the
                // bytes different, a projected read a part touched.
                && let Some((seq, theirs)) =
                    self.read_changed(check, (latest_seq, newest), u64::MAX, view)?
            {
                // The commit-level `CommitConflicts` ticker is recorded once
                // per commit where the outcome is mapped; this is the per-key
                // subset.
                if let Some(s) = self.statistics() {
                    s.add(Ticker::CommitConflictsOnRead, 1);
                }
                return Ok(Verdict::Conflict(Conflict::new(
                    check.key.clone(),
                    check.access,
                    theirs,
                    check.observed_seq,
                    seq,
                )));
            }
        }
        // A validated scan decided on a whole range, so a write anywhere in it
        // after the snapshot is a conflict, a key that left it or appeared in
        // it alike. One found clean at the horizon looks only above it.
        let reads = checks.reads.len();
        for (at, range) in checks.ranges.iter().enumerate() {
            let (floor, memtables_only) = match early.mark(reads + at) {
                Mark::Dirty => (range.observed_seq, false),
                _ => (horizon.max(range.observed_seq), memtables_only),
            };
            if let Some((key, seq, theirs)) =
                self.written_in_range_of(&range.lo, &range.hi, floor, view, memtables_only)?
            {
                if let Some(s) = self.statistics() {
                    s.add(Ticker::CommitConflictsOnRead, 1);
                }
                return Ok(Verdict::Conflict(Conflict::new(
                    key,
                    Access::ScannedRange,
                    theirs,
                    range.observed_seq,
                    seq,
                )));
            }
        }
        // The merges arrive sorted by key, so a key merged N times in one
        // transaction is probed once, not N times: a repeat of the previous
        // merged key is skipped, since another probe would just walk the
        // same view again for an answer already known. Only an optimization:
        // a repeat probe lands on the same outcome, so no correctness rests
        // on the order. A key with both a point op and a merge op is still
        // probed twice, since the point op and the first merge op are seen as
        // distinct writes here; `write_matches_committed` refuses any key
        // carrying a merge op, so both probes land on the same outcome.
        if let Some(observed_seq) = checks.writes_at {
            // Borrows the batch and allocates nothing.
            let replaced = checks.blind_merges_commute.then(|| Replaced::of(ops));
            // Whether anything committed since the snapshot, which only an
            // exempt put has any use for: with no exempt key, or nothing
            // newer, no put is looked up.
            let landed_since = !checks.exempt.is_empty() && ceiling > observed_seq;
            let mut last_merged: Option<&[u8]> = None;
            let first_op = reads + checks.ranges.len();
            for (at, op) in ops.iter().enumerate() {
                let mark = early.mark(first_op + at);
                let (key, mine) = match op {
                    WriteBatchOp::Put { key, .. } => (key, Access::Put),
                    WriteBatchOp::Delete { key } => (key, Access::Delete),
                    WriteBatchOp::Merge { key, .. } => {
                        if last_merged == Some(key.as_slice()) {
                            continue;
                        }
                        last_merged = Some(key.as_slice());
                        (key, Access::Merge)
                    }
                    // A transaction never carries a range delete.
                    WriteBatchOp::DeleteRange { .. } => continue,
                };
                // The caller exempted this key from validation, so a newer
                // write of it is no conflict and its lookup is not worth
                // making. A search of a sorted list, no hash and no
                // allocation, and an empty list unless a key classifier
                // named keys.
                // vertexia: O(log exempt keys) per written key; a merge-join
                // over the sorted point and merge runs is O(1) if a very
                // large exempt list ever shows in a profile.
                if checks
                    .exempt
                    .binary_search_by(|exempt| exempt.as_slice().cmp(key))
                    .is_ok()
                {
                    // The one lookup an exempt put can cost: the key names
                    // its bytes, so a put beside different ones breaks the
                    // contract and the commit is refused loudly.
                    if landed_since
                        && let WriteBatchOp::Put { value, .. } = op
                        && landed(key, mark)?
                        && self.content_mismatch(key, value, observed_seq, view)?
                    {
                        tracing::error!(
                            "a content-addressed key was put with bytes that differ from \
                             the bytes it holds; the commit was refused"
                        );
                        return Err(crate::Error::ContentMismatch.into_io_error());
                    }
                    continue;
                }
                // A written key the transaction also read was validated above,
                // at the read's anchor and without the elision below. A
                // presence-only read does not stand for the write, so that
                // key goes on to the check below.
                if Self::read_stands_for(checks, key) {
                    continue;
                }
                // Clean at the horizon and nothing above it: clean, or, for a
                // blind merge only operands landed on, commuting.
                if !landed(key, mark)? {
                    if mark == Mark::Commuted {
                        merges_commuted += 1;
                    }
                    continue;
                }
                match self.check_write(
                    key,
                    mine,
                    observed_seq,
                    replaced.as_ref(),
                    view,
                    |theirs| self.write_matches_committed(key, ops, view, theirs),
                )? {
                    WriteCheck::Clean => {}
                    WriteCheck::Commuted => merges_commuted += 1,
                    WriteCheck::Elided => writes_elided += 1,
                    WriteCheck::Conflict { seq, theirs } => {
                        if let Some(s) = self.statistics() {
                            s.add(Ticker::CommitConflictsOnWrite, 1);
                        }
                        return Ok(Verdict::Conflict(Conflict::new(
                            key.clone(),
                            mine,
                            theirs,
                            observed_seq,
                            seq,
                        )));
                    }
                }
            }
        }
        Ok(Verdict::Accept {
            merges_commuted,
            writes_elided,
        })
    }
}
