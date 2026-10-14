//! Validation outside the pipeline mutex (plan 4.4, `early_check_split` in
//! `GroupCommit.lean`).
//!
//! Before a transaction joins a commit group it samples the read horizon `h`
//! and checks every item of its commit (each read, each validated scan, each
//! written key) against the versions committed up to `h`, on its own thread
//! and outside the mutex. Under the mutex the leader then looks only above
//! `h`: an item nothing landed on above `h` keeps the verdict it had at `h`,
//! and an item something did land on is checked in full, exactly as a commit
//! checked alone would check it. Splitting the check at `h` decides as one
//! check of every version does, per item and so for the whole commit.
//!
//! Why the split is exact, item by item:
//! - The horizon is sampled before the view is loaded, so the view holds
//!   every version at or below `h`; a version compaction dropped was shadowed
//!   by a newer one, which the view holds or which lies above `h`.
//! - An item marked clean had no version newer than its read in that view.
//!   If nothing lands on it above `h` either, a check of every version finds
//!   nothing newer: clean. A blind merge marked as commuting saw only
//!   operands; with no replacement above `h` it still commutes.
//! - An item with a newer version is decided under the mutex in full, with
//!   one exception, a conflict that no later version can undo: a read
//!   validated by sequence, and a validated scan, conflict with any newer
//!   version, and a blind merge with any newer replacement, so the
//!   transaction aborts at once, without queueing (the model's early abort).
//!   It aborts only when every item before it is clean, so the conflict it
//!   names is the first one in the commit's order, as a check of every item
//!   would name it. Every version the view holds was applied, so its group
//!   committed: the abort sorts after a commit the transaction did not see.
//! - Identical-write elision, value reads and content-addressed puts can be
//!   undone by a later write of the same bytes, so for them a newer version
//!   only marks the item for the full check.
//!
//! What lands above `h` is found in the memtables alone whenever the
//! version's `last_seq` is at or below `h`: a flushed or ingested table holds
//! no sequence above the `last_seq` it raised, so every version above `h` is
//! still in a memtable the view holds, the group's overlay included. That is
//! the work left under the mutex: one memtable probe per item.

use std::io;

use super::super::lookup_key::LookupKey;
use super::super::{ReadView, RegolithEngine, ValidationSet};
use super::replaced::Replaced;
use super::terminator::Landed;
use crate::statistics::Ticker;
use crate::{Access, Conflict, WriteBatchOp};

/// What the check at the horizon found for one item.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Mark {
    /// Nothing newer than the item's read up to the horizon.
    Clean,
    /// A blind merge that only operands landed on up to the horizon.
    Commuted,
    /// A newer version the full check under the mutex has to judge.
    Dirty,
}

/// The check at the horizon, carried into the commit group.
#[derive(Debug)]
pub(crate) struct Early {
    /// The read horizon the check ran at.
    pub(crate) horizon: u64,
    /// One mark per item: the reads, then the validated scans, then every
    /// operation of the batch, in that order. Empty when every item is
    /// clean, which is what a commit nothing landed under looks like, so the
    /// common case allocates nothing.
    marks: Vec<Mark>,
}

impl Early {
    /// The mark of item `at`, counted as `marks` is.
    pub(crate) fn mark(&self, at: usize) -> Mark {
        self.marks.get(at).copied().unwrap_or(Mark::Clean)
    }
}

/// The early check's answer: a conflict found at the horizon, or the marks
/// the leader finishes from.
pub(crate) enum EarlyVerdict {
    Conflict(Conflict),
    Marks(Early),
}

/// Records marks, allocating only once a mark is not clean.
struct Marker {
    marks: Vec<Mark>,
    total: usize,
    /// An item before the current one is dirty, so a conflict found now may
    /// not be the first in the commit's order and is left to the full check.
    dirty_before: bool,
}

impl Marker {
    fn set(&mut self, at: usize, mark: Mark) {
        if mark == Mark::Clean {
            return;
        }
        if self.marks.is_empty() {
            self.marks = vec![Mark::Clean; self.total];
        }
        self.marks[at] = mark;
        self.dirty_before |= mark == Mark::Dirty;
    }
}

impl RegolithEngine {
    /// Check `checks` and `ops` against the versions committed up to the
    /// current read horizon, outside the pipeline mutex. Returns the conflict
    /// that settles the commit at once, or the marks the leader finishes the
    /// check from.
    pub(super) fn check_early(
        &self,
        checks: &ValidationSet,
        ops: &[WriteBatchOp],
    ) -> io::Result<EarlyVerdict> {
        // Sampled before the view is loaded: the view then holds every
        // version at or below it.
        let horizon = self.visible_seq.visible();
        let reads = checks.reads.len();
        let ranges = checks.ranges.len();
        let mut marker = Marker {
            marks: Vec::new(),
            total: reads + ranges + ops.len(),
            dirty_before: false,
        };
        let newest_read = checks.reads.iter().map(|r| r.observed_seq);
        let newest_range = checks.ranges.iter().map(|r| r.observed_seq);
        // Nothing committed since any item was read: every item is clean,
        // and no view is loaded.
        if newest_read
            .chain(newest_range)
            .chain(checks.writes_at.filter(|_| !ops.is_empty()))
            .all(|observed| horizon <= observed)
        {
            return Ok(EarlyVerdict::Marks(Early {
                horizon,
                marks: Vec::new(),
            }));
        }
        let view = self.view.load();
        for (at, check) in checks.reads.iter().enumerate() {
            if horizon <= check.observed_seq {
                continue;
            }
            let Some((seq, theirs)) = self.latest_version_in_view(&check.key, &view)? else {
                continue;
            };
            if seq <= check.observed_seq {
                continue;
            }
            let final_conflict =
                matches!(check.rule, super::super::ReadRule::Seq) && !check.presence_only();
            if final_conflict && !marker.dirty_before {
                if let Some(s) = self.statistics() {
                    s.add(Ticker::CommitConflictsOnRead, 1);
                }
                return Ok(EarlyVerdict::Conflict(Conflict::new(
                    check.key.clone(),
                    check.access,
                    theirs,
                    check.observed_seq,
                    seq,
                )));
            }
            marker.set(at, Mark::Dirty);
        }
        for (at, range) in checks.ranges.iter().enumerate() {
            if horizon <= range.observed_seq {
                continue;
            }
            if let Some((key, seq, theirs)) =
                self.written_in_range(&range.lo, &range.hi, range.observed_seq, &view)?
            {
                if !marker.dirty_before {
                    if let Some(s) = self.statistics() {
                        s.add(Ticker::CommitConflictsOnRead, 1);
                    }
                    return Ok(EarlyVerdict::Conflict(Conflict::new(
                        key,
                        Access::ScannedRange,
                        theirs,
                        range.observed_seq,
                        seq,
                    )));
                }
                marker.set(reads + at, Mark::Dirty);
            }
        }
        if let Some(observed_seq) = checks.writes_at
            && horizon > observed_seq
        {
            let replaced = checks.blind_merges_commute.then(|| Replaced::of(ops));
            let mut last_merged: Option<&[u8]> = None;
            // The same items, skipped the same way, as the full check.
            for (at, op) in ops.iter().enumerate() {
                let at = reads + ranges + at;
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
                    WriteBatchOp::DeleteRange { .. } => continue,
                };
                if checks
                    .exempt
                    .binary_search_by(|exempt| exempt.as_slice().cmp(key))
                    .is_ok()
                {
                    // Only an exempt put is ever looked up, for its contract.
                    if matches!(op, WriteBatchOp::Put { .. })
                        && self.landed_above_horizon(key, observed_seq, &view, false)?
                    {
                        marker.set(at, Mark::Dirty);
                    }
                    continue;
                }
                if Self::read_stands_for(checks, key) {
                    continue;
                }
                let blind =
                    mine == Access::Merge && replaced.as_ref().is_some_and(|r| !r.contains(key));
                if blind {
                    match self.landed_above(key, observed_seq, &view)? {
                        Landed::Nothing => {}
                        Landed::Operands => marker.set(at, Mark::Commuted),
                        Landed::Replaced { seq, kind } if !marker.dirty_before => {
                            if let Some(s) = self.statistics() {
                                s.add(Ticker::CommitConflictsOnWrite, 1);
                            }
                            return Ok(EarlyVerdict::Conflict(Conflict::new(
                                key.clone(),
                                mine,
                                kind,
                                observed_seq,
                                seq,
                            )));
                        }
                        Landed::Replaced { .. } => marker.set(at, Mark::Dirty),
                    }
                } else if self.landed_above_horizon(key, observed_seq, &view, false)? {
                    marker.set(at, Mark::Dirty);
                }
            }
        }
        Ok(EarlyVerdict::Marks(Early {
            horizon,
            marks: marker.marks,
        }))
    }

    /// Whether a read of `key` in `checks` is validated in place of the write:
    /// every read but a presence-only one.
    pub(super) fn read_stands_for(checks: &ValidationSet, key: &[u8]) -> bool {
        checks
            .reads
            .binary_search_by(|read| read.key.as_slice().cmp(key))
            .is_ok_and(|at| !checks.reads[at].presence_only())
    }

    /// Whether anything landed on `key` above `horizon` in `view`: a point
    /// version or a covering range delete. With `memtables_only` the tables
    /// are not consulted, which is exact when the version's `last_seq` is at
    /// or below `horizon` (see the module docs).
    pub(super) fn landed_above_horizon(
        &self,
        key: &[u8],
        horizon: u64,
        view: &ReadView,
        memtables_only: bool,
    ) -> io::Result<bool> {
        if !memtables_only {
            return Ok(self
                .latest_version_in_view(key, view)?
                .is_some_and(|(seq, _)| seq > horizon));
        }
        let lk = LookupKey::from_prefixed(key, u64::MAX);
        Ok(std::iter::once(&view.active)
            .chain(view.frozen.iter().rev())
            .any(|mt| {
                mt.latest_version(&lk).is_some_and(|(seq, _)| seq > horizon)
                    || mt.covering_range_tombstone_seq(key, u64::MAX) > horizon
            }))
    }
}
