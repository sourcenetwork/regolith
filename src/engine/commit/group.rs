//! The decide stage of a commit group: every transaction member is validated
//! in group order against the view plus the writes of the members before it,
//! and turned into the batch it lands as, or into a request that writes
//! nothing.
//!
//! The earlier members' writes are not in the view: nothing is applied before
//! the group's record is in the log, so a failed group leaves nothing behind
//! (G2). They are put instead into a small memtable of their own, the overlay,
//! at the sequences they will take, and the member is validated against a view
//! whose newest source is that overlay. Every check a transaction committing
//! alone runs then sees exactly what it would see had the earlier members
//! committed one at a time first: the keys they wrote stand for them, and the
//! rules that refine a conflict per key (identical-write elision, blind merges
//! that commute, value and projected reads, content-addressed puts) judge
//! their writes as they judge any committed one. This is the model's rule,
//! `Decide` in `GroupCommit.tla` and `group_eq_serial` in `GroupCommit.lean`,
//! with the per-key test the transaction layer chose.
//!
//! The sequences are known before they are drawn: the pipeline mutex is held,
//! and every sequence is drawn under it, so the group's first sequence is the
//! one after `latest_seq` and the members take theirs in group order.
//!
//! A plain write in the group is not validated; it behaves as an accepted
//! member, so a transaction behind it in the group conflicts with it. Members
//! after the last transaction need no overlay, and a group with no
//! transaction never builds one.

use std::io;
use std::sync::Arc;
use std::sync::atomic::Ordering;

use super::super::memtable::MemTable;
use super::super::{ReadView, RegolithEngine};
use super::append::AppendOrder;
use super::txn::{TxnRequest, Verdict};
use super::{GroupTicket, WriteRequest};
use crate::perf_context::PerfLevel;

/// The earlier members' writes, at the sequences they will take, as the
/// newest source of a view.
struct Overlay {
    view: ReadView,
}

impl Overlay {
    /// A view of `base` under an empty memtable.
    fn over(engine: &RegolithEngine, base: &ReadView) -> io::Result<Self> {
        let mut frozen = Vec::with_capacity(base.frozen.len() + 1);
        frozen.extend(base.frozen.iter().cloned());
        frozen.push(Arc::clone(&base.active));
        Ok(Self {
            view: ReadView {
                active: Arc::new(MemTable::new(&engine.memtable_config)?),
                frozen,
                version: Arc::clone(&base.version),
            },
        })
    }

    /// Put `request`'s writes into the overlay from sequence `seq` on.
    fn add(&self, request: &WriteRequest, mut seq: u64) {
        let memtable: &MemTable = &self.view.active;
        let mut hint = memtable.insert_hint();
        request.apply(memtable, &mut hint, &mut seq);
    }
}

impl RegolithEngine {
    /// Decide every transaction member of `group` in group order against
    /// `view`, which holds every committed write.
    ///
    /// A member that validates has its appends numbered and becomes the batch
    /// it lands as; one that does not, or whose own check failed, becomes a
    /// request that writes nothing. Either way its ticket records the
    /// verdict. `Err` is a failure of the whole group: a caller's code
    /// panicked in the ordered step, which latched the database, or the
    /// overlay could not be built.
    pub(super) fn decide(&self, group: &mut [GroupTicket], view: &ReadView) -> io::Result<()> {
        let Some(last_txn) = group
            .iter()
            .rposition(|ticket| matches!(ticket.request, WriteRequest::Txn(_)))
        else {
            return Ok(());
        };
        let mut overlay: Option<Overlay> = None;
        // The group's sequences, drawn later under this same mutex, start
        // here; `run_group` checks they did.
        let mut next_seq = self.latest_seq.load(Ordering::Acquire) + 1;
        // Made for the first member that appends: most groups have none.
        let mut order: Option<AppendOrder> = None;
        for (at, ticket) in group.iter_mut().enumerate().take(last_txn + 1) {
            match std::mem::replace(&mut ticket.request, WriteRequest::Idle) {
                WriteRequest::Txn(txn) => {
                    let against = overlay.as_ref().map_or(view, |overlay| &overlay.view);
                    let perf = txn.perf;
                    let decide = || self.decide_member(txn, against, next_seq - 1, &mut order);
                    let (request, verdict) = if perf == PerfLevel::Disable {
                        decide()?
                    } else {
                        let (decided, counted) = crate::perf_context::on_behalf(perf, decide);
                        ticket.perf = Some(Box::new(counted));
                        decided?
                    };
                    ticket.request = request;
                    ticket.verdict = Some(verdict);
                }
                plain => ticket.request = plain,
            }
            let ops = ticket.request.op_count();
            // The last transaction's own writes have no later member to judge.
            if at < last_txn && ops > 0 {
                if overlay.is_none() {
                    overlay = Some(Overlay::over(self, view)?);
                }
                if let Some(overlay) = &overlay {
                    overlay.add(&ticket.request, next_seq);
                }
            }
            next_seq += ops;
        }
        Ok(())
    }

    /// Decide one transaction against `view`, whose newest sequence is
    /// `ceiling`: validate it, then number its appends in `order`.
    fn decide_member(
        &self,
        txn: TxnRequest,
        view: &ReadView,
        ceiling: u64,
        order: &mut Option<AppendOrder>,
    ) -> io::Result<(WriteRequest, io::Result<Verdict>)> {
        let TxnRequest {
            checks,
            mut ops,
            appends,
            durability,
            early,
            ..
        } = txn;
        let verdict = match self.validate(&checks, &ops, &early, view, ceiling) {
            Ok(Verdict::Conflict(conflict)) => {
                return Ok((WriteRequest::Idle, Ok(Verdict::Conflict(conflict))));
            }
            Ok(accept) => accept,
            Err(err) => return Self::member_failed(err),
        };
        // Positions are taken after validation and never before, so a member
        // that aborted took none (RED AssignBeforeValidation).
        if !appends.is_empty()
            && let Err(err) = order
                .get_or_insert_with(AppendOrder::default)
                .number(self, view, appends, &mut ops)
        {
            return Self::member_failed(err);
        }
        // A read-only member validated and takes no sequence.
        if ops.is_empty() {
            return Ok((WriteRequest::Idle, Ok(verdict)));
        }
        Ok((
            WriteRequest::Batch {
                ops,
                durability,
                disable_wal: false,
            },
            Ok(verdict),
        ))
    }

    /// A member whose own check failed writes nothing and learns why, unless a
    /// caller's code panicked in the ordered step: that latched the database,
    /// and the whole group fails with it.
    fn member_failed(err: io::Error) -> io::Result<(WriteRequest, io::Result<Verdict>)> {
        if crate::Error::callback_panic_of(&err).is_some() {
            return Err(err);
        }
        Ok((WriteRequest::Idle, Err(err)))
    }
}
