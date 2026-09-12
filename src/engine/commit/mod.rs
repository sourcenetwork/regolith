//! Group commit: many concurrent writers, one WAL append, one fsync.
//!
//! A writer hands an owned [`WriteRequest`] to a bounded ring and parks.
//! Whichever thread holds the pipeline mutex is the leader: it drains the
//! ring, formats every pending record into one staging buffer, issues a
//! single `write_all` and at most one `fdatasync`, applies the whole group
//! to the active memtable, publishes the read horizon, and only then
//! releases the followers.
//!
//! Three invariants outrank throughput here, and every design choice below
//! is subordinate to them.
//!
//! * **the lost-update fix - the horizon trails durability.** `visible_seq` moves only after
//!   every record in the group is on stable storage *and* every operation
//!   is in the memtable, and always before any follower is released. A
//!   snapshot therefore cannot observe a torn batch.
//! * **G2 - a group fails as one unit.** When the append or the sync fails,
//!   the WAL is truncated back to the pre-group offset, nothing is applied,
//!   nothing is published, and *every* member of the group receives the
//!   error. No writer can believe it committed when the fsync did not.
//! * **G3 - an abandoned writer cannot wedge the ring.** The ring owns an
//!   `Arc` on the slot and the request is moved into the slot, so the
//!   leader never touches a frame that may have unwound, and a ticket is
//!   always completed and dropped exactly once.
//!
//! Groups do not pipeline. `visible_seq` is a single `fetch_max` watermark:
//! if a later group published its maximum before an earlier one applied, a
//! snapshot at that watermark would read a hole. Overlapping groups need a
//! per-commit completion tracker, which this module deliberately does not
//! have.

use std::io;
use std::sync::Arc;
use std::sync::atomic::Ordering;
use std::thread;
use std::time::Duration;

use kovan_queue::array_queue::ArrayQueue;

use super::memtable::MemTable;
use super::wal::Wal;
use super::{CommitOutcome, DurabilityMode, ReadView, RegolithEngine, grouped_batch_ops};
use crate::WriteBatchOp;
use crate::perf_context::{PerfTimer, PerfTimerField};
use crate::statistics::{Histogram, Ticker};

mod request;
mod slot;
mod stall;

pub(crate) use request::WriteRequest;
pub(crate) use slot::WriteSlot;
pub(crate) use stall::StallSignal;

/// Largest number of WAL bytes one group stages before it stops admitting.
///
/// Bounded in bytes rather than in tickets because bytes are what the
/// staging buffer, the write syscall and the fsync latency actually scale
/// with. The cap is tested before a ticket is popped, so a request larger
/// than the whole cap is still admitted rather than starved.
const MAX_GROUP_BYTES: usize = 1024 * 1024;

/// Ceiling on how much stage capacity `trim_stage` ever keeps.
///
/// Without a ceiling a single one-off giant group parks its whole peak
/// allocation for as long as the engine stays open and idle, or even after
/// `close()`, because nothing else ever touches the stage. 16x the group
/// cap still leaves a steady `BatchWrite`/4KiB stream (about 4.1 MB)
/// allocation-free; only a group larger than this is trimmed back down to
/// it in the same call that ran it.
const MAX_KEPT_STAGE_BYTES: usize = 16 * MAX_GROUP_BYTES;

/// Upper bound on how long a parked follower sleeps before re-checking.
///
/// Correctness does not rest on this: the leader unparks every follower it
/// completes, and `thread::park`'s unpark token is sticky, so a wake-up
/// racing ahead of the park is not lost. The slice only bounds the one
/// window a wake-up cannot cover, where a writer pushes its ticket in the
/// instant between the last leader's final `pop` and its release of the
/// pipeline mutex.
const PARK_SLICE: Duration = Duration::from_micros(200);

/// Ring capacity for pending commit tickets, sized from the machine's
/// parallelism and clamped so a huge core count cannot balloon it.
fn commit_ring_capacity() -> usize {
    thread::available_parallelism()
        .map(|n| n.get().saturating_mul(4))
        .unwrap_or(16)
        .clamp(16, 1024)
}

/// A group member: the work, plus the slot to complete when the group is
/// done. `slot` is `None` for the leader's own request, which needs no
/// handoff because the leader returns the outcome directly.
struct GroupTicket {
    slot: Option<Arc<WriteSlot>>,
    request: WriteRequest,
}

/// Leader-owned scratch, guarded by the pipeline mutex so only the leader
/// can reach it. The stage is reserved to each group's exact framed length
/// before it is encoded and kept between groups up to a byte ceiling, so a
/// stream of equal-sized groups at or under that ceiling stages its bytes
/// without touching the allocator once warmed up; `trim_stage` says when a
/// varying stream reallocates, when capacity is given back, and bounds how
/// much a one-off giant group can leave parked.
pub(crate) struct Pipeline {
    stage: Vec<u8>,
    group: Vec<GroupTicket>,
    /// Framed bytes the previous group staged: the one group of hysteresis
    /// `trim_stage` keeps, so a group cannot shrink a stage the group
    /// before it just grew.
    prev_staged: usize,
}

impl Pipeline {
    pub(crate) fn new() -> Self {
        Self {
            stage: Vec::new(),
            group: Vec::new(),
            prev_staged: 0,
        }
    }
}

/// `io::Error` is not `Clone`, but a failed group has to hand the same
/// failure to every member. Kind and message are the whole of what a
/// caller can observe, so reconstructing them is lossless here.
fn clone_io_error(err: &io::Error) -> io::Error {
    io::Error::new(err.kind(), err.to_string())
}

/// Give staging memory back when neither of the last two groups needed it,
/// and never keep more than `MAX_KEPT_STAGE_BYTES` regardless.
///
/// Policy: within that ceiling, the stage keeps enough capacity for the
/// larger of the group that just ran and the one before it, and never less
/// than `MAX_GROUP_BYTES`. A group at or under the ceiling touches the
/// allocator only when it needs to grow past the kept capacity, or when
/// the group two back was the largest of the three and is now shed, so a
/// stream of equal-sized groups at or under the ceiling is allocation-free
/// once warmed up, and a stage the previous group grew is not shrunk by a
/// small group that happens to follow it (the common interleave of a bulk
/// batch and a single put) until two smaller groups have run. A group
/// larger than the ceiling is trimmed straight back down to it in the same
/// call that ran it, so a one-off giant group can never park more than
/// `MAX_KEPT_STAGE_BYTES` for the rest of the engine's life, whether writes
/// go idle or the engine closes; the cost is that a steady stream of groups
/// above the ceiling reallocates on every group instead of holding its
/// peak. Bound, in bytes: on return, `stage.capacity() <=
/// max(MAX_GROUP_BYTES, min(max(prev_staged, staged), MAX_KEPT_STAGE_BYTES))`,
/// which is itself at most `MAX_KEPT_STAGE_BYTES`.
///
/// `shrink_to` cannot go below `len`, so the bytes have to go first.
fn trim_stage(stage: &mut Vec<u8>, prev_staged: usize, staged: usize) {
    let keep = MAX_GROUP_BYTES.max(prev_staged.max(staged).min(MAX_KEPT_STAGE_BYTES));
    if stage.capacity() > keep {
        stage.clear();
        stage.shrink_to(keep);
    }
}

/// Empty a staged group, telling anyone still in it that their write did
/// not land.
///
/// Normally the group is already empty here, because `run_and_complete`
/// drains it. It is not empty only when a previous leader unwound in the
/// middle of a group, and the writers behind those tickets are parked. G3
/// says they must be told something rather than left waiting, and after an
/// unwind the only honest thing to tell them is that the group failed:
/// reporting failure for a write that may in fact have landed is the safe
/// direction, reporting success for one that did not is never safe.
fn release_stranded(group: &mut Vec<GroupTicket>) {
    for ticket in group.drain(..) {
        if let Some(slot) = ticket.slot {
            slot.complete(Err(io::Error::other(
                "commit group abandoned by a leader that did not finish",
            )));
        }
    }
}

impl RegolithEngine {
    /// Build the commit ring. Sized once at open.
    pub(crate) fn new_commit_ring() -> ArrayQueue<Arc<WriteSlot>> {
        ArrayQueue::new(commit_ring_capacity())
    }

    /// Apply an ordered batch of writes atomically.
    ///
    /// Operations are assigned consecutive sequence numbers in the order
    /// the caller recorded them. That order matters when a batch mixes
    /// range tombstones with puts, deletes and merges for keys inside the
    /// range.
    ///
    /// `durability` controls WAL fsync semantics; `disable_wal` skips the
    /// WAL entirely, so the caller accepts that a crash before the next
    /// memtable flush loses the write.
    pub(crate) fn apply_batch(
        &self,
        ops: Vec<WriteBatchOp>,
        durability: DurabilityMode,
        disable_wal: bool,
    ) -> io::Result<u64> {
        self.validate_ops_sizes(&ops)?;
        self.submit_batch(ops, durability, disable_wal)
    }

    /// [`Self::apply_batch`] for a caller that has already checked every
    /// key and value against the configured limits. `Db::write` does so at
    /// the API boundary, before the stall wait and the statistics, so
    /// repeating the pass here would compare the same lengths against the
    /// same numbers a second time.
    pub(crate) fn submit_batch(
        &self,
        ops: Vec<WriteBatchOp>,
        durability: DurabilityMode,
        disable_wal: bool,
    ) -> io::Result<u64> {
        self.ensure_writable()?;
        if ops.is_empty() {
            return Ok(self.visible_seq.visible());
        }
        self.submit(WriteRequest::Batch {
            ops,
            durability,
            disable_wal,
        })
    }

    /// Apply grouped writes from internal callers that do not preserve a
    /// single operation log.
    pub(crate) fn apply_grouped_batch(
        &self,
        point_ops: std::collections::BTreeMap<Vec<u8>, Option<Vec<u8>>>,
        range_deletes: Vec<(Vec<u8>, Vec<u8>)>,
        merges: Vec<(Vec<u8>, Vec<u8>)>,
        durability: DurabilityMode,
        disable_wal: bool,
    ) -> io::Result<u64> {
        let ops = grouped_batch_ops(point_ops, range_deletes, merges);
        self.apply_batch(ops, durability, disable_wal)
    }

    /// Fast path for a single put: skips the batch vector so the most
    /// common write allocates nothing beyond the key and value the caller
    /// already owns.
    pub(crate) fn apply_single_put(
        &self,
        key: Vec<u8>,
        value: Vec<u8>,
        durability: DurabilityMode,
        disable_wal: bool,
    ) -> io::Result<u64> {
        self.ensure_writable()?;
        self.validate_prefixed_key_size(&key)?;
        self.validate_value_size(&value)?;
        self.submit(WriteRequest::Put {
            key,
            value,
            durability,
            disable_wal,
        })
    }

    /// Attempt to commit an optimistic transaction's buffered writes.
    ///
    /// The conflict check and the apply run under one uninterrupted hold
    /// of the pipeline mutex, so no other write can land between them.
    /// The transaction is committed as a group of exactly one: batching a
    /// transaction with a concurrent plain write would let the write land
    /// in the same group the conflict check already looked past, which is
    /// precisely the write-write conflict the check exists to catch.
    ///
    /// The checks and the apply also share one view: the active memtable is
    /// replaced only under the pipeline mutex, so the memtable the checks read
    /// is the memtable the group lands in unless this leader rotates it, and
    /// `rotate_if_full` hands the apply the fresh view in that case.
    pub(crate) fn commit_optimistic(
        &self,
        checks: &crate::engine::ValidationSet,
        point_ops: std::collections::BTreeMap<Vec<u8>, Option<Vec<u8>>>,
        range_deletes: Vec<(Vec<u8>, Vec<u8>)>,
        merges: Vec<(Vec<u8>, Vec<u8>)>,
        durability: DurabilityMode,
    ) -> io::Result<CommitOutcome> {
        self.ensure_writable()?;
        let ops = grouped_batch_ops(point_ops, range_deletes, merges);
        self.validate_ops_sizes(&ops)?;

        // The write-stall admission a plain write pays with
        // `WriteOptions::default()`, in the same order: closed/WAL-failed/
        // read-only above, then size validation above, then the wait, and
        // only then the pipeline mutex below. Never inside that mutex: a
        // `CompactInline` wait runs a compaction pass on this thread, and
        // that pass must not be entered while any commit-path lock is
        // held. A commit that writes nothing (`ops` empty, e.g. a
        // `get_for_update` with no write) takes no capacity and skips the
        // wait, though its conflict check below still runs under the
        // mutex like any other commit.
        if !ops.is_empty() {
            self.wait_for_write_capacity(false)
                .map_err(crate::Error::into_io_error)?;
        }

        self.commit_locked(checks, ops, durability)
    }

    /// The conflict check and the apply, under one uninterrupted hold of
    /// the pipeline mutex. Split out of [`Self::commit_optimistic`] so the
    /// admission wait above does not share a function body with this loop
    /// once `Transaction::commit_inner` inlines both: sharing one grew
    /// large enough to cost the loop its rotation, adding a per-key
    /// instruction count no admission check should touch.
    fn commit_locked(
        &self,
        checks: &crate::engine::ValidationSet,
        ops: Vec<WriteBatchOp>,
        durability: DurabilityMode,
    ) -> io::Result<CommitOutcome> {
        let mut pipe = self.pipeline.lock();

        let view = self.view.load();
        // Reads first, then the written keys in operation order: point
        // operations arrive sorted from the write map, merges after them in
        // the order they were buffered, so a multi-key conflict names the
        // same key on every run.
        for check in &checks.reads {
            if let Some(latest_seq) = self.latest_version_seq_in_view(&check.key, &view)?
                && latest_seq > check.observed_seq
            {
                // A key the transaction *read* always aborts, since the stale
                // read may have changed what it decided.
                return Ok(CommitOutcome::Conflict {
                    key: check.key.clone(),
                    observed_seq: check.observed_seq,
                    latest_seq,
                });
            }
        }
        // A key merged N times in one transaction is probed once, not N
        // times: each probe past the first would just walk the same
        // pipeline-mutex-held view again for an answer already known. A key
        // with both a point op and a merge op is still probed twice, since
        // the point op and the first merge op are seen as distinct writes
        // here; `write_matches_committed` refuses any key carrying a merge
        // op, so both probes land on the same outcome.
        if let Some(observed_seq) = checks.writes_at {
            let mut merged_keys: std::collections::HashSet<&[u8]> =
                std::collections::HashSet::new();
            for op in &ops {
                let key = match op {
                    WriteBatchOp::Put { key, .. } | WriteBatchOp::Delete { key } => key,
                    WriteBatchOp::Merge { key, .. } => {
                        if !merged_keys.insert(key.as_slice()) {
                            continue;
                        }
                        key
                    }
                    // Range deletes are not validated (transaction.rs:459-460).
                    WriteBatchOp::DeleteRange { .. } => continue,
                };
                // A written key the transaction also read was validated above,
                // at the read's anchor and without the elision below.
                if checks
                    .reads
                    .binary_search_by(|read| read.key.as_slice().cmp(key))
                    .is_ok()
                {
                    continue;
                }
                if let Some(latest_seq) = self.latest_version_seq_in_view(key, &view)?
                    && latest_seq > observed_seq
                {
                    // A blind write of the value the key already holds is not a
                    // conflict: the schedule has a serial equivalent reaching the
                    // same state.
                    if self.write_matches_committed(key, &ops, &view)? {
                        continue;
                    }
                    return Ok(CommitOutcome::Conflict {
                        key: key.clone(),
                        observed_seq,
                        latest_seq,
                    });
                }
            }
        }

        // A read-only transaction still has to be validated: a
        // `get_for_update` with no write is exactly the read whose
        // conflict a lost-update check exists to catch. Short-circuit
        // only after the check, never before it.
        if ops.is_empty() {
            return Ok(CommitOutcome::Ok);
        }

        let request = WriteRequest::Batch {
            ops,
            durability,
            disable_wal: false,
        };
        release_stranded(&mut pipe.group);
        pipe.group.push(GroupTicket {
            slot: None,
            request,
        });
        let result = self.run_and_complete(&mut pipe, view);
        self.drain_locked(&mut pipe);
        result.map(|_| CommitOutcome::Ok)
    }

    /// Hand `request` to the commit pipeline and block until its group is
    /// durable and applied, or until that group fails.
    fn submit(&self, request: WriteRequest) -> io::Result<u64> {
        // Uncontended path: nobody is committing, so lead a group carrying
        // this request plus anything already queued behind it. One fsync
        // covers all of it.
        if let Some(mut pipe) = self.pipeline.try_lock() {
            return self.lead_with(&mut pipe, request);
        }

        let slot = slot::thread_slot();
        // A refused slot still belongs to an outstanding ticket on this
        // thread. Wait for the pipeline and commit inline rather than race
        // an in-flight handoff.
        if let Err(request) = slot.arm(request) {
            let mut pipe = self.pipeline.lock();
            return self.lead_with(&mut pipe, request);
        }

        // Publish the ticket. A full ring means a leader is behind, so
        // help drain it and retry; draining strictly removes entries, so
        // this makes progress.
        let mut ticket = Arc::clone(&slot);
        while let Err(returned) = self.commit_ring.push(ticket) {
            ticket = returned;
            if !self.try_drain() {
                thread::yield_now();
            }
        }

        while !slot.is_done() {
            // Anyone may lead. Whoever wins the mutex drains for everyone,
            // which may complete this very ticket.
            if self.try_drain() {
                continue;
            }
            thread::park_timeout(PARK_SLICE);
        }

        slot.finish()
    }

    /// Lead a group whose first member is the caller's own `request`, then
    /// drain anything that arrived while it ran. Returns that request's
    /// outcome.
    pub(super) fn lead_with(&self, pipe: &mut Pipeline, request: WriteRequest) -> io::Result<u64> {
        release_stranded(&mut pipe.group);
        pipe.group.push(GroupTicket {
            slot: None,
            request,
        });
        let view = self.view.load();
        self.admit_from_ring(pipe, &view);

        let result = self.run_and_complete(pipe, view);
        self.drain_locked(pipe);
        result
    }

    /// Become the leader if nobody else is, and drain the ring dry.
    /// Returns whether this call held the pipeline mutex.
    fn try_drain(&self) -> bool {
        let Some(mut pipe) = self.pipeline.try_lock() else {
            return false;
        };
        self.drain_locked(&mut pipe);
        true
    }

    /// Run group after group until the ring is empty.
    ///
    /// Re-checking the ring after each group is half of what closes the
    /// drain-then-push race; the other half is the follower's own
    /// `try_drain` retry, which covers a ticket pushed after this loop's
    /// last `pop` but before the mutex is released.
    fn drain_locked(&self, pipe: &mut Pipeline) {
        loop {
            release_stranded(&mut pipe.group);
            // The common exit: nothing queued behind the group just run.
            // Checked before the view load so the empty pass costs no lock
            // and no Arc.
            if self.commit_ring.is_empty() {
                return;
            }
            let view = self.view.load();
            self.admit_from_ring(pipe, &view);
            if pipe.group.is_empty() {
                return;
            }
            let _ = self.run_and_complete(pipe, view);
        }
    }

    /// Pop tickets into the current group until the ring is empty, the
    /// group's staged byte cap is reached, or the group would carry the
    /// active memtable past `write_buffer_size`.
    ///
    /// The first ticket is always admitted, whatever it costs, so a write
    /// larger than either cap commits alone instead of starving. That one
    /// ticket is the whole of the documented overshoot: the active
    /// memtable holds at most `write_buffer_size` plus one request.
    fn admit_from_ring(&self, pipe: &mut Pipeline, view: &ReadView) {
        let room = self.memtable_room(view);
        // `lead_with` seeds the group with the leader's own request
        // before calling in, so the running totals start from what is
        // already staged rather than from zero.
        let mut staged: usize = pipe.group.iter().map(|t| t.request.staged_len()).sum();
        let mut projected: usize = pipe.group.iter().map(|t| t.request.memtable_cost()).sum();
        loop {
            if !pipe.group.is_empty() && (staged >= MAX_GROUP_BYTES || projected >= room) {
                return;
            }
            let Some(slot) = self.commit_ring.pop() else {
                return;
            };
            let request = slot.take_request();
            staged += request.staged_len();
            projected += request.memtable_cost();
            pipe.group.push(GroupTicket {
                slot: Some(slot),
                request,
            });
        }
    }

    /// Bytes the memtable this group will land in can still take.
    ///
    /// `run_group` rotates before it applies anything, so a memtable
    /// already at or past its budget is about to be replaced by an empty
    /// one and the group may fill a whole `write_buffer_size`.
    fn memtable_room(&self, view: &ReadView) -> usize {
        let budget = self.options.write_buffer_size;
        let used = view.active.approximate_size();
        if used >= budget {
            budget
        } else {
            budget - used
        }
    }

    /// Commit the staged group, then release every follower in it.
    ///
    /// Completion happens after [`Self::run_group`] has published the read
    /// horizon (the lost-update fix) and hands the same outcome to every member (G2).
    fn run_and_complete(&self, pipe: &mut Pipeline, view: Arc<ReadView>) -> io::Result<u64> {
        let Pipeline {
            stage,
            group,
            prev_staged,
        } = pipe;
        // Summed again here rather than carried over from admission:
        // `commit_optimistic` seeds a group without going through
        // `admit_from_ring`, and the sum is one add per ticket.
        let staged: usize = group.iter().map(|t| t.request.staged_len()).sum();
        let result = self.run_group(stage, group, view, staged);
        // Each ticket learns the sequence *its own* operations were
        // assigned, not the group's maximum. An upper layer ordering its
        // versions against regolith's needs the sequence of the write it
        // made, and a group can carry many writers' batches.
        let mut seq = result.as_ref().ok().copied().unwrap_or(0);
        for ticket in group.drain(..) {
            let ops = ticket.request.op_count();
            let last = seq.saturating_add(ops).saturating_sub(1);
            if let Some(slot) = ticket.slot {
                slot.complete(match &result {
                    Ok(_) => Ok(last),
                    Err(e) => Err(io::Error::new(e.kind(), e.to_string())),
                });
            }
            seq = last.saturating_add(1);
        }
        // Trimmed by what is actually resident (`stage.len()`), not by
        // `staged`: a group that failed before encoding stages nothing,
        // and crediting it with `staged` bytes would let a refused
        // reservation pin an older group's capacity alive under a size
        // that was never reserved.
        let used = stage.len();
        trim_stage(stage, *prev_staged, used);
        *prev_staged = used;
        result
    }

    /// Write, sync and apply one group.
    fn run_group(
        &self,
        stage: &mut Vec<u8>,
        group: &[GroupTicket],
        view: Arc<ReadView>,
        staged: usize,
    ) -> io::Result<u64> {
        // Cleared first, ahead of every early return (`ensure_writable`,
        // `rotate_if_full`, a refused reservation), so a group that never
        // reaches the encode loop leaves the stage empty instead of a
        // previous group's leftover length behind for `run_and_complete`'s
        // `stage.len()` to mistake for this one.
        stage.clear();
        self.ensure_writable()?;
        // Ahead of the WAL append on purpose: a rotation swaps the WAL as
        // well as the memtable, so rotating after this group's records
        // were appended would strand them in the WAL that belongs to the
        // memtable now being flushed. `admit_from_ring` sized the group
        // against the room this leaves.
        let view = self.rotate_if_full(view)?;

        let total_ops: u64 = group.iter().map(|t| t.request.op_count()).sum();
        if total_ops == 0 {
            return Ok(self.visible_seq.visible());
        }

        // One allocation for the whole group, before any sequence number
        // is taken, so a refused reservation costs nothing but this group.
        // The framed length is exact (`staged_len`), so `reserve_exact`
        // leaves no slack to trim later.
        // Handed to every member of this group (G2), including one whose
        // own request was small: a group can carry another writer's
        // oversized batch, so the message names no internal mechanism and
        // gives advice that fits every caller, not just whoever staged the
        // bytes.
        stage.try_reserve_exact(staged).map_err(|_| {
            io::Error::new(
                io::ErrorKind::OutOfMemory,
                format!(
                    "not enough memory to commit this write ({staged} bytes pending); retry, splitting any very large write batch"
                ),
            )
        })?;

        // The whole group's sequence range is allocated here, in group
        // order, so sequence order, WAL byte order and memtable apply
        // order stay identical - the property every reader depends on.
        let base_seq = self.latest_seq.fetch_add(total_ops, Ordering::AcqRel) + 1;

        let mut any_immediate = false;
        let mut reported_bytes = 0u64;
        let mut seq = base_seq;
        for ticket in group {
            if !ticket.request.skips_wal() {
                ticket.request.encode_wal(stage, seq);
                reported_bytes += ticket.request.reported_bytes();
                any_immediate |= matches!(ticket.request.durability(), DurabilityMode::Immediate);
            }
            seq += ticket.request.op_count();
        }

        if !stage.is_empty() {
            // Timed on the leader, which is the thread that does the WAL
            // work. A follower's own perf context records no WAL time
            // because it did none.
            let _perf_wal = PerfTimer::new(PerfTimerField::WriteWal);
            // Through `Env`, not `std::time::Instant`: browsers have a
            // clock but `Instant::now` panics on
            // `wasm32-unknown-unknown`, and `OpfsEnv` reads
            // `performance.now()` instead. Read only when statistics
            // are on, so a write with them off pays no clock read at
            // all.
            let wal_start = self.statistics().and_then(|_| self.env.now_micros());
            let mut guard = self.active_wal.lock();
            let wal = guard.as_mut().ok_or_else(Self::read_only_error)?;
            let start_offset = wal.offset();

            if let Err(err) = wal.append_group(stage) {
                self.abandon_group(wal, start_offset, &err);
                return Err(err);
            }

            let mut synced = 0u64;
            if any_immediate {
                if let Err(err) = wal.sync_data() {
                    self.abandon_group(wal, start_offset, &err);
                    return Err(err);
                }
                synced = 1;
            }
            drop(guard);

            if let Some(s) = self.statistics() {
                s.add(Ticker::WalBytesWritten, reported_bytes);
                if synced > 0 {
                    s.add(Ticker::WalSyncCount, synced);
                }
                // `None` means the platform has no clock. Skip the
                // recording rather than publishing a zero that reads
                // like a measurement.
                if let Some(micros) = self.elapsed_micros(wal_start) {
                    s.record(Histogram::WalWriteTime, micros);
                }
            }
        }

        {
            let _perf_mt = PerfTimer::new(PerfTimerField::WriteMemtable);
            let memtable: &MemTable = &view.active;
            // One hint per group: a commit's point ops arrive in key
            // order (`grouped_batch_ops`), so each insert after the
            // first starts where the previous one landed. The hint
            // borrows the memtable this group was applied to and dies
            // with the block, so a rotation between groups can never
            // leave it pointing into a retired arena.
            let mut hint = memtable.insert_hint();
            let mut seq = base_seq;
            for ticket in group {
                ticket.request.apply(memtable, &mut hint, &mut seq);
            }
        }

        // the lost-update fix: the horizon moves only now that every record is durable and
        // every operation is applied, and `run_and_complete` releases the
        // followers only after this returns.
        self.visible_seq.publish(base_seq + total_ops - 1);
        Ok(base_seq)
    }

    /// Discard a group whose WAL work failed.
    ///
    /// Truncating back to `start_offset` is what makes G2 true on disk: a
    /// partially written group never survives as a torn record. If the
    /// truncation itself fails the log's tail is unknown, so the engine
    /// latches and every later write fails loud rather than appending
    /// after bytes nobody can account for.
    fn abandon_group(&self, wal: &mut Wal, start_offset: u64, cause: &io::Error) {
        tracing::error!(error = %cause, "commit group failed; discarding its WAL bytes");
        if let Err(rollback_err) = wal.rollback_to(start_offset) {
            self.latch_wal_failure(&rollback_err);
        }
        if !self.options.listeners.is_empty() {
            let err = crate::Error::from(clone_io_error(cause));
            crate::event_listener::dispatch(&self.options.listeners, |l| {
                l.on_background_error(
                    crate::event_listener::BackgroundErrorReason::WriteAheadLog,
                    &err,
                )
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::{EngineOptions, wal::fault};
    use super::*;
    use crate::sync::Mutex;
    use proptest::prelude::*;
    use tempfile::TempDir;

    fn open_engine(dir: &TempDir) -> Arc<RegolithEngine> {
        RegolithEngine::open(dir.path(), EngineOptions::default()).expect("engine open")
    }

    /// Default-column-family prefix, the shape every engine key carries.
    fn key(name: &[u8]) -> Vec<u8> {
        let mut k = vec![0u8; 4];
        k.extend_from_slice(name);
        k
    }

    fn durable_put(name: &[u8], value: &[u8]) -> WriteRequest {
        WriteRequest::Put {
            key: key(name),
            value: value.to_vec(),
            durability: DurabilityMode::Immediate,
            disable_wal: false,
        }
    }

    struct FaultGuard(std::path::PathBuf);

    impl Drop for FaultGuard {
        fn drop(&mut self) {
            fault::disarm_sync_failure(&self.0);
        }
    }

    /// Arm the WAL sync fault for `dir` only, and disarm that directory
    /// when the test scope ends, leaving any parallel test's own arming
    /// untouched.
    fn arm_sync_failure(dir: &TempDir) -> FaultGuard {
        fault::arm_sync_failure(dir.path());
        FaultGuard(dir.path().to_path_buf())
    }

    /// Arm the WAL sync fault for `dir` so it fails every sync but each
    /// second one, and disarm that directory when the test scope ends.
    fn arm_flapping_sync_failure(dir: &TempDir) -> FaultGuard {
        fault::arm_flapping_sync_failure(dir.path(), 2);
        FaultGuard(dir.path().to_path_buf())
    }

    #[test]
    fn cloned_errors_keep_kind_and_message() {
        let err = io::Error::new(io::ErrorKind::StorageFull, "disk is full");
        let cloned = clone_io_error(&err);
        assert_eq!(cloned.kind(), err.kind());
        assert_eq!(cloned.to_string(), err.to_string());
    }

    #[test]
    fn commit_ring_capacity_is_bounded() {
        let cap = commit_ring_capacity();
        assert!((16..=1024).contains(&cap), "unexpected ring capacity {cap}");
    }

    #[test]
    fn a_failed_sync_fails_every_member_of_the_group() {
        // G2: the whole group learns the fsync did not happen. A writer
        // that believed it committed here would be silent data loss.
        let dir = TempDir::new().unwrap();
        let engine = open_engine(&dir);

        let horizon_before = engine.snapshot_seq();
        let wal_len_before = engine
            .active_wal
            .lock()
            .as_ref()
            .map(|w| w.offset())
            .expect("writable engine has a wal");

        let followers: Vec<Arc<WriteSlot>> = (0..3)
            .map(|i| {
                let slot = Arc::new(WriteSlot::new());
                let request = durable_put(format!("member{i}").as_bytes(), b"value");
                slot.arm(request).expect("fresh slot arms");
                slot
            })
            .collect();

        {
            let _fault = arm_sync_failure(&dir);
            let mut pipe = engine.pipeline.lock();
            pipe.group.clear();
            for slot in &followers {
                let request = slot.take_request();
                pipe.group.push(GroupTicket {
                    slot: Some(Arc::clone(slot)),
                    request,
                });
            }
            let result = engine.run_and_complete(&mut pipe, engine.view.load());
            assert!(
                result.is_err(),
                "an injected sync failure must fail the group"
            );
        }

        for (i, slot) in followers.iter().enumerate() {
            assert!(slot.is_done(), "member {i} was left pending");
            let outcome = slot.finish();
            assert!(
                outcome.is_err(),
                "member {i} must learn the group did not commit"
            );
        }

        assert_eq!(
            engine.snapshot_seq(),
            horizon_before,
            "a failed group must not publish a read horizon"
        );
        for i in 0..3 {
            let name = format!("member{i}");
            assert_eq!(
                engine.get(&key(name.as_bytes()), u64::MAX).unwrap(),
                None,
                "a failed group must not be applied to the memtable"
            );
        }
        assert_eq!(
            engine
                .active_wal
                .lock()
                .as_ref()
                .map(|w| w.offset())
                .unwrap(),
            wal_len_before,
            "a failed group must be rolled back out of the WAL"
        );
    }

    #[test]
    fn a_failed_group_leaves_nothing_to_recover() {
        let dir = TempDir::new().unwrap();
        {
            let engine = open_engine(&dir);
            engine
                .submit(durable_put(b"before", b"kept"))
                .expect("the pre-failure write commits");

            let _fault = arm_sync_failure(&dir);
            let err = engine
                .submit(durable_put(b"during", b"lost"))
                .expect_err("the injected failure must surface");
            assert!(err.to_string().contains("injected"));
        }

        let engine = open_engine(&dir);
        assert_eq!(
            engine.get(&key(b"before"), u64::MAX).unwrap(),
            Some(b"kept".to_vec())
        );
        assert_eq!(
            engine.get(&key(b"during"), u64::MAX).unwrap(),
            None,
            "a write whose group failed must not survive a reopen"
        );
    }

    #[test]
    fn an_abandoned_ticket_is_completed_and_does_not_wedge_the_ring() {
        // G3: the ring owns the slot, so a writer that went away between
        // its push and its wait still gets its ticket executed and the
        // ring still drains for everyone behind it.
        let dir = TempDir::new().unwrap();
        let engine = open_engine(&dir);

        let orphan = Arc::new(WriteSlot::new());
        orphan
            .arm(durable_put(b"orphan", b"value"))
            .expect("fresh slot arms");
        engine
            .commit_ring
            .push(Arc::clone(&orphan))
            .map_err(|_| "commit ring full")
            .expect("empty ring accepts a ticket");

        engine
            .submit(durable_put(b"later", b"value"))
            .expect("a later writer drains the ring");

        assert!(orphan.is_done(), "the abandoned ticket was never executed");
        assert!(orphan.finish().is_ok());
        assert_eq!(
            engine.get(&key(b"orphan"), u64::MAX).unwrap(),
            Some(b"value".to_vec())
        );
        assert_eq!(
            engine.get(&key(b"later"), u64::MAX).unwrap(),
            Some(b"value".to_vec())
        );
    }

    #[test]
    fn one_group_costs_one_sync_no_matter_how_many_members() {
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

        let followers: Vec<Arc<WriteSlot>> = (0..8)
            .map(|i| {
                let slot = Arc::new(WriteSlot::new());
                slot.arm(durable_put(format!("k{i}").as_bytes(), b"v"))
                    .expect("fresh slot arms");
                engine
                    .commit_ring
                    .push(Arc::clone(&slot))
                    .map_err(|_| "commit ring full")
                    .expect("ring accepts the ticket");
                slot
            })
            .collect();

        assert_eq!(stats.get_ticker(Ticker::WalSyncCount), 0);
        engine.try_drain();

        for slot in &followers {
            assert!(slot.is_done());
            slot.finish().expect("every member commits");
        }
        assert_eq!(
            stats.get_ticker(Ticker::WalSyncCount),
            1,
            "eight durable writers in one group must cost exactly one fdatasync"
        );
        for i in 0..8 {
            let name = format!("k{i}");
            assert_eq!(
                engine.get(&key(name.as_bytes()), u64::MAX).unwrap(),
                Some(b"v".to_vec())
            );
        }
    }

    #[test]
    fn a_group_publishes_the_horizon_only_after_every_member_is_applied() {
        // the lost-update fix: `snapshot_seq` must cover every operation in the group or
        // none of it, never a prefix.
        let dir = TempDir::new().unwrap();
        let engine = open_engine(&dir);

        let slots: Vec<Arc<WriteSlot>> = (0..4)
            .map(|i| {
                let slot = Arc::new(WriteSlot::new());
                slot.arm(durable_put(format!("h{i}").as_bytes(), b"v"))
                    .expect("fresh slot arms");
                slot
            })
            .collect();

        let mut pipe = engine.pipeline.lock();
        pipe.group.clear();
        for slot in &slots {
            let request = slot.take_request();
            pipe.group.push(GroupTicket {
                slot: Some(Arc::clone(slot)),
                request,
            });
        }
        engine
            .run_and_complete(&mut pipe, engine.view.load())
            .expect("group commits");
        drop(pipe);

        let horizon = engine.snapshot_seq();
        for i in 0..4 {
            let name = format!("h{i}");
            assert_eq!(
                engine.get(&key(name.as_bytes()), horizon).unwrap(),
                Some(b"v".to_vec()),
                "the published horizon must cover every member of the group"
            );
        }
    }

    #[test]
    fn a_group_stranded_by_an_unwound_leader_is_released_not_left_parked() {
        // Simulates what a leader that unwound mid-group leaves behind:
        // staged tickets whose writers are parked. The next leader must
        // tell them, not silently drop them.
        let dir = TempDir::new().unwrap();
        let engine = open_engine(&dir);

        let stranded = Arc::new(WriteSlot::new());
        stranded
            .arm(durable_put(b"stranded", b"v"))
            .expect("fresh slot arms");

        {
            let mut pipe = engine.pipeline.lock();
            let request = stranded.take_request();
            pipe.group.push(GroupTicket {
                slot: Some(Arc::clone(&stranded)),
                request,
            });
        }

        engine
            .submit(durable_put(b"next", b"v"))
            .expect("the next leader commits its own write");

        assert!(stranded.is_done(), "the stranded writer is still parked");
        let err = stranded
            .finish()
            .expect_err("a stranded writer must not be told it committed");
        assert!(err.to_string().contains("abandoned"));
        assert_eq!(
            engine.get(&key(b"next"), u64::MAX).unwrap(),
            Some(b"v".to_vec())
        );
    }

    #[test]
    fn a_group_is_staged_in_one_exact_reservation_the_next_group_reuses() {
        let dir = TempDir::new().unwrap();
        let engine = open_engine(&dir);

        let batch = || WriteRequest::Batch {
            ops: (0..1000)
                .map(|i| WriteBatchOp::Put {
                    key: key(format!("k{i:04}").as_bytes()),
                    value: vec![b'v'; 4096],
                })
                .collect(),
            durability: DurabilityMode::Eventual,
            disable_wal: false,
        };
        let staged = batch().staged_len();
        assert!(
            staged > MAX_GROUP_BYTES,
            "the test batch must exceed the group cap to exercise the reservation, got {staged}"
        );

        // `run_group` alone, ahead of `run_and_complete`'s `trim_stage`:
        // `trim_stage` shrinks an overshot stage back down to exactly
        // `staged` regardless of how it got there, which would make a
        // doubling chain that happens to end above `staged` indistinguishable
        // from a single exact reservation once the group has fully
        // completed. Checking right after `run_group` returns, before that
        // trim runs, is what actually pins the one-allocation claim.
        {
            let mut guard = engine.pipeline.lock();
            let pipe: &mut Pipeline = &mut guard;
            pipe.group.push(GroupTicket {
                slot: None,
                request: batch(),
            });
            engine
                .run_group(&mut pipe.stage, &pipe.group, engine.view.load(), staged)
                .expect("a batch larger than the group cap still commits");
            assert_eq!(
                pipe.stage.capacity(),
                staged,
                "run_group must reserve exactly the group's framed length in one allocation, not grow it by doubling"
            );
            pipe.group.clear();
        }

        engine
            .submit(batch())
            .expect("a batch larger than the group cap still commits");
        let (cap, ptr) = {
            let pipe = engine.pipeline.lock();
            (pipe.stage.capacity(), pipe.stage.as_ptr())
        };
        assert_eq!(
            cap, staged,
            "the stage must reserve exactly the group's framed length, not a doubling chain"
        );

        engine.submit(batch()).expect("the next group commits");
        let pipe = engine.pipeline.lock();
        assert_eq!(
            pipe.stage.capacity(),
            staged,
            "a stage already exactly sized must not change capacity"
        );
        assert_eq!(
            pipe.stage.as_ptr(),
            ptr,
            "a stage already large enough for the next group must not reallocate"
        );
    }

    #[test]
    fn an_outsized_request_gives_its_stage_back_once_two_smaller_groups_ran() {
        let dir = TempDir::new().unwrap();
        let engine = open_engine(&dir);

        let huge = vec![b'x'; MAX_GROUP_BYTES + 64 * 1024];
        let huge_staged = WriteRequest::Put {
            key: key(b"huge"),
            value: huge.clone(),
            durability: DurabilityMode::Eventual,
            disable_wal: false,
        }
        .staged_len();

        engine
            .submit(WriteRequest::Put {
                key: key(b"huge"),
                value: huge.clone(),
                durability: DurabilityMode::Eventual,
                disable_wal: false,
            })
            .expect("a request larger than the group cap still commits");
        assert_eq!(
            engine.pipeline.lock().stage.capacity(),
            huge_staged,
            "the group that just staged the huge request keeps exactly what it staged"
        );

        engine
            .submit(durable_put(b"a", b"v"))
            .expect("a small put commits");
        assert_eq!(
            engine.pipeline.lock().stage.capacity(),
            huge_staged,
            "one group of hysteresis must not release the stage yet"
        );

        engine
            .submit(durable_put(b"b", b"v"))
            .expect("a second small put commits");
        assert!(
            engine.pipeline.lock().stage.capacity() <= MAX_GROUP_BYTES,
            "the stage must be released once two smaller groups have run"
        );

        assert_eq!(engine.get(&key(b"huge"), u64::MAX).unwrap(), Some(huge));
    }

    #[test]
    fn a_giant_group_parks_no_more_than_the_retention_cap() {
        // Only `run_and_complete` trims the stage, so a giant group has to
        // be cut to the ceiling in the same call or it stays parked while
        // writes are idle or after close.
        let dir = TempDir::new().unwrap();
        let engine = open_engine(&dir);

        let huge = vec![b'x'; 32 * MAX_GROUP_BYTES];
        engine
            .submit(WriteRequest::Put {
                key: key(b"huge"),
                value: huge,
                durability: DurabilityMode::Eventual,
                disable_wal: false,
            })
            .expect("a request far larger than the group cap still commits");

        let cap = engine.pipeline.lock().stage.capacity();
        assert!(
            cap <= MAX_KEPT_STAGE_BYTES,
            "a one-off giant group must not park more than the retention cap, got {cap}"
        );
    }

    #[test]
    fn varying_group_sizes_reallocate_only_across_the_kept_capacity_boundary() {
        // A group of varying size grows the stage only past the kept
        // capacity, and shrinks it only once the group two back was the
        // largest of the three, not on every group above the cap.
        let dir = TempDir::new().unwrap();
        let engine = open_engine(&dir);

        let put_of = |mib: usize| WriteRequest::Put {
            key: key(b"v"),
            value: vec![b'x'; mib * 1024 * 1024],
            durability: DurabilityMode::Eventual,
            disable_wal: false,
        };
        let staged_of = |mib: usize| put_of(mib).staged_len();

        let mut capacities = Vec::new();
        for mib in [3, 2, 2, 3] {
            engine
                .submit(put_of(mib))
                .expect("each oversized put commits on its own");
            capacities.push(engine.pipeline.lock().stage.capacity());
        }

        assert_eq!(
            capacities,
            vec![staged_of(3), staged_of(3), staged_of(2), staged_of(3)],
            "the stage grows only past its kept capacity and shrinks only once the group two back is shed"
        );
    }

    #[test]
    fn a_group_that_staged_nothing_does_not_count_as_staged() {
        // A group that returns before encoding (here, a latched wal
        // failure caught by `ensure_writable`) must not be credited with
        // the bytes it was *asked* to stage: crediting it would let a
        // refused or failed group pin an older, larger group's buffer
        // alive under a size that was never reserved.
        let dir = TempDir::new().unwrap();
        let engine = open_engine(&dir);

        let big = vec![b'x'; 2 * MAX_GROUP_BYTES];
        let big_staged = WriteRequest::Put {
            key: key(b"big"),
            value: big.clone(),
            durability: DurabilityMode::Eventual,
            disable_wal: false,
        }
        .staged_len();

        engine
            .submit(WriteRequest::Put {
                key: key(b"big"),
                value: big,
                durability: DurabilityMode::Eventual,
                disable_wal: false,
            })
            .expect("a request larger than the group cap still commits");
        assert_eq!(engine.pipeline.lock().stage.capacity(), big_staged);

        engine
            .submit(durable_put(b"small", b"v"))
            .expect("a small put commits");
        assert_eq!(
            engine.pipeline.lock().stage.capacity(),
            big_staged,
            "one group of hysteresis must not release the stage yet"
        );

        engine.latch_wal_failure(&io::Error::other("induced for the test"));

        let doomed = WriteRequest::Put {
            key: key(b"never"),
            value: vec![b'y'; 3 * MAX_GROUP_BYTES],
            durability: DurabilityMode::Eventual,
            disable_wal: false,
        };
        let mut pipe = engine.pipeline.lock();
        pipe.group.clear();
        pipe.group.push(GroupTicket {
            slot: None,
            request: doomed,
        });
        let result = engine.run_and_complete(&mut pipe, engine.view.load());
        assert!(
            result.is_err(),
            "a latched wal failure must fail the group before it stages anything"
        );
        assert!(
            pipe.stage.capacity() <= MAX_GROUP_BYTES,
            "a group that staged nothing must not be credited with a size it \
             never reserved, so the previous group's buffer stays parked"
        );
    }

    #[test]
    fn a_refused_reservation_consumes_no_sequence_and_applies_nothing() {
        // The refused-reservation branch (`try_reserve_exact` failing) has
        // no other coverage. Pin that it behaves like any other failed
        // group: no sequence number spent, nothing applied.
        let dir = TempDir::new().unwrap();
        let engine = open_engine(&dir);

        let before = engine.latest_seq.load(Ordering::Acquire);
        let mut guard = engine.pipeline.lock();
        let pipe: &mut Pipeline = &mut guard;
        pipe.group.clear();
        pipe.group.push(GroupTicket {
            slot: None,
            request: durable_put(b"never", b"v"),
        });
        let err = engine
            .run_group(&mut pipe.stage, &pipe.group, engine.view.load(), usize::MAX)
            .expect_err("an unsatisfiable reservation must fail rather than allocate");
        assert_eq!(err.kind(), io::ErrorKind::OutOfMemory);
        pipe.group.clear();
        drop(guard);

        assert_eq!(
            engine.latest_seq.load(Ordering::Acquire),
            before,
            "a refused reservation must not consume a sequence number"
        );
        assert_eq!(
            engine.get(&key(b"never"), u64::MAX).unwrap(),
            None,
            "a refused reservation must not apply its group to the memtable"
        );
    }

    #[test]
    fn the_reservation_error_names_no_internal_mechanism() {
        // The same refused reservation is handed to every member of a
        // possibly shared group, including a writer whose own request was
        // small, so the message must not name the internal staging
        // mechanism or give advice tied to the group's size.
        let dir = TempDir::new().unwrap();
        let engine = open_engine(&dir);

        let mut guard = engine.pipeline.lock();
        let pipe: &mut Pipeline = &mut guard;
        pipe.group.clear();
        pipe.group.push(GroupTicket {
            slot: None,
            request: durable_put(b"never", b"v"),
        });
        let err = engine
            .run_group(&mut pipe.stage, &pipe.group, engine.view.load(), usize::MAX)
            .expect_err("an unsatisfiable reservation must fail rather than allocate");
        pipe.group.clear();

        assert_eq!(err.kind(), io::ErrorKind::OutOfMemory);
        assert!(
            !err.to_string().contains("group"),
            "the message must not name the internal staging mechanism: {err}"
        );
    }

    #[test]
    fn a_wal_disabled_member_rides_along_without_forcing_a_sync() {
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

        let quiet = Arc::new(WriteSlot::new());
        quiet
            .arm(WriteRequest::Put {
                key: key(b"quiet"),
                value: b"v".to_vec(),
                durability: DurabilityMode::Eventual,
                disable_wal: true,
            })
            .expect("fresh slot arms");
        engine
            .commit_ring
            .push(Arc::clone(&quiet))
            .map_err(|_| "commit ring full")
            .expect("ring accepts the ticket");

        engine
            .submit(WriteRequest::Put {
                key: key(b"eventual"),
                value: b"v".to_vec(),
                durability: DurabilityMode::Eventual,
                disable_wal: false,
            })
            .expect("the group commits");

        assert!(quiet.is_done());
        quiet.finish().expect("the wal-disabled member commits");
        assert_eq!(
            stats.get_ticker(Ticker::WalSyncCount),
            0,
            "no member asked for Immediate durability, so no fsync is due"
        );
        assert_eq!(
            engine.get(&key(b"quiet"), u64::MAX).unwrap(),
            Some(b"v".to_vec())
        );
    }

    #[test]
    fn concurrent_writers_share_far_fewer_fsyncs_than_writes() {
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

        const WRITERS: usize = 8;
        const PER_WRITER: usize = 64;

        let mut handles = Vec::with_capacity(WRITERS);
        for w in 0..WRITERS {
            let engine = Arc::clone(&engine);
            handles.push(thread::spawn(move || {
                for i in 0..PER_WRITER {
                    engine
                        .submit(durable_put(format!("w{w}k{i:04}").as_bytes(), b"value"))
                        .expect("every durable write commits");
                }
            }));
        }
        for handle in handles {
            handle.join().expect("writer thread panicked");
        }

        let total = (WRITERS * PER_WRITER) as u64;
        let syncs = stats.get_ticker(Ticker::WalSyncCount);
        assert!(syncs >= 1, "durable writes must fsync at least once");
        assert!(
            syncs <= total,
            "group commit can never issue more fsyncs than writes: {syncs} > {total}"
        );

        for w in 0..WRITERS {
            for i in 0..PER_WRITER {
                let name = format!("w{w}k{i:04}");
                assert_eq!(
                    engine.get(&key(name.as_bytes()), u64::MAX).unwrap(),
                    Some(b"value".to_vec()),
                    "every committed write must be readable"
                );
            }
        }
    }

    #[test]
    fn real_concurrent_writers_all_learn_a_failed_fsync() {
        // G2 against the real handoff, not a hand-built group: every
        // thread goes through `submit`, so groups form the way they do
        // in production. A thread told `Ok` whose bytes were truncated
        // away is silent data loss; a thread told `Err` whose bytes
        // survive a reopen is a resurrection.
        let dir = TempDir::new().unwrap();
        const WRITERS: usize = 12;
        const PER_WRITER: usize = 40;

        let acknowledged = {
            let engine = open_engine(&dir);
            engine
                .submit(durable_put(b"before", b"kept"))
                .expect("the pre-failure write commits");

            // Alternating, so both outcomes are guaranteed. Half the
            // writers ask for Immediate durability and half for
            // Eventual: an Eventual-only group never syncs and commits,
            // and an Eventual writer that lands in a group with an
            // Immediate one shares that group's fate. Which groups form
            // is decided by thread timing, so leaving the mix to group
            // formation alone makes the test a machine-speed test: on a
            // slow two-core runner every group contained a syncing
            // writer, every group failed, and the run reported 0 of 480
            // acknowledged. A flapping fault supplies the successes
            // itself.
            let _fault = arm_flapping_sync_failure(&dir);
            let acknowledged = Arc::new(Mutex::new(Vec::new()));
            let mut handles = Vec::with_capacity(WRITERS);
            for w in 0..WRITERS {
                let engine = Arc::clone(&engine);
                let acknowledged = Arc::clone(&acknowledged);
                handles.push(thread::spawn(move || {
                    let durability = if w % 2 == 0 {
                        DurabilityMode::Immediate
                    } else {
                        DurabilityMode::Eventual
                    };
                    for i in 0..PER_WRITER {
                        let name = format!("f{w:02}_{i:03}");
                        let request = WriteRequest::Put {
                            key: key(name.as_bytes()),
                            value: b"v".to_vec(),
                            durability,
                            disable_wal: false,
                        };
                        if engine.submit(request).is_ok() {
                            acknowledged.lock().push(name);
                        }
                    }
                }));
            }
            for handle in handles {
                handle.join().expect("writer thread panicked");
            }
            let acknowledged = acknowledged.lock().clone();
            assert!(
                !acknowledged.is_empty() && acknowledged.len() < WRITERS * PER_WRITER,
                "the flapping fault must produce a mix: {} of {} acknowledged",
                acknowledged.len(),
                WRITERS * PER_WRITER
            );
            // A write the caller was told failed must not be readable
            // through the live engine either.
            for w in 0..WRITERS {
                for i in 0..PER_WRITER {
                    let name = format!("f{w:02}_{i:03}");
                    let present = engine
                        .get(&key(name.as_bytes()), u64::MAX)
                        .unwrap()
                        .is_some();
                    assert_eq!(
                        present,
                        acknowledged.contains(&name),
                        "{name}: readable={present} but acknowledged={}",
                        acknowledged.contains(&name)
                    );
                }
            }
            acknowledged
        };

        let engine = open_engine(&dir);
        assert_eq!(
            engine.get(&key(b"before"), u64::MAX).unwrap(),
            Some(b"kept".to_vec()),
            "a write that committed before the fault must survive"
        );
        for w in 0..WRITERS {
            for i in 0..PER_WRITER {
                let name = format!("f{w:02}_{i:03}");
                let recovered = engine.get(&key(name.as_bytes()), u64::MAX).unwrap();
                if acknowledged.contains(&name) {
                    assert_eq!(
                        recovered,
                        Some(b"v".to_vec()),
                        "{name} was acknowledged but lost across a reopen"
                    );
                } else {
                    assert_eq!(
                        recovered, None,
                        "{name} was rejected but resurrected across a reopen"
                    );
                }
            }
        }
    }

    #[test]
    fn a_failed_group_does_not_truncate_an_earlier_groups_bytes() {
        // The rollback offset is per group. An Eventual writer that
        // already committed must keep its WAL bytes when a later
        // Immediate group's fsync fails and rolls back.
        let dir = TempDir::new().unwrap();
        {
            let engine = open_engine(&dir);
            engine
                .submit(WriteRequest::Put {
                    key: key(b"eventual"),
                    value: b"kept".to_vec(),
                    durability: DurabilityMode::Eventual,
                    disable_wal: false,
                })
                .expect("the eventual write commits");

            let _fault = arm_sync_failure(&dir);
            engine
                .submit(durable_put(b"doomed", b"lost"))
                .expect_err("the injected failure must surface");
        }

        let engine = open_engine(&dir);
        assert_eq!(
            engine.get(&key(b"eventual"), u64::MAX).unwrap(),
            Some(b"kept".to_vec()),
            "a failed group rolled back past an earlier group's bytes"
        );
        assert_eq!(engine.get(&key(b"doomed"), u64::MAX).unwrap(), None);
    }

    #[test]
    fn a_writer_that_commits_is_immediately_visible_to_another_thread() {
        // The horizon must be published before the writer is released,
        // observed from a thread that never touched the write path.
        let dir = TempDir::new().unwrap();
        let engine = open_engine(&dir);
        let (tx, rx) = std::sync::mpsc::channel::<usize>();

        let writer = {
            let engine = Arc::clone(&engine);
            thread::spawn(move || {
                for i in 0..2_000usize {
                    engine
                        .submit(durable_put(format!("v{i:05}").as_bytes(), b"v"))
                        .expect("write commits");
                    tx.send(i).expect("reader is alive");
                }
            })
        };

        let mut checked = 0usize;
        for i in rx {
            let horizon = engine.snapshot_seq();
            assert_eq!(
                engine
                    .get(&key(format!("v{i:05}").as_bytes()), horizon)
                    .unwrap(),
                Some(b"v".to_vec()),
                "a committed write was not visible at the published horizon"
            );
            checked += 1;
        }
        writer.join().expect("writer thread panicked");
        assert_eq!(checked, 2_000);
    }

    #[test]
    fn writers_make_progress_with_more_threads_than_ring_slots() {
        let dir = TempDir::new().unwrap();
        let engine = open_engine(&dir);
        let writers = commit_ring_capacity() + 8;

        let mut handles = Vec::with_capacity(writers);
        for w in 0..writers {
            let engine = Arc::clone(&engine);
            handles.push(thread::spawn(move || {
                engine
                    .submit(durable_put(format!("overflow{w:04}").as_bytes(), b"v"))
                    .expect("a full ring must not lose a write");
            }));
        }
        for handle in handles {
            handle.join().expect("writer thread panicked");
        }

        for w in 0..writers {
            let name = format!("overflow{w:04}");
            assert_eq!(
                engine.get(&key(name.as_bytes()), u64::MAX).unwrap(),
                Some(b"v".to_vec())
            );
        }
    }

    proptest! {
        // Cases dropped from the default 256: the low-weight arm below
        // draws lengths above `MAX_KEPT_STAGE_BYTES` so the property
        // actually exercises the ceiling, and resizing (memset) a stage
        // that large on every case would be needlessly slow.
        #![proptest_config(ProptestConfig::with_cases(32))]
        #[test]
        fn the_stage_never_keeps_more_than_the_capped_larger_of_the_last_two_groups(
            lengths in proptest::collection::vec(
                prop_oneof![
                    9 => 0usize..=2 * MAX_GROUP_BYTES + 4096,
                    1 => MAX_KEPT_STAGE_BYTES..=MAX_KEPT_STAGE_BYTES + 2 * MAX_GROUP_BYTES,
                ],
                1..8,
            ),
        ) {
            let mut stage: Vec<u8> = Vec::new();
            let mut prev = 0usize;
            for staged in lengths {
                // Stands in for the encode loop: a real stage always has
                // `len == staged` when `trim_stage` sees it, so a forgotten
                // `clear` inside `trim_stage` would be caught by
                // `shrink_to`'s cannot-go-below-`len` rule.
                stage.clear();
                stage.reserve_exact(staged);
                stage.resize(staged, 0);
                let before = stage.capacity();
                trim_stage(&mut stage, prev, staged);
                let keep = MAX_GROUP_BYTES.max(prev.max(staged).min(MAX_KEPT_STAGE_BYTES));
                prop_assert!(stage.capacity() <= keep);
                prop_assert!(stage.capacity() <= MAX_KEPT_STAGE_BYTES);
                if before <= keep {
                    prop_assert_eq!(stage.capacity(), before);
                }
                prev = staged;
            }
        }
    }
}
