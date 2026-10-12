//! The ordered step: work that takes its turn through the commit ring with
//! the whole pipeline to itself, in place of a mutex (plan 4.7).
//!
//! Rotating the memtable and its log, handing a sealed memtable to its
//! flush, installing an ingested table, creating or dropping a column
//! family, emptying the database, closing it: each needs the pipeline still.
//! Each takes a slot of the ring like a commit and runs when the slot's turn
//! comes, as a *unit*:
//!
//! - **A unit is claimed, not owned.** Its body is a job. Whichever thread
//!   reaches the slot first claims the job with one compare-and-swap and
//!   runs the body; the thread that asked for it is only the likeliest one.
//!   So a thread that stopped after asking holds nobody up.
//! - **The pipeline is drained before the body runs.** The claimer brings
//!   every earlier slot through: written, synced where it must be, and
//!   published. No later slot can be decided before this one is. The body
//!   therefore runs with nothing in flight, as a critical section of one
//!   lock over the whole pipeline would, and reads and changes the
//!   pipeline's state through an [`Ordered`].
//! - **The slot's decision is the state the body left.** The next commit is
//!   decided from it: a new log and memtable after a rotation, a sequence
//!   taken by an ingest.
//! - **A claimed unit is device I/O under way.** A blocking call that finds
//!   it claimed waits for it, as it waits for a sync; a `commit_nowait`
//!   commit leaves it on its queue.
//!
//! # The rotation check
//!
//! A write whose turn comes with the memtable's counted bytes at the write
//! buffer size has the rotation check run first, as a unit of the same kind
//! attached to the write's own slot ([`RegolithEngine::take_turn`]). The
//! count is an upper bound kept in the pipeline's state, so every thread
//! agrees when the check is due; the check itself, with the pipeline
//! drained, measures the memtable and rotates only when it is in fact full.
//! The state it leaves replaces the tip in place, and the write is decided
//! from that.
//!
//! # The round
//!
//! A unit's body runs holding the round, the one claim on the log's device
//! step (`pipeline.rs`): no sync and no rollback of another thread runs
//! under it, and the body syncs the log itself. The state the body leaves
//! is the pipeline's tip before the round is let go.
//!
//! # A failed log write or sync (G2)
//!
//! A failure poisons the log. The thread that next holds the round, a sync
//! round or a unit, discards every commit decided and not yet published
//! ([`RegolithEngine::roll_back`]): their records are cut out of the log,
//! their operations out of the memtable, their sequences handed back, and
//! each of their owners learns the failure. Commits already published are
//! untouched, and the database goes on taking writes. Only a cut that
//! itself fails latches the database, since the log's tail is then unknown.
//!
//! The rollback takes no slot of the ring, so it runs with the ring full.
//! It is ordered against the commits being decided by freezing the decided
//! frontier and moving the pipeline to a new epoch: a decision a thread was
//! computing from the old state is recognized by its epoch when it is
//! settled, lands nothing, and fails its slot.

use std::io;
use std::sync::Arc;

use super::super::internal_key::{
    VALUE_TYPE_DELETION, VALUE_TYPE_MERGE, VALUE_TYPE_VALUE, decode_internal_key,
};
use super::super::io::job::{Job, JobBody};
use super::super::take::Take;
use super::super::wal::{check_write_len, encode_ops_record, ops_record_len, wal_filename};
use super::super::wal_frame::KIND_GROUP;
use super::super::wal_log::Log;
use super::super::{
    DurabilityMode, MemTable, RegolithEngine, apply_batch_op_to_memtable, batch_op_wal_bytes,
};
use super::descriptor::{
    After, Decision, Descriptor, FAILED, Turned, Verdict as Fate, Work, is_immediate,
};
use super::pipeline::{Pipeline, Progress, Turn};
use super::request::batch_op_memtable_cost;
use super::ring::Loaded;
use super::round::HeldRound;
use crate::WriteBatchOp;
use crate::portability::{AtomicU64, Ordering};
use crate::statistics::Ticker;
use crate::sync::internal::Arc as RingArc;

/// What a unit's body is: it runs once, on the thread that claimed it.
pub(super) type Body = Box<dyn FnOnce(&RegolithEngine, &mut Ordered<'_>) + Send>;

/// What a unit's job holds of it. The body itself is in the unit's
/// descriptor, which the job reaches through the ring.
struct Unit {
    engine: std::sync::Weak<RegolithEngine>,
    /// The slot the unit was installed at.
    index: Arc<AtomicU64>,
}

impl Unit {
    fn run(self) {
        if let Some(engine) = self.engine.upgrade() {
            engine.run_unit(self.index.load(Ordering::Acquire));
        }
    }
}

impl JobBody for Unit {
    fn run(self: Box<Self>) {
        (*self).run();
    }

    /// The pipeline cannot pass a unit that did not run, so a release runs
    /// it too.
    fn release(self: Box<Self>) {
        (*self).run();
    }
}

/// The rotation check of one write's turn, as a job.
struct TurnCheck {
    engine: std::sync::Weak<RegolithEngine>,
    index: u64,
}

impl TurnCheck {
    fn run(self) {
        if let Some(engine) = self.engine.upgrade() {
            engine.run_turn(self.index);
        }
    }
}

impl JobBody for TurnCheck {
    fn run(self: Box<Self>) {
        (*self).run();
    }

    fn release(self: Box<Self>) {
        (*self).run();
    }
}

/// The pipeline, held still, as a unit's body sees it. See the module docs.
pub(crate) struct Ordered<'a> {
    engine: &'a RegolithEngine,
    /// The state the next commit is decided from once the unit ends.
    pub(super) state: After,
}

impl Ordered<'_> {
    /// The last sequence decided so far.
    pub(crate) fn last_seq(&self) -> u64 {
        self.state.next_seq.saturating_sub(1)
    }

    /// Take the next sequence, for an ingested table.
    pub(crate) fn take_seq(&mut self) -> u64 {
        let seq = self.state.next_seq;
        self.state.next_seq += 1;
        seq
    }

    /// The memtable commits are applied to now.
    pub(crate) fn active(&self) -> &Arc<MemTable> {
        &self.state.memtable
    }

    /// Make every record of the active log durable. A failed sync latches
    /// the database: the log's tail can no longer be vouched for, and a
    /// retried sync may report success for pages the host already dropped.
    pub(crate) fn sync_log(&mut self) -> io::Result<()> {
        let log = &self.state.log;
        if let Err(err) = log.sync_through(self.state.next_off) {
            tracing::error!(error = %err, "syncing the write-ahead log failed");
            self.engine.latch_wal_failure(&err);
            self.engine.notify_wal_error(&err)?;
            return Err(err);
        }
        Ok(())
    }

    /// Move the active memtable to the frozen list behind a fresh one and a
    /// fresh log, and return it. `check` refuses on a database that is not
    /// writable; a drain for close passes `false`.
    pub(crate) fn seal(&mut self, check: bool) -> io::Result<Arc<MemTable>> {
        if check {
            self.engine.ensure_writable()?;
        }
        // Everything fallible happens before the publication, so a rotation
        // that fails leaves the view as it was.
        let engine = self.engine;
        let fresh = Arc::new(MemTable::new(&engine.memtable_config)?);
        let new_wal_id = engine.versions.take_file_id()?;
        // Recovery takes the newest log by file name and tolerates a torn
        // tail only there, so a log has to be complete on disk before any
        // newer file exists, an empty one included: sync it, then create the
        // next one.
        self.sync_log()?;
        let log = Arc::new(Log::create_in(
            &engine.env,
            &engine.wal_dir.join(wal_filename(new_wal_id)),
            engine.options.keyring.as_deref(),
        )?);
        log.start_epoch(self.state.epoch);

        // Stamped before it is published as frozen: from then on a flush on
        // another thread may take it, and the flush reads both stamps. The
        // ordered step is held, so no write enters it after this.
        let sealing = Arc::clone(&self.state.memtable);
        sealing.seal_seq(self.last_seq());
        // The log that was active while it took writes is the one its
        // records are in, and the only durable copy of them until a flush
        // publishes an SSTable.
        sealing.seal_wal(self.state.log.path().to_path_buf());

        // One publication: the sealed memtable joins `frozen` in the same
        // view that hands writers the fresh active one.
        let sealed = engine.view.update_memtables(|active, frozen| {
            let sealed = Arc::clone(active);
            let mut next_frozen = frozen.to_vec();
            next_frozen.push(Arc::clone(&sealed));
            (Arc::clone(&fresh), next_frozen, sealed)
        });
        debug_assert!(Arc::ptr_eq(&sealed, &sealing));
        engine
            .wal_id
            .store(new_wal_id, std::sync::atomic::Ordering::Release);
        self.state.next_off = log.stamp_len();
        self.state.log = log;
        self.state.memtable = fresh;
        self.state.mem_used = 0;
        Ok(sealed)
    }

    /// Commit `ops` here, inside the unit: logged, synced when `durability`
    /// asks, applied and published before this returns. Returns the last
    /// sequence they took. What a column family's creation and drop use, so
    /// that what follows the commit in the unit is ordered against every
    /// later write.
    ///
    /// The record is written and synced before anything is applied, so a
    /// failure leaves nothing behind but the cut that removes the record.
    pub(crate) fn commit_alone(
        &mut self,
        ops: &[WriteBatchOp],
        durability: DurabilityMode,
    ) -> io::Result<u64> {
        let engine = self.engine;
        engine.ensure_writable()?;
        engine.cf_fence_ops(ops)?;
        if ops.is_empty() {
            return Ok(self.last_seq());
        }
        let _commit = super::super::callback::InCommit::enter();
        let payload = ops_record_len(ops);
        check_write_len(payload)?;
        let log = Arc::clone(&self.state.log);
        let place = log.place(self.state.next_off, payload, self.state.epoch)?;
        let base = self.state.next_seq;
        let mut record = vec![0u8; log.prefix_len()];
        encode_ops_record(&mut record, ops, base);
        let synced = is_immediate(durability);
        let logged = log
            .finish_record(KIND_GROUP, &place, &mut record)
            .and_then(|()| log.write_record(&place, &record))
            .and_then(|_| {
                if synced {
                    log.sync_through(place.end())
                } else {
                    Ok(())
                }
            });
        if let Err(err) = logged {
            tracing::error!(error = %err, "a commit failed in the write-ahead log; discarding its record");
            // The record was placed and written by this thread alone, so
            // there is no other writer of it to turn away: the epoch stays.
            let (_, cut) = log.rollback_to(place.offset.max(log.durable()), self.state.epoch);
            if let Err(cut_err) = cut {
                engine.latch_wal_failure(&cut_err);
            }
            engine.notify_wal_error(&err)?;
            return Err(err);
        }
        if let Some(s) = engine.statistics() {
            s.add(
                Ticker::WalBytesWritten,
                ops.iter().map(batch_op_wal_bytes).sum(),
            );
            if synced {
                s.add(Ticker::WalSyncCount, 1);
            }
        }
        let memtable = &self.state.memtable;
        let mut hint = memtable.insert_hint();
        for (op, seq) in ops.iter().zip(base..) {
            apply_batch_op_to_memtable(memtable, &mut hint, op, seq);
        }
        let last = base + ops.len() as u64 - 1;
        self.state.next_seq = last + 1;
        self.state.next_off = place.end();
        self.state.mem_used = self.state.mem_used.saturating_add(
            ops.iter()
                .map(batch_op_memtable_cost)
                .fold(0usize, usize::saturating_add),
        );
        engine.visible_seq.publish(last);
        Ok(last)
    }

    /// Put `memtable` and `log`, both empty, in place of the active ones:
    /// what emptying the database does once the view no longer shows the old
    /// ones.
    pub(crate) fn replace(&mut self, memtable: Arc<MemTable>, log: Arc<Log>) {
        log.start_epoch(self.state.epoch);
        self.state.next_off = log.stamp_len();
        self.state.log = log;
        self.state.memtable = memtable;
        self.state.mem_used = 0;
    }

    /// Close the active log cleanly, after which every commit is refused.
    /// A log left in an unknown state by an earlier failure is only synced:
    /// CLOSE would vouch for bytes nobody can account for.
    pub(crate) fn close_log(&mut self, latched: bool) -> io::Result<()> {
        if latched {
            return self.state.log.sync_through(self.state.next_off);
        }
        self.state.closed = true;
        self.state.log.close(self.state.next_off)
    }
}

impl RegolithEngine {
    /// A unit descriptor whose body is `body`.
    fn unit(&self, body: Body) -> RingArc<Descriptor> {
        let index = Arc::new(AtomicU64::new(0));
        let job = Job::new(Box::new(Unit {
            engine: self.me.clone(),
            index: Arc::clone(&index),
        }));
        let desc = Descriptor::new(Work::Unit { job, index });
        desc.body.put(body);
        RingArc::new(desc)
    }

    /// Run `body` in the ordered step and return what it returns. See the
    /// module docs: the body may run on another thread, and runs with every
    /// earlier commit published and no later one decided.
    pub(crate) fn ordered<T: Send + 'static>(
        &self,
        body: impl FnOnce(&RegolithEngine, &mut Ordered<'_>) -> io::Result<T> + Send + 'static,
    ) -> io::Result<T> {
        let pipe = self.pipe()?;
        let result: Arc<Take<io::Result<T>>> = Arc::new(Take::empty());
        let out = Arc::clone(&result);
        let desc = self.unit(Box::new(move |engine, ord| out.put(body(engine, ord))));
        let index = self.enter(pipe, &desc);
        loop {
            if let Some(result) = result.take() {
                return result;
            }
            match self.help_decide(pipe, index, true) {
                Turn::Blocked(job) => self.run_or_wait(&job),
                Turn::Done => {
                    // Every slot before the unit is published, and the unit
                    // takes nothing: the frontier passes it here, so the
                    // unit leaves nothing in the ring.
                    let _ = self.publish_upto(pipe, index);
                    return result.take().unwrap_or_else(|| {
                        Err(io::Error::other(
                            "an ordered step of the commit pipeline did not finish",
                        ))
                    });
                }
            }
        }
    }

    /// Run the unit at slot `index`: drain the pipeline, run the body, and
    /// decide the slot with the state the body left.
    fn run_unit(&self, index: u64) {
        let Some(pipe) = self.pipeline.as_ref() else {
            return;
        };
        let Loaded::Ready(desc) = pipe.ring.load(index) else {
            return;
        };
        if desc.decision().is_some() {
            return;
        }
        let (_held, state) = self.drained(pipe, index);
        let mut ord = Ordered {
            engine: self,
            state,
        };
        if let Some(body) = desc.body.take() {
            body(self, &mut ord);
        }
        desc.decide(RingArc::new(Decision::new(index, Fate::Unit, ord.state)));
        // The state the body left is the tip before the round is let go:
        // a rollback, which needs the round, then starts from it.
        self.settle(pipe, index, &desc);
    }

    /// Bring every slot before `index` through to published, with the
    /// decided frontier at `index - 1`. The caller runs a unit, so it does
    /// its own device I/O and waits for what is under way.
    fn drain_before(&self, pipe: &Pipeline, index: u64) {
        loop {
            match self.publish_upto(pipe, index - 1) {
                Progress::Published => return,
                Progress::NeedsSync | Progress::Failed => self.sync_round(pipe),
                Progress::Undecided => {
                    if let Turn::Blocked(job) = self.help_decide(pipe, index - 1, true) {
                        self.run_or_wait(&job);
                    }
                }
            }
        }
    }

    /// Drain the pipeline before slot `index` and hold the round: what a
    /// unit's body runs under. Returns the hold and the state the pipeline
    /// is in. A log that failed is rolled back first, here.
    fn drained<'a>(&'a self, pipe: &Pipeline, index: u64) -> (HeldRound<'a>, After) {
        self.drain_before(pipe, index);
        // Nothing before `index` is unpublished from here on, and nothing
        // after it is decided before this unit is. Only the log can still
        // change under a unit, in a round another thread runs; the hold
        // stops that.
        let held = self.hold_round(pipe);
        if pipe.tip.load().after.log.is_poisoned() {
            self.roll_back(pipe);
        }
        (held, pipe.tip.load().after.clone())
    }

    /// Discard every commit decided and not published (G2), and leave the
    /// pipeline resuming from the published prefix. Called by the thread
    /// that holds the round, so no sync and no unit's body is running. See
    /// the module docs.
    pub(super) fn roll_back(&self, pipe: &Pipeline) {
        // Deciding stops: no frontier pass succeeds from here on (R5).
        let decided = pipe.ring.freeze_decided();
        // The tip stops: a marker of the next epoch takes its place, which
        // no decision computed from the old state can replace. The slot the
        // old tip decided is the last one in the old state; a decision a
        // thread is still computing for the slot after it is stale, and its
        // slot is failed when it is settled (P4).
        let (seen, marker) = loop {
            let seen = pipe.tip.load();
            let mut after = seen.after.clone();
            after.epoch += 1;
            let marker = RingArc::new(Decision::new(seen.index, Fate::Unit, after));
            if pipe.tip.replace(&seen, RingArc::clone(&marker)) {
                break (seen, marker);
            }
        };
        let last = decided.max(seen.index);
        let mut after = marker.after.clone();
        let log = Arc::clone(&after.log);

        // No other thread publishes from here on. A slot another thread was
        // about to publish is one every thread calls publishable, so it is
        // published here rather than discarded (P3).
        let mut at = pipe.ring.freeze();
        while at < last {
            if let Loaded::Ready(desc) = pipe.ring.load(at + 1) {
                let publishable = desc
                    .decision()
                    .is_some_and(|decision| Self::publishable_slot(&desc, decision));
                if !publishable {
                    break;
                }
                if !desc.is(FAILED)
                    && let Some(last) = desc.decision().and_then(Decision::last_seq)
                {
                    self.visible_seq.publish(last);
                }
                desc.land();
                at += 1;
                pipe.ring.set_frozen(at);
                pipe.ring.retire(at);
            } else {
                // Voided, or already passed.
                at += 1;
                pipe.ring.set_frozen(at);
            }
        }

        // Everything in `(at, last]` is discarded: where its first record
        // starts, and the first sequence it took.
        let mut cut = None;
        let mut floor = None;
        let mut failed = Vec::new();
        for slot in (at + 1)..=last {
            let Loaded::Ready(desc) = pipe.ring.load(slot) else {
                continue;
            };
            if let Some(decision) = desc.decision() {
                if decision.commits() && floor.is_none() {
                    floor = Some(decision.base_seq);
                }
                if let Some(place) = &decision.place
                    && cut.is_none()
                    && Arc::ptr_eq(&decision.after.log, &log)
                {
                    cut = Some(place.offset);
                }
            }
            failed.push(desc);
        }

        // A sync covers a prefix of written records, so nothing durable lies
        // past the first discarded record; the bound is for a reader of
        // this line.
        let cut_at = cut.unwrap_or(after.next_off).max(log.durable());
        let (cause, cut_done) = log.rollback_to(cut_at, after.epoch);
        if let Err(err) = &cut_done {
            tracing::error!(error = %err, "cutting failed commits out of the write-ahead log failed");
            self.latch_wal_failure(err);
        }
        after.next_off = cut_at;
        if let Some(floor) = floor {
            after.next_seq = floor;
        }
        // The memtable is replaced whether or not a discarded commit was
        // applied to it: a thread that was applying a stale decision when
        // this began applies it to the old one, which no view shows again.
        match self.rebuild_memtable(&after.memtable, after.next_seq.saturating_sub(1)) {
            Ok(fresh) => {
                let old = Arc::clone(&after.memtable);
                self.view.update_memtables(|active, frozen| {
                    let active = if Arc::ptr_eq(active, &old) {
                        Arc::clone(&fresh)
                    } else {
                        Arc::clone(active)
                    };
                    (active, frozen.to_vec(), ())
                });
                after.memtable = fresh;
            }
            Err(err) => {
                tracing::error!(error = %err, "removing failed commits from the memtable failed");
                self.latch_wal_failure(&err);
            }
        }
        after.mem_used = after.memtable.approximate_size();

        let cause = cause.unwrap_or_else(|| {
            io::Error::other("the write-ahead log failed and unfinished commits were discarded")
        });
        if !failed.is_empty() {
            tracing::error!(error = %cause, commits = failed.len(), "a write-ahead log failure discarded commits");
        }
        for desc in &failed {
            desc.failure.put(crate::Error::clone_io(&cause));
            desc.mark(FAILED);
            // Discarded is landed too: what waited for the commit is told.
            desc.land();
        }
        if !failed.is_empty()
            && let Err(err) = self.notify_wal_error(&cause)
            && let Some(callback) = crate::Error::callback_panic_of(&err)
        {
            self.latch_callback_panic(callback);
        }
        // The state every later commit is decided from, then the frontiers:
        // they pass the discarded slots, and their owners learn.
        let resumed = RingArc::new(Decision::new(last, Fate::Unit, after));
        let replaced = pipe.tip.replace(&marker, resumed);
        debug_assert!(replaced, "only a rollback replaces its own marker");
        pipe.ring.thaw(last);
        pipe.ring.thaw_decided(last);
        for desc in &failed {
            pipe.ring.retire(desc.index());
        }
    }

    /// A copy of `old` holding only what was written at or below sequence
    /// `through`: what the active memtable is replaced with when commits
    /// applied to it are discarded.
    ///
    /// Costs one pass over the memtable. It runs only after a log failure,
    /// and a reader holding the old memtable keeps reading it: every
    /// snapshot is at or below the published horizon, which `through` is at
    /// or above.
    fn rebuild_memtable(&self, old: &MemTable, through: u64) -> io::Result<Arc<MemTable>> {
        let fresh = MemTable::new(&self.memtable_config)?;
        old.try_for_each_entry(|internal_key, value| {
            let (key, seq, value_type) = decode_internal_key(internal_key);
            if seq <= through {
                match value_type {
                    VALUE_TYPE_VALUE => fresh.put(key, value, seq),
                    VALUE_TYPE_DELETION => fresh.delete(key, seq),
                    VALUE_TYPE_MERGE => fresh.merge(key, value, seq),
                    _ => {
                        return Err(io::Error::other(
                            "a memtable entry has a kind this build does not know",
                        ));
                    }
                }
            }
            Ok(())
        })?;
        for tombstone in old.clone_range_tombstones() {
            if tombstone.seq <= through {
                fresh.delete_range(&tombstone.start, &tombstone.end, tombstone.seq);
            }
        }
        Ok(Arc::new(fresh))
    }

    /// Whether the rotation check is due at the turn of `desc`, decided
    /// from `after`: the memtable's counted bytes reached the write buffer
    /// size, and the slot may write.
    pub(super) fn turn_is_due(&self, desc: &Descriptor, after: &After) -> bool {
        after.mem_used >= self.options.write_buffer_size
            && !after.closed
            && matches!(desc.work, Work::Request(_) | Work::Allocate { .. })
    }

    /// The rotation check of the write at slot `index`, run here if this
    /// thread may and nobody has, or handed back as the job in the way.
    pub(super) fn take_turn<'d>(
        &self,
        index: u64,
        desc: &'d Descriptor,
        can_run: bool,
    ) -> Result<&'d Turned, Arc<Job>> {
        let job = match desc.turn_job.get() {
            Some(job) => job,
            None => desc.turn_job.get_or_set(Job::new(Box::new(TurnCheck {
                engine: self.me.clone(),
                index,
            }))),
        };
        if !job.is_done() {
            if !(can_run && job.claim()) {
                return Err(Arc::clone(job));
            }
            self.io().run_job(job);
        }
        Ok(match desc.turn.get() {
            Some(turned) => turned,
            // The check ended without an answer: it unwound.
            None => desc.turn.get_or_set(Turned {
                refused: Some(io::Error::other(
                    "the memtable rotation before this write did not finish",
                )),
            }),
        })
    }

    /// The rotation check at slot `index`: drain the pipeline, then rotate
    /// if the memtable is in fact full.
    fn run_turn(&self, index: u64) {
        let Some(pipe) = self.pipeline.as_ref() else {
            return;
        };
        let Loaded::Ready(desc) = pipe.ring.load(index) else {
            return;
        };
        if desc.turn.get().is_some() || desc.decision().is_some() {
            return;
        }
        // A flush the rotation runs under back-pressure calls the caller's
        // code (a prefix extractor, a listener): a panic there is caught, as
        // in every ordered step of a commit, and latches the database.
        let _commit = super::super::callback::InCommit::enter();
        let (_held, state) = self.drained(pipe, index);
        let mut ord = Ordered {
            engine: self,
            state,
        };
        let refused = self.rotate_if_full(&mut ord).err();
        if let Some(err) = &refused
            && let Some(callback) = crate::Error::callback_panic_of(err)
        {
            self.latch_callback_panic(callback);
        }
        // The state the check left, rotated or not, takes the tip's place
        // before the round is let go and before the job lands, so every
        // thread that waited for the check decides the write from it.
        loop {
            let tip = pipe.tip.load();
            let turned = Decision::new(tip.index, Fate::Unit, ord.state.clone());
            if pipe.tip.replace(&tip, RingArc::new(turned)) {
                break;
            }
        }
        desc.turn.get_or_set(Turned { refused });
    }

    /// Seal the active memtable when it has reached `write_buffer_size`,
    /// in the ordered step, before the write whose turn this is takes a
    /// sequence: a failure is the write's, and means it did not land.
    ///
    /// A memtable below the size only has its counted bytes corrected to
    /// what it holds: the count is an upper bound.
    fn rotate_if_full(&self, ord: &mut Ordered<'_>) -> io::Result<()> {
        let used = ord.state.memtable.approximate_size();
        if used < self.options.write_buffer_size {
            ord.state.mem_used = used;
            return Ok(());
        }
        // A rotation leaves at most `max_write_buffer_number` memtables. One
        // that may leave none but the fresh active one flushes what it seals
        // here, as every rotation did before flushes left the commit path.
        let room = self.options.max_write_buffer_number.checked_sub(1);
        if room == Some(0) {
            let sealed = ord.seal(true)?;
            let flushed = self.flush_until_retired(&sealed);
            // Even when the flush failed: the memtable it left frozen counts
            // toward the stall thresholds.
            self.refresh_stall_level();
            return flushed;
        }
        // Normally the flushes behind it are done and nothing is written
        // here. When they are not, the oldest frozen memtables are written
        // out first: memory stays within the cap, and the commit path waits
        // only when the background has fallen a whole memtable behind.
        if let Some(room) = room {
            while self.view.load().frozen.len() >= room {
                // The exclusion is released before the level is refreshed.
                let flushed = self
                    .flusher
                    .flushing()
                    .and_then(|flushing| self.flush_oldest_frozen(&flushing));
                // A failed flush too, once its exclusion is released: a
                // stopped writer it held off looks again (`StallSignal`,
                // relief handed back).
                if flushed.is_err() {
                    self.refresh_stall_level();
                }
                if !flushed? {
                    break;
                }
            }
        }
        // Sealed here and flushed off the commit path (E9): by the worker,
        // or by a writer once it leaves the pipeline.
        ord.seal(true)?;
        self.flush_sealed_later();
        self.refresh_stall_level();
        Ok(())
    }
}
