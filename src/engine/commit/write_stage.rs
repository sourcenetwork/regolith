//! The write stage: how decided commits' records reach the log (plan 4.7;
//! `wal_gate.rs`, WG4 and WG6; `WriteClaim` and `BatchWrite` in
//! `proofs/tla/CommitPipelineSteps.tla`).
//!
//! The host puts the writes of one file one after another, whoever calls
//! them: a positional write takes the file's lock, and a second writer
//! spins on it or sleeps. Eight threads each writing their own record keep
//! seven of them spinning in the kernel and buy nothing. So records are
//! written in batches. The thread that takes the log's write claim, in the
//! same step that counts its write in at the gate, gathers every record that
//! is decided and not written yet, in ring order from the first one, as one
//! contiguous range of the log, and writes the range with one positional
//! write. It marks each record written, which wakes whoever waits for it,
//! lets the claim go with its count out, and wakes the next writer in line
//! when one parked on the claim.
//!
//! # Who waits, and for what
//!
//! - **A blocking call** that finds the claim taken parks on the slot whose
//!   record it needs, until that record is written, the slot failed, the
//!   claim is let go, or [`WRITE_PATIENCE`] passed. A record the holder
//!   gathered is a write under way: device I/O, which the call goes on
//!   waiting for. Any other record it then writes itself, without the claim,
//!   as a copy: the holder may be slow to gather that far, and nothing waits
//!   for a thread to be scheduled.
//! - **A `commit_nowait` call or a queue's poll** never waits. One that
//!   finds the claim taken gives the holder about as long as a write takes
//!   (the courtesy) and then writes its own record as a copy.
//!
//! A copy is the same bytes at the same offset. It counts in at the gate and
//! looks at its record after, as a batch does, so no copy lands on a range a
//! sync has begun to cover (WG4).
//!
//! # Invariants
//!
//! - **W1, a batch is one contiguous range of one log in one epoch.** Its
//!   first record fixes the log and the epoch; it stops at a record of
//!   another log or epoch, at a gap, and at a record already written.
//! - **W2, a batch looks at its records after its count in.** Each record it
//!   gathers was not written when it looked, after the count in, so a sync
//!   whose turn came before the count in knew none of them written and syncs
//!   none of them (WG4); the rollback that moved the epoch waits for the
//!   count out (WG2).
//! - **W3, a batch's records are marked written before its count out.** A
//!   thread parked on one of them is woken while the batch is still a write
//!   under way, which is all it waits for.
//! - **W4, a batch is bounded.** It holds the slots decided when it began,
//!   and at most [`MAX_BATCH_BYTES`] past its first record, so one call
//!   writes the records up to its own and at most one batch past it (P5).

use std::cell::RefCell;
use std::io;
use std::sync::Arc;
use std::time::Duration;

use super::super::RegolithEngine;
use super::super::wal_frame::KIND_GROUP;
use super::super::wal_log::Log;
use super::descriptor::{Descriptor, FAILED, WRITTEN};
use super::park::Help;
use super::pipeline::{Pipeline, courtesy, ops_of};
use super::ring::Loaded;
use crate::perf_context::{PerfTimer, PerfTimerField};
use crate::statistics::{Histogram, Ticker};
use crate::sync::internal::{Arc as RingArc, AtomicU64, Ordering};

/// Bytes a batch gathers past its first record at the most: the size of
/// record buffer a thread keeps between commits anyway.
const MAX_BATCH_BYTES: u64 = super::MAX_GROUP_BYTES as u64;

/// How long a blocking call parks on a write claim another thread holds
/// before it looks again: whether the claim was let go, and whether its
/// record is in the batch under way. A batch normally ends within a few
/// microseconds and wakes the writers whose records it holds, and the
/// claim's next holder is woken when it is let go, so this bounds only what
/// a slow or descheduled holder costs the writers behind it.
pub(super) const WRITE_PATIENCE: Duration = Duration::from_micros(200);

/// Where the write stage stands. Both words are hints a batch starts from;
/// what it writes it decides from each record's own flags.
pub(crate) struct WriteStage {
    /// Every slot at or below this one has its record written, or has none:
    /// where the next batch starts looking. Raised only by a claim holder.
    written: AtomicU64,
    /// The last slot the batch under way gathered. A record at or below it
    /// that is not written yet is being written now.
    through: AtomicU64,
}

impl WriteStage {
    /// The stage of a ring whose slots below `first` are all finished.
    pub(crate) fn new(first: u64) -> Self {
        Self {
            written: AtomicU64::new(first - 1),
            through: AtomicU64::new(first - 1),
        }
    }
}

std::thread_local! {
    /// This thread's buffers for a batch: the record it frames now, the
    /// length of the one before it (`trim_stage`'s hysteresis), the batch
    /// built of them, and the descriptors of the records in the batch. The
    /// first record of a batch is written from the first buffer when it is
    /// the only one, with no copy.
    static BATCH: RefCell<Buffers> = const {
        RefCell::new(Buffers {
            stage: Vec::new(),
            prev: 0,
            batch: Vec::new(),
            slots: Vec::new(),
        })
    };
}

struct Buffers {
    stage: Vec<u8>,
    prev: usize,
    batch: Vec<u8>,
    /// The batch's slots past its first, which is the caller's.
    slots: Vec<RingArc<Descriptor>>,
}

#[cfg(test)]
std::thread_local! {
    /// Test-only: where this thread's last batch began in the log, and its
    /// bytes.
    static LAST_BATCH: std::cell::Cell<(u64, usize)> = const { std::cell::Cell::new((0, 0)) };
}

/// Test-only: where this thread's last batch began in the log, and its
/// bytes.
#[cfg(test)]
pub(super) fn last_batch() -> (u64, usize) {
    LAST_BATCH.with(std::cell::Cell::get)
}

/// Test-only: the capacity and the address of this thread's stage buffer.
#[cfg(test)]
pub(super) fn stage_buffer() -> (usize, *const u8) {
    BATCH.with(|b| {
        let b = b.borrow();
        (b.stage.capacity(), b.stage.as_ptr())
    })
}

/// What one try at a batch did.
enum Tried {
    /// It wrote a batch, or found nothing it may write.
    Done,
    /// Another thread holds the log's write claim.
    Claimed,
}

/// The batch a claim holder gathered.
struct Gathered {
    /// Where its first record starts in the log...
    offset: u64,
    /// ...and where its last one ends.
    end: u64,
    /// The slot of its last record.
    last: u64,
    /// How many records it holds.
    count: usize,
    /// Whether the caller's own slot is among them.
    has_target: bool,
    /// Whether every slot from where the batch began looking to its last is
    /// written once it is: the written hint may then move to its last.
    contiguous: bool,
}

/// Whether slot `desc`'s record needs writing: it has one, it is not
/// written, the slot was not discarded, and its log has not failed. Its log
/// when it does.
fn unwritten(desc: &Descriptor) -> Option<&Arc<Log>> {
    let decision = desc.decision()?;
    decision.place.as_ref()?;
    if desc.is(WRITTEN) || desc.is(FAILED) || decision.after.log.is_poisoned() {
        return None;
    }
    Some(&decision.after.log)
}

impl RegolithEngine {
    /// Bring slot `desc`'s record into the log, as `help` says: a blocking
    /// call returns once it is written, the slot failed, or the log did; a
    /// call that may not wait returns once it wrote it or gave the claim's
    /// holder its courtesy. See the module docs.
    pub(super) fn write_slot(&self, pipe: &Pipeline, desc: &RingArc<Descriptor>, help: Help<'_>) {
        match help {
            Help::Wait => self.write_waiting(pipe, desc),
            Help::Leave | Help::Park(_) => {
                if unwritten(desc).is_none() {
                    return;
                }
                if let Tried::Claimed = self.try_batch(pipe, desc) {
                    let kib = desc
                        .decision()
                        .and_then(|decision| decision.place.as_ref())
                        .map_or(0, |place| place.len / 1024);
                    courtesy(kib as usize, || desc.is(WRITTEN));
                    if unwritten(desc).is_some() {
                        self.write_copy(desc);
                    }
                }
            }
        }
    }

    /// [`Self::write_slot`] for a blocking call.
    fn write_waiting(&self, pipe: &Pipeline, desc: &RingArc<Descriptor>) {
        while let Some(log) = unwritten(desc) {
            if let Tried::Done = self.try_batch(pipe, desc) {
                continue;
            }
            super::hook::at(super::hook::Stage::WriteWait);
            // On the slot's list first, then counted among the claim's
            // waiters, then a last look (WG6): the holder lets the claim go
            // and reads the count in one step, and wakes the next record's
            // waiters when the count is not zero.
            let counted = std::cell::Cell::new(false);
            desc.park(WRITE_PATIENCE, || {
                if !log.wait_for_claim() {
                    return true;
                }
                counted.set(true);
                unwritten(desc).is_none()
            });
            if counted.get() {
                log.unwait();
            }
            if unwritten(desc).is_none() || !log.is_claimed() {
                continue;
            }
            // Still claimed after the patience. A record the holder gathered
            // is a write under way: wait on. Any other the holder may be slow
            // to reach, and it is written here, as a copy.
            if desc.index() <= pipe.writes.through.load(Ordering::Acquire) {
                continue;
            }
            self.write_copy(desc);
        }
    }

    /// Take the log's write claim and write a batch that holds slot
    /// `target`'s record, when nobody holds the claim. See the module docs.
    fn try_batch(&self, pipe: &Pipeline, target: &RingArc<Descriptor>) -> Tried {
        let Some(decision) = target.decision() else {
            return Tried::Done;
        };
        let Some(place) = &decision.place else {
            return Tried::Done;
        };
        let log = &decision.after.log;
        // Most calls that find the claim taken need not count in to see so.
        if log.is_claimed() {
            return Tried::Claimed;
        }
        super::hook::at(super::hook::Stage::Write);
        let Some(flight) = log.count_in(place.epoch, true) else {
            // The gate moved on: a rollback discarded the slot (WG1).
            return Tried::Done;
        };
        if !flight.claimed() {
            drop(flight);
            return Tried::Claimed;
        }
        let _perf = PerfTimer::new(PerfTimerField::WriteWal);
        let start = self.statistics().and_then(|_| self.env.now_micros());
        let (last, wrote) = BATCH.with(|buffers| {
            let mut buffers = buffers.borrow_mut();
            let buffers = &mut *buffers;
            buffers.slots.clear();
            let Some(gathered) = self.gather(pipe, target, log, place.epoch, buffers) else {
                return (None, false);
            };
            pipe.writes.through.store(gathered.last, Ordering::Release);
            let bytes = if gathered.count == 1 {
                &buffers.stage
            } else {
                &buffers.batch
            };
            #[cfg(test)]
            LAST_BATCH.with(|last| last.set((gathered.offset, bytes.len())));
            let wrote = flight.write_at(gathered.offset, bytes);
            let target = gathered.has_target.then_some(target);
            match wrote {
                Ok(()) => {
                    // W3: marked before the count out.
                    self.mark_written(target, &buffers.slots);
                    if gathered.contiguous {
                        pipe.writes.written.store(gathered.last, Ordering::Release);
                    }
                }
                Err(err) => {
                    tracing::error!(error = %err, "writing commits to the write-ahead log failed");
                    log.poison(err);
                    // Whoever waits for one of these records looks again,
                    // and finds the log failed.
                    for desc in target.into_iter().chain(buffers.slots.iter()) {
                        desc.wake();
                    }
                }
            }
            let used = bytes.len();
            super::trim_stage(&mut buffers.batch, used, used);
            super::trim_stage(&mut buffers.stage, buffers.prev, used);
            buffers.prev = used;
            buffers.slots.clear();
            (Some(gathered.last), true)
        });
        let waiters = flight.leave();
        if wrote
            && let Some(s) = self.statistics()
            && let Some(micros) = self.elapsed_micros(start)
        {
            s.record(Histogram::WalWriteTime, micros);
        }
        if waiters > 0 {
            Self::pass_claim(pipe, last.unwrap_or_else(|| pipe.ring.published()));
        }
        Tried::Done
    }

    /// Gather the batch, counted in and holding the claim: the records from
    /// the first one not written, through `target`'s and on while they stay
    /// contiguous (W1, W4), framed into `buffers`. `None` when there is
    /// none it may write.
    fn gather(
        &self,
        pipe: &Pipeline,
        target: &RingArc<Descriptor>,
        log: &Arc<Log>,
        epoch: u64,
        buffers: &mut Buffers,
    ) -> Option<Gathered> {
        let from = pipe
            .writes
            .written
            .load(Ordering::Acquire)
            .max(pipe.ring.published())
            + 1;
        let bound = pipe.ring.decided().max(target.index());
        let mut batch: Option<Gathered> = None;
        let mut contiguous = true;
        for index in from..=bound {
            let loaded;
            let desc = if index == target.index() {
                target
            } else {
                match pipe.ring.load(index) {
                    Loaded::Ready(desc) => {
                        loaded = desc;
                        &loaded
                    }
                    Loaded::Void | Loaded::Gone => continue,
                    Loaded::Empty | Loaded::Full => break,
                }
            };
            let Some(decision) = desc.decision() else {
                break;
            };
            let Some(place) = &decision.place else {
                continue;
            };
            // W2: looked at after the count in.
            let usable = !desc.is(WRITTEN)
                && !desc.is(FAILED)
                && place.epoch == epoch
                && Arc::ptr_eq(&decision.after.log, log);
            match &mut batch {
                None => {
                    if !usable {
                        // A batch begins at a record it may write. One that
                        // is not written is left to its own writer, and the
                        // written hint does not pass it.
                        contiguous &= desc.is(WRITTEN) || desc.is(FAILED);
                        continue;
                    }
                    if let Err(err) = Self::frame(&mut buffers.stage, log, desc) {
                        // The record cannot be built: no write can vouch for
                        // the log past it.
                        tracing::error!(error = %err, "building a commit's write-ahead log record failed");
                        log.poison(err);
                        return None;
                    }
                    batch = Some(Gathered {
                        offset: place.offset,
                        end: place.end(),
                        last: index,
                        count: 1,
                        has_target: index == target.index(),
                        contiguous,
                    });
                }
                Some(gathered) => {
                    // W1, W4: it stops at what does not follow on, or does
                    // not fit.
                    if !usable
                        || place.offset != gathered.end
                        || place.end() - gathered.offset > MAX_BATCH_BYTES
                    {
                        break;
                    }
                    if gathered.count == 1 {
                        // A second record: the first moves into the batch.
                        buffers.batch.clear();
                        buffers.batch.extend_from_slice(&buffers.stage);
                    }
                    if Self::frame(&mut buffers.stage, log, desc).is_err() {
                        // Left for the next batch, which begins with it.
                        break;
                    }
                    buffers.batch.extend_from_slice(&buffers.stage);
                    gathered.end = place.end();
                    gathered.last = index;
                    gathered.count += 1;
                    gathered.has_target |= index == target.index();
                }
            }
            if index != target.index() {
                buffers.slots.push(RingArc::clone(desc));
            }
        }
        batch
    }

    /// Frame slot `desc`'s record into `stage`, replacing what it held.
    fn frame(stage: &mut Vec<u8>, log: &Log, desc: &Descriptor) -> io::Result<()> {
        let Some(decision) = desc.decision() else {
            return Ok(());
        };
        let Some(place) = &decision.place else {
            return Ok(());
        };
        stage.clear();
        if stage.try_reserve_exact(place.len as usize).is_err() {
            return Err(io::Error::new(
                io::ErrorKind::OutOfMemory,
                format!(
                    "not enough memory to commit this write ({} bytes pending); retry, splitting any very large write batch",
                    place.len
                ),
            ));
        }
        stage.resize(log.prefix_len(), 0);
        ops_of(desc, decision).encode(stage, decision.base_seq);
        log.finish_record(KIND_GROUP, place, stage)
    }

    /// Mark the records of a batch written, counting each one this call
    /// marked: `target` when it is in the batch, and `slots`.
    fn mark_written(&self, target: Option<&RingArc<Descriptor>>, slots: &[RingArc<Descriptor>]) {
        let stats = self.statistics();
        for desc in target.into_iter().chain(slots.iter()) {
            if desc.mark(WRITTEN)
                && let Some(s) = stats
                && let Some(decision) = desc.decision()
            {
                s.add(
                    Ticker::WalBytesWritten,
                    ops_of(desc, decision).reported_bytes(),
                );
            }
        }
    }

    /// Write slot `desc`'s record alone, without the claim: a copy, when
    /// the claim's holder may be slow to reach it. Counted in at the gate,
    /// and written only if it is not written by then (WG4).
    pub(super) fn write_copy(&self, desc: &Descriptor) {
        let Some(decision) = desc.decision() else {
            return;
        };
        let Some(place) = &decision.place else {
            return;
        };
        let log = &decision.after.log;
        super::hook::at(super::hook::Stage::Write);
        let _perf = PerfTimer::new(PerfTimerField::WriteWal);
        let start = self.statistics().and_then(|_| self.env.now_micros());
        let wrote = BATCH.with(|buffers| {
            let mut buffers = buffers.borrow_mut();
            let buffers = &mut *buffers;
            Self::frame(&mut buffers.stage, log, desc)?;
            let wrote = match log.count_in(place.epoch, false) {
                // W2: looked at after the count in.
                Some(flight) if !desc.is(WRITTEN) && !desc.is(FAILED) => {
                    let wrote = flight.write_at(place.offset, &buffers.stage);
                    if wrote.is_ok()
                        && desc.mark(WRITTEN)
                        && let Some(s) = self.statistics()
                    {
                        s.add(
                            Ticker::WalBytesWritten,
                            ops_of(desc, decision).reported_bytes(),
                        );
                    }
                    wrote.map(|()| true)
                }
                _ => Ok(false),
            };
            let used = buffers.stage.len();
            super::trim_stage(&mut buffers.stage, buffers.prev, used);
            buffers.prev = used;
            wrote
        });
        match wrote {
            Ok(true) => {
                if let Some(s) = self.statistics()
                    && let Some(micros) = self.elapsed_micros(start)
                {
                    s.record(Histogram::WalWriteTime, micros);
                }
            }
            Ok(false) => {}
            Err(err) => {
                tracing::error!(error = %err, "writing a commit to the write-ahead log failed");
                log.poison(err);
                desc.wake();
            }
        }
    }

    /// Hand the write claim on after a batch that ended at slot `last`, let
    /// go while writers were parked on it: wake the threads parked on the
    /// first record after it that is not written and that somebody waits
    /// for. That thread takes the claim, and its batch begins with the
    /// first record not written. Bounded by the slots decided.
    fn pass_claim(pipe: &Pipeline, last: u64) {
        for index in last + 1..=pipe.ring.decided() {
            match pipe.ring.load(index) {
                Loaded::Ready(desc) => {
                    if unwritten(&desc).is_some() && desc.has_parked() {
                        desc.wake();
                        return;
                    }
                }
                Loaded::Void | Loaded::Gone => {}
                Loaded::Empty | Loaded::Full => return,
            }
        }
    }
}

#[cfg(test)]
#[path = "write_stage_tests.rs"]
mod tests;
