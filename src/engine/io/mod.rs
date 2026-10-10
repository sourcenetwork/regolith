//! Device reads for `CacheOnly` handles, run on per-thread queues (D53).
//!
//! A read through a `CacheOnly` handle never touches the device. When the
//! block cache misses, the read hands the block to a *unit* in the shared
//! table here, records itself on its own queue, and returns
//! `WouldBlock::Io(IoWait)`. The queue's owner runs the unit when it polls,
//! unless another queue's owner already claimed it; whoever runs it fills the
//! block cache and pushes one completion to every queue waiting on it. The
//! read is then run again and finds its block in the cache, or, when the
//! cache did not keep it, in what landed for its queue.
//!
//! # Invariants
//!
//! - **One read per unit.** A unit is claimed by one compare-and-swap and run
//!   by the thread that won it (`unit`). Every read of a block with the same
//!   allocation guard that misses while the unit is in the table joins it,
//!   across every queue.
//! - **Exactly one completion per waiting queue.** The finishing thread
//!   closes the unit's waiter list with one swap and pushes one `Done` to each
//!   queue on it; a queue that registers after the swap is refused and reads
//!   the outcome itself (`unit`, `stack`).
//! - **A completion lands on the queue that asked.** Only the queue a read
//!   names receives its request, and only queues on a unit's list receive its
//!   `Done`.
//! - **What bounds the unit table.** A unit enters the table only with a
//!   request for it, and that request's bytes are reserved against the byte
//!   bound of the queue it names until the request completes (`shared`). A
//!   unit leaves the table when it finishes, when the database closes, or when
//!   the queue that requested it is dropped. So the table never holds more
//!   units than the open queues' byte bounds admit, plus the ones being run
//!   right now.
//! - **No unit outlives close.** A read checks that the database is open
//!   when it starts, and close may come between that check and its miss
//!   (group commit's close flushes and joins its workers after it releases
//!   the units, while reads still in flight go on). Every miss is counted in
//!   one atomic word that close marks with one read-modify-write: a miss
//!   that starts after the mark answers `Closed`, one under way when the mark
//!   lands releases its own unit when it ends, and one that ended before it
//!   inserted its unit where close's sweep, which comes after the mark,
//!   finds it. So once close returns, no unit is left in the table, and every
//!   queue waiting on one has its completion (`NonBlocking.tla`, Release;
//!   the loom model `no_unit_outlives_close`).
//! - **A unit never waits for an open-file slot** (D60). Its reopen under
//!   `max_open_files` sweeps the slot table once; finding every slot in use
//!   by running reads, it parks the unit on the queue running it and the
//!   poll goes on. The read that next frees a slot the park marked wanted
//!   pushes a message to that queue, and its poll unparks and runs the unit
//!   again (`env::open_file_limit::slots`, `OpenFileTable.tla`). A parked
//!   unit stays in the table, so reads of its block join it. Close releases
//!   it like any unit nobody runs; a park that comes after close's sweep sees
//!   the mark (one read-modify-write after the park) and releases the unit
//!   itself.
//!
//! `scope` carries a handle's mode to the device seam; `crate::IoQueue` is
//! the owner's side.

pub(crate) mod atomic_waker;
pub(crate) mod scope;
pub(crate) mod shared;
pub(crate) mod stack;
pub(crate) mod unit;

use std::io;
use std::sync::Arc;

use kovan_map::HashMap;

use super::block::Block;
use super::block_cache::BlockCache;
use super::filter_block::FilterBlock;
use super::index_block::IndexBlock;
use crate::io_queue::{IoWait, QueueId};
use crate::sync::internal::{AtomicUsize, Ordering};
use shared::{Landing, Message, QueueShared, WaitSlot};
use unit::{Ran, Unit, UnitKey, Work};

/// Buckets the unit table starts with; it grows past this on demand.
const UNIT_BUCKETS: usize = 256;
/// Buckets the queue registry starts with.
const QUEUE_BUCKETS: usize = 64;

/// The bit of a [`CloseGate`] close sets. The bits above it count the misses
/// under way, one [`MISS`] each.
const CLOSED: usize = 1;
/// One miss under way in a [`CloseGate`].
const MISS: usize = 2;

/// The one word close and a miss meet on, so no unit outlives close (the
/// module docs): close marks it, and a miss counts itself in before it looks
/// for a unit and out once its unit is in the table.
pub(crate) struct CloseGate(AtomicUsize);

impl CloseGate {
    pub(crate) fn new() -> Self {
        Self(AtomicUsize::new(0))
    }

    /// Count a miss in. `false` once close began: the miss then makes no
    /// unit, and answers `Closed`.
    pub(crate) fn enter(&self) -> bool {
        if self.0.fetch_add(MISS, Ordering::AcqRel) & CLOSED != 0 {
            self.0.fetch_sub(MISS, Ordering::AcqRel);
            return false;
        }
        true
    }

    /// Count a miss out. `true` when close began while the miss was under
    /// way: its sweep may have run before the miss's unit was in the table,
    /// so the miss lets that unit go itself. Otherwise this release is
    /// ordered before close's mark, and the sweep after the mark finds it.
    pub(crate) fn leave(&self) -> bool {
        self.0.fetch_sub(MISS, Ordering::AcqRel) & CLOSED != 0
    }

    /// Mark close, before its sweep.
    pub(crate) fn close(&self) {
        self.0.fetch_or(CLOSED, Ordering::AcqRel);
    }

    /// Whether close began, read by a unit just parked. A read-modify-write,
    /// not a load: either it comes after close's mark and sees it, or the
    /// mark reads it and so close's sweep comes after the park and finds the
    /// unit parked. A plain load could miss the mark while the sweep missed
    /// the park.
    pub(crate) fn closing(&self) -> bool {
        self.0.fetch_or(0, Ordering::AcqRel) & CLOSED != 0
    }

    /// A close that failed: misses make units again.
    pub(crate) fn reopen(&self) {
        self.0.fetch_and(!CLOSED, Ordering::AcqRel);
    }
}

/// What a unit read from the device.
#[derive(Clone)]
pub(crate) enum Landed {
    /// A data block.
    Data(Arc<Block>),
    /// A flat index, a top-level index or a partitioned index leaf.
    Index(Arc<IndexBlock>),
    /// A filter region.
    Filter(Arc<FilterBlock>),
}

impl Landed {
    /// Bytes this costs while held.
    pub(crate) fn charge(&self) -> usize {
        match self {
            Self::Data(block) => block.charge(),
            Self::Index(block) => block.charge(),
            Self::Filter(block) => block.charge(),
        }
    }

    pub(crate) fn into_data(self) -> io::Result<Arc<Block>> {
        match self {
            Self::Data(block) => Ok(block),
            _ => Err(aliased()),
        }
    }

    pub(crate) fn into_index(self) -> io::Result<Arc<IndexBlock>> {
        match self {
            Self::Index(block) => Ok(block),
            _ => Err(aliased()),
        }
    }

    pub(crate) fn into_filter(self) -> io::Result<Arc<FilterBlock>> {
        match self {
            Self::Filter(block) => Ok(block),
            _ => Err(aliased()),
        }
    }
}

/// Two kinds of region at one offset of one table: only a corrupt index can
/// say so, since the layout gives every region its own offset.
fn aliased() -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        "a table names one offset for two kinds of block",
    )
}

/// The table of units in flight and the registry of open queues, for one
/// database. Lives beside its block cache, which every read path already
/// carries to the seam.
pub(crate) struct IoRuntime {
    units: HashMap<UnitKey, Arc<Unit>>,
    queues: HashMap<QueueId, Arc<QueueShared>>,
    /// Where close and the misses meet, so no unit outlives close.
    gate: CloseGate,
}

impl IoRuntime {
    pub(crate) fn new() -> Self {
        Self {
            units: HashMap::with_capacity(UNIT_BUCKETS),
            queues: HashMap::with_capacity(QUEUE_BUCKETS),
            gate: CloseGate::new(),
        }
    }

    /// Open a queue for one owner thread.
    pub(crate) fn open_queue(&self, id: QueueId, bound: usize) -> Arc<QueueShared> {
        let queue = Arc::new(QueueShared::new(id, bound));
        self.queues.insert(id, Arc::clone(&queue));
        queue
    }

    /// Forget a dropped queue: reads that name it from now on fail.
    pub(crate) fn close_queue(&self, id: QueueId) {
        self.queues.remove(&id);
    }

    /// A read in a `CacheOnly` scope on `queue` missed the block cache for
    /// `key`, a read of `bytes` from the device that `work` would do.
    ///
    /// Returns what already landed for the queue, or the error a failed unit
    /// left for it, or an `io::Error` carrying `WouldBlock::Io` after
    /// recording the read on its queue, or `Closed` once the database began
    /// to close. Never reads the device.
    pub(crate) fn miss(
        &self,
        queue: QueueId,
        key: UnitKey,
        bytes: usize,
        work: impl FnOnce() -> io::Result<Work>,
    ) -> io::Result<Landed> {
        if !self.gate.enter() {
            return Err(crate::Error::Closed.into_io_error());
        }
        let missed = self.miss_counted(queue, key, bytes, work);
        if self.gate.leave()
            && let Some(unit) = self.units.get(&key)
        {
            self.release(&unit);
        }
        missed
    }

    /// [`Self::miss`], counted as under way.
    fn miss_counted(
        &self,
        queue: QueueId,
        key: UnitKey,
        bytes: usize,
        work: impl FnOnce() -> io::Result<Work>,
    ) -> io::Result<Landed> {
        let Some(queue) = self.queues.get(&queue) else {
            return Err(queue_gone());
        };
        match queue.landed(&key) {
            Some(Landing::Ready(landed)) => return Ok(landed),
            Some(Landing::Failed(err)) => return Err(crate::Error::clone_io(&err)),
            None => {}
        }
        let slot = Arc::new(WaitSlot::new());
        if !queue.admit(bytes) {
            // The queue owes its whole bound: wait for room instead of adding
            // a unit, and record the read when it is run again.
            if queue.deliver(Message::Room(Arc::clone(&slot))).is_err() {
                return Err(queue_gone());
            }
            return Err(IoWait::new(&queue, None, slot).into_io_error());
        }
        let unit = match self.unit_for(key, bytes, work) {
            Ok(unit) => unit,
            Err(err) => {
                queue.release(bytes);
                return Err(err);
            }
        };
        let request = Message::Read {
            unit: Arc::clone(&unit),
            slot: Arc::clone(&slot),
        };
        if queue.deliver(request).is_err() {
            // The queue was dropped between the lookup and the push. The unit
            // may now be wanted by nobody, so close it; any queue that did
            // want it runs its read again and makes a new one.
            queue.release(bytes);
            self.release(&unit);
            return Err(queue_gone());
        }
        Err(IoWait::new(&queue, Some(key), slot).into_io_error())
    }

    /// The unit in flight for `key`, made from `work` when there is none. A
    /// finished unit still in the table is replaced: its read is over, and
    /// this miss needs a new one.
    fn unit_for(
        &self,
        key: UnitKey,
        bytes: usize,
        work: impl FnOnce() -> io::Result<Work>,
    ) -> io::Result<Arc<Unit>> {
        if let Some(unit) = self.units.get(&key)
            && !unit.is_done()
        {
            return Ok(unit);
        }
        let fresh = Arc::new(Unit::new(key, bytes, work()?));
        loop {
            match self.units.insert_if_absent(key, Arc::clone(&fresh)) {
                None => return Ok(fresh),
                Some(existing) if !existing.is_done() => return Ok(existing),
                Some(finished) => {
                    self.units
                        .remove_if(&key, |unit| Arc::ptr_eq(unit, &finished));
                }
            }
        }
    }

    /// Run a unit this thread claimed for `queue`, reading the device
    /// whatever scope the caller is in, then drop it from the table. A
    /// reopen in it that finds every open-file slot busy parks it on
    /// `queue` instead of waiting (D60): it stays in the table, and the
    /// queue runs it again once told a slot freed.
    pub(crate) fn run(
        &self,
        unit: &Arc<Unit>,
        queue: &Arc<QueueShared>,
        cache: &BlockCache,
    ) -> Ran {
        let ran = {
            let run = scope::unit_run(queue);
            unit.run(cache, || run.parked())
        };
        match ran {
            Ran::Finished => self.forget(unit),
            // Close marks its gate and then sweeps the table: a park that
            // landed after the sweep passed this unit finds the mark here
            // and lets the unit go itself (the module docs).
            Ran::Parked if self.gate.closing() => {
                self.release(unit);
                return Ran::Finished;
            }
            Ran::Parked => {}
        }
        ran
    }

    /// Close `unit` without reading, unless another thread is running it,
    /// and drop it from the table.
    pub(crate) fn release(&self, unit: &Arc<Unit>) {
        if unit.release() {
            self.forget(unit);
        }
    }

    fn forget(&self, unit: &Arc<Unit>) {
        self.units
            .remove_if(&unit.key(), |held| Arc::ptr_eq(held, unit));
    }

    /// `close`: finish every unit nobody is running with nothing read, so
    /// every queue waiting on one gets its completion now. A unit being run
    /// finishes on its own; a read run again after either finds the database
    /// closed. Marked first, so a miss from now on answers `Closed` and a
    /// miss under way lets its own unit go (see the module docs).
    pub(crate) fn close(&self) {
        self.gate.close();
        for unit in self.units.values() {
            self.release(&unit);
        }
    }

    /// A close that failed and left the database open: misses make units
    /// again.
    pub(crate) fn reopen(&self) {
        self.gate.reopen();
    }

    /// Units in the table now.
    #[cfg(test)]
    pub(crate) fn units_in_flight(&self) -> usize {
        self.units.len()
    }

    /// The unit in the table for `key`.
    #[cfg(test)]
    pub(crate) fn unit(&self, key: &UnitKey) -> Option<Arc<Unit>> {
        self.units.get(key)
    }
}

/// The error a read gets when the queue it names is not open on this
/// database.
fn queue_gone() -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidInput,
        "the I/O queue this read names is not open on this database",
    )
}
