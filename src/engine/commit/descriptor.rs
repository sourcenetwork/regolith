//! What a slot of the commit ring holds: the work a committer handed over,
//! and what the pipeline decided for it.
//!
//! A [`Descriptor`] is installed in the ring by its owner and then read by
//! every thread that helps the slot along, so everything in it is either
//! immutable (the work) or an atomic that only moves forward (the decision,
//! the stage flags). Nothing in it is ever taken back out: that is what lets
//! two threads work on one slot at once without a lock.
//!
//! # Invariants
//!
//! - **D1, one decision.** [`Descriptor::decide`] installs a slot's
//!   [`Decision`] by one compare-and-swap. Every thread that computed one
//!   for the slot proceeds with the one that was installed, whoever built
//!   it, so the sequences, the log position and the verdict of a slot are
//!   the same for every thread (model action `DecideCas`).
//! - **D2, stages are flags that are set once.** `APPLIED`, `WRITTEN` and
//!   `FAILED` are set by whichever thread finishes the stage, after its
//!   work, and never cleared. A thread that sees a flag set skips the stage;
//!   one that does not repeats work that is idempotent.
//! - **D3, a decision is a pure record.** It owns what later stages need
//!   (the batch a transaction's appends were numbered into, the record's
//!   place) and names the memtable and the log through its [`After`], so a
//!   stage never reads state that a later slot may have changed.

#![allow(unsafe_code)]

use std::io;
use std::ops::Range;
use std::ptr;
use std::sync::Arc;

// A parked thread is unparked through loom in a loom build, so the model
// sees whether a wake can be lost.
#[cfg(loom)]
use loom::thread::{self, Thread};
#[cfg(not(loom))]
use std::thread::{self, Thread};

use super::super::DurabilityMode;
use super::super::io::job::{Delivery, Job};
use super::super::io::stack::{SHUT, Stack};
use super::super::memtable::MemTable;
use super::super::take::Take;
use super::super::wal_log::{Log, Place};
use super::WriteRequest;
use super::ring::Linked;
use crate::perf_context::PerfContextSnapshot;
use crate::sync::internal::{Arc as RingArc, AtomicPtr, AtomicU64, Ordering, take_ptr};
use crate::{Conflict, QueueId, WriteBatchOp};

/// An `Arc<T>` (the ring's kind, which a loom build swaps) set at most once and then read by any thread for as long as
/// the cell lives.
pub(super) struct OnceArc<T>(AtomicPtr<T>);

// SAFETY: the cell hands out `&T` and `RingArc<T>` and may drop the `T` on any
// thread, which is what `RingArc<T>: Send + Sync` asks of `T`.
unsafe impl<T: Send + Sync> Send for OnceArc<T> {}
// SAFETY: as above; the one field is an atomic.
unsafe impl<T: Send + Sync> Sync for OnceArc<T> {}

impl<T> OnceArc<T> {
    pub(super) fn empty() -> Self {
        Self(AtomicPtr::new(ptr::null_mut()))
    }

    /// Set the cell to `value` if it is empty. When another thread set it
    /// first, `value` is handed back.
    pub(super) fn set(&self, value: RingArc<T>) -> Result<(), RingArc<T>> {
        let raw = RingArc::into_raw(value).cast_mut();
        if self
            .0
            .compare_exchange(ptr::null_mut(), raw, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
        {
            return Ok(());
        }
        // SAFETY: `raw` came from `RingArc::into_raw` above and was not stored.
        Err(unsafe { RingArc::from_raw(raw.cast_const()) })
    }

    /// The value, once set.
    pub(super) fn get(&self) -> Option<&T> {
        let raw = self.0.load(Ordering::Acquire);
        // SAFETY: a non-null pointer is the cell's own reference, never
        // replaced or dropped before the cell is, and the borrow does not
        // outlive `self`.
        unsafe { raw.as_ref() }
    }

    /// The value, once set, as a reference of the caller's own.
    pub(super) fn get_arc(&self) -> Option<RingArc<T>> {
        let raw = self.0.load(Ordering::Acquire).cast_const();
        if raw.is_null() {
            return None;
        }
        // SAFETY: as in `get`: the cell holds its reference for as long as
        // `self` lives, so a new one can be taken from it.
        Some(unsafe {
            RingArc::increment_strong_count(raw);
            RingArc::from_raw(raw)
        })
    }
}

impl<T> Drop for OnceArc<T> {
    fn drop(&mut self) {
        let raw = take_ptr(&mut self.0);
        if !raw.is_null() {
            // SAFETY: the cell's own reference, dropped once, here.
            drop(unsafe { RingArc::from_raw(raw.cast_const()) });
        }
    }
}

/// A `T` set at most once and then read by any thread for as long as the
/// cell lives.
pub(super) struct Once<T>(AtomicPtr<T>);

// SAFETY: the cell hands out `&T` and may drop the `T` on any thread.
unsafe impl<T: Send + Sync> Send for Once<T> {}
// SAFETY: as above; the one field is an atomic.
unsafe impl<T: Send + Sync> Sync for Once<T> {}

impl<T> Once<T> {
    pub(super) fn empty() -> Self {
        Self(AtomicPtr::new(ptr::null_mut()))
    }

    /// Set the cell to `value` if it is empty, and return what it holds
    /// afterwards: `value`, or what another thread set first.
    pub(super) fn get_or_set(&self, value: T) -> &T {
        let raw = Box::into_raw(Box::new(value));
        let held =
            match self
                .0
                .compare_exchange(ptr::null_mut(), raw, Ordering::AcqRel, Ordering::Acquire)
            {
                Ok(_) => raw,
                Err(first) => {
                    // SAFETY: `raw` came from `Box::into_raw` above and was not
                    // stored.
                    drop(unsafe { Box::from_raw(raw) });
                    first
                }
            };
        // SAFETY: a stored pointer is the cell's own box, never replaced or
        // freed before the cell is, and the borrow does not outlive `self`.
        unsafe { &*held }
    }

    /// The value, once set.
    pub(super) fn get(&self) -> Option<&T> {
        // SAFETY: as in `get_or_set`.
        unsafe { self.0.load(Ordering::Acquire).as_ref() }
    }
}

impl<T> Drop for Once<T> {
    fn drop(&mut self) {
        let raw = take_ptr(&mut self.0);
        if !raw.is_null() {
            // SAFETY: the cell's own box, freed once, here.
            drop(unsafe { Box::from_raw(raw) });
        }
    }
}

/// The state the pipeline is in after a slot: what the next slot is decided
/// from. Every field is fixed when the slot is decided.
#[derive(Clone)]
pub(crate) struct After {
    /// The sequence the next commit's first operation takes.
    pub(crate) next_seq: u64,
    /// The log the next commit's record goes to.
    pub(crate) log: Arc<Log>,
    /// The offset that record starts at.
    pub(crate) next_off: u64,
    /// The memtable the next commit is applied to.
    pub(crate) memtable: Arc<MemTable>,
    /// An upper bound on the bytes that memtable holds, counted from the
    /// commits decided into it. When it reaches the write buffer size the
    /// next write's turn begins with the rotation check.
    pub(crate) mem_used: usize,
    /// The database closed: every later commit is refused.
    pub(crate) closed: bool,
    /// How many rollbacks the pipeline has made. A decision carries the
    /// epoch of the state it was computed from; one whose epoch is not the
    /// tip's was computed from a state a rollback has since discarded, and
    /// lands nothing (`pipeline.rs`, P4). It is also the write epoch of
    /// `log`: a record placed in an older epoch is not written.
    pub(crate) epoch: u64,
    /// The counters reservations have read or set, at their values as of
    /// this state (`counters.rs`).
    pub(crate) counters: super::counters::Counters,
}

/// What the pipeline decided for one slot.
pub(super) enum Verdict {
    /// A plain write: it takes its sequences and its record.
    Write,
    /// A transaction that validated. The counts are recorded once it lands.
    Commit {
        merges_commuted: u64,
        writes_elided: u64,
    },
    /// A transaction that lost a race; the key still carries its
    /// column-family prefix. It takes nothing.
    Conflict(Conflict),
    /// A commit refused before it took anything: a dropped column family, a
    /// closed or latched database, its own check failing.
    Refused(io::Error),
    /// A counter reservation: the values it reserved.
    Allocated(Range<u64>),
    /// An ordered unit ran.
    Unit,
}

/// One slot's decision (D1, D3).
pub(crate) struct Decision {
    /// The slot it decides.
    pub(super) index: u64,
    pub(super) verdict: Verdict,
    /// The first sequence the slot took; meaningful when `ops > 0`.
    pub(super) base_seq: u64,
    /// Sequences the slot took: one per operation, none for a slot that
    /// writes nothing.
    pub(super) ops: u64,
    /// Where its record goes, or `None` for a slot with no record.
    pub(super) place: Option<Place>,
    /// Whether the slot is published only once its record is durable.
    pub(super) immediate: bool,
    /// The operations the slot lands as when they are not the request's own:
    /// a transaction whose appends were numbered, a counter reservation.
    pub(super) batch: Option<Vec<WriteBatchOp>>,
    /// What deciding the slot counted, for its own thread's perf context.
    /// Boxed: only a thread that counts sets it, and every decision is
    /// moved into its allocation whole.
    pub(super) perf: Option<Box<PerfContextSnapshot>>,
    /// The pipeline's state after the slot. A slot that writes is applied
    /// to `after.memtable` and logged to `after.log`.
    pub(crate) after: After,
    /// [`Linked`]: the pipeline's tip list.
    link: AtomicPtr<Decision>,
}

impl Decision {
    pub(super) fn new(index: u64, verdict: Verdict, after: After) -> Self {
        Self {
            index,
            verdict,
            base_seq: 0,
            ops: 0,
            place: None,
            immediate: false,
            batch: None,
            perf: None,
            after,
            link: AtomicPtr::new(ptr::null_mut()),
        }
    }

    /// The last sequence the slot took, when it took any.
    pub(super) fn last_seq(&self) -> Option<u64> {
        (self.ops > 0).then(|| self.base_seq + self.ops - 1)
    }

    /// Whether the slot lands data: it has operations to apply.
    pub(super) fn commits(&self) -> bool {
        self.ops > 0
    }
}

impl Linked for Decision {
    fn link(&self) -> &AtomicPtr<Self> {
        &self.link
    }

    fn retired(value: RingArc<Self>) {
        super::spare::keep_decision(value);
    }
}

/// What the rotation check at a slot's turn left: the error the slot is
/// refused with when the rotation failed part way. The state it left, rotated
/// or not, is the pipeline's tip.
pub(super) struct Turned {
    pub(super) refused: Option<io::Error>,
}

/// The work a slot carries.
pub(super) enum Work {
    /// A plain write or a transaction's commit.
    Request(WriteRequest),
    /// Reserve `n` values of the counter at `key` (`allocate.rs`). With a
    /// `read_queue` the counter is read from the cache alone, as a
    /// `CacheOnly` commit's validation is (`read_mode.rs`).
    Allocate {
        key: Vec<u8>,
        n: u64,
        read_queue: Option<QueueId>,
    },
    /// An ordered unit (`ordered.rs`): its body runs when the slot's turn
    /// comes, on whichever thread claims the job. `index` tells the body
    /// which slot it is, since a job knows nothing of the ring; `needs` is
    /// what the body may wait for, which a queue's poll takes before it
    /// begins (`park.rs`).
    Unit {
        job: Arc<Job>,
        index: Arc<crate::portability::AtomicU64>,
        needs: super::park::Needs,
    },
}

/// The slot's operations are in its memtable.
pub(super) const APPLIED: u64 = 1;
/// The slot's record is in the log.
pub(super) const WRITTEN: u64 = 1 << 1;
/// A rollback discarded the slot: its owner learns the failure.
pub(super) const FAILED: u64 = 1 << 2;
/// A thread is deciding the slot. A hint: another thread that needs the
/// decision gives this one a moment before it repeats the work. The thread
/// that claims it claims [`APPLYING`] in the same instruction, since it goes
/// on to apply what it decided.
pub(super) const DECIDING: u64 = 1 << 3;
/// A thread is applying the slot's operations. A hint, as [`DECIDING`].
pub(super) const APPLYING: u64 = 1 << 5;
/// The descriptor is in the ring: its index is the slot it holds. Set by
/// its owner, which is the only thread that reads it, and only on a
/// descriptor that is not [`Descriptor::is_blocking`].
pub(super) const INSTALLED: u64 = 1 << 6;
/// A `commit_nowait` commit has the write-stall admission behind it, or
/// needs none because it writes nothing: it may take a slot. Set by its
/// owner, which is the only thread that reads it.
pub(super) const ADMITTED: u64 = 1 << 7;
/// An `allocate_nowait` caller gave its reservation up before the slot was
/// decided: whoever decides it refuses it. Set by its owner.
pub(super) const ABANDONED: u64 = 1 << 8;
/// A thread parked on the slot ([`Descriptor::park`]): whoever sets
/// [`WRITTEN`] or [`FAILED`] wakes it, and so does whoever passes the decided
/// frontier over the slot or hands the log's write claim on to it. Never
/// cleared: a wake that finds nobody left costs a look at an empty list.
pub(super) const PARKED: u64 = 1 << 9;

/// One slot's descriptor. See the module docs.
pub(crate) struct Descriptor {
    /// The slot index, set by the owner before each install attempt. A
    /// descriptor is seen by other threads only once an install succeeded,
    /// and is never installed again after that.
    index: AtomicU64,
    pub(super) work: Work,
    decision: OnceArc<Decision>,
    /// The rotation check that ran at this slot's turn, when one was due:
    /// why the slot is refused when the rotation failed.
    pub(super) turn: Once<Turned>,
    /// The unit that runs that rotation check, made by the first thread
    /// that finds it due.
    pub(super) turn_job: Once<Arc<Job>>,
    /// The unit that decides the slot with the device, made by the first
    /// thread that could not: one that must not read the device and found a
    /// block the slot's validation needs missing (`read_mode.rs`).
    pub(super) decide_job: Once<Arc<Job>>,
    flags: AtomicU64,
    /// Why a rollback discarded the slot.
    pub(super) failure: Take<io::Error>,
    /// A unit's body, taken by the thread that runs it.
    pub(super) body: Take<super::ordered::Body>,
    /// Who is told, on the landing thread, when the slot lands: a
    /// pessimistic commit's key locks, released then. Closed with [`SHUT`].
    landing: Stack<Arc<dyn Delivery>>,
    /// Threads parked on the slot ([`Self::park`]). Never closed: a parked
    /// thread looks again at what it waits for after it is on the list, so a
    /// wake that comes before it parks is not lost.
    sleepers: Stack<Thread>,
    /// See [`Self::is_blocking`].
    blocking: bool,
}

impl Descriptor {
    /// A descriptor for `work`. `blocking`: see [`Self::is_blocking`].
    pub(super) fn new(work: Work, blocking: bool) -> Self {
        Self {
            index: AtomicU64::new(0),
            work,
            decision: OnceArc::empty(),
            turn: Once::empty(),
            turn_job: Once::empty(),
            decide_job: Once::empty(),
            flags: AtomicU64::new(0),
            failure: Take::empty(),
            body: Take::empty(),
            landing: Stack::new(),
            sleepers: Stack::new(),
            blocking,
        }
    }

    /// Whether the descriptor is a blocking call's: its owner brings the slot
    /// through itself and returns once it is published, so nothing listens
    /// for its landing ([`Self::listen`] is never called on it) and the owner
    /// never asks whether it is installed. Its owner sets no [`INSTALLED`]
    /// flag, and [`Self::land`] has nobody to tell: two locked instructions a
    /// commit saves.
    pub(super) fn is_blocking(&self) -> bool {
        self.blocking
    }

    /// Tell `waiter`, on the landing thread, when the slot lands: when its
    /// commit is visible to readers, or discarded. `false` when it already
    /// landed: the caller tells `waiter` itself.
    pub(super) fn listen(&self, waiter: Arc<dyn Delivery>) -> bool {
        debug_assert!(!self.blocking, "a blocking call's commit has no listener");
        self.landing.push(waiter, SHUT).is_ok()
    }

    /// Refuse a commit that has not taken a slot, with `err`: its owner
    /// learns `err` as it learns a discarded slot's failure, and whoever
    /// listens for its landing is told now. Called by its owner.
    pub(super) fn refuse(&self, err: io::Error) {
        self.failure.put(err);
        self.mark(FAILED);
        self.land();
    }

    /// Whether the commit was refused before it took a slot
    /// ([`Self::refuse`]).
    pub(super) fn is_refused(&self) -> bool {
        !self.blocking && self.is(FAILED) && !self.is(INSTALLED)
    }

    /// Tell everyone listening that the slot landed. Every thread that
    /// publishes the slot calls this before it passes the frontier, and one
    /// of them tells each listener, so a thread that stops before it takes
    /// the listeners keeps none waiting: the next one to reach the slot
    /// tells them. A thread stopped after it took them keeps the ones it
    /// took until it runs again.
    pub(super) fn land(&self) {
        if self.blocking {
            return;
        }
        for waiter in self.landing.take(SHUT) {
            waiter.deliver();
        }
    }

    /// The slot this descriptor is installed at.
    pub(super) fn index(&self) -> u64 {
        self.index.load(Ordering::Acquire)
    }

    /// Name the slot the owner is about to install at.
    pub(super) fn set_index(&self, index: u64) {
        self.index.store(index, Ordering::Release);
        if let Work::Unit { index: told, .. } = &self.work {
            told.store(index, crate::portability::Ordering::Release);
        }
    }

    /// The slot's decision, once it has one.
    pub(super) fn decision(&self) -> Option<&Decision> {
        self.decision.get()
    }

    /// The slot's decision as a reference of the caller's own.
    pub(super) fn decision_arc(&self) -> Option<RingArc<Decision>> {
        self.decision.get_arc()
    }

    /// Install `decision` if the slot has none (D1). Either way the slot's
    /// decision is the one [`Self::decision`] returns afterwards.
    pub(super) fn decide(&self, decision: Decision) -> bool {
        match self.decision.set(super::spare::decision(decision)) {
            Ok(()) => true,
            Err(lost) => {
                // Nobody else ever saw it: its allocation serves again.
                super::spare::keep_decision(lost);
                false
            }
        }
    }

    /// The queue the slot's own validation reads send their misses to: set
    /// for a transaction committed without waiting through a `CacheOnly`
    /// handle, whose validation never reads the device.
    pub(super) fn read_queue(&self) -> Option<QueueId> {
        match &self.work {
            Work::Request(WriteRequest::Txn(txn)) => txn.read_queue,
            Work::Allocate { read_queue, .. } => *read_queue,
            _ => None,
        }
    }

    /// A measure of what deciding the slot costs: the items a transaction
    /// validates, or one for anything else.
    pub(super) fn work_size(&self) -> usize {
        match &self.work {
            Work::Request(WriteRequest::Txn(txn)) => {
                txn.checks.reads.len() + txn.checks.ranges.len() + txn.ops.len()
            }
            _ => 1,
        }
    }

    /// Whether every flag of `mask` is set.
    pub(super) fn is(&self, mask: u64) -> bool {
        self.flags.load(Ordering::Acquire) & mask == mask
    }

    /// Set the flags of `mask` (D2). `true` when this call set one of them.
    /// Setting [`WRITTEN`] or [`FAILED`] wakes every thread parked on the
    /// slot: the flag and [`PARKED`] share this word, so of a waiter's
    /// read-modify-write and this one the later sees the earlier.
    pub(super) fn mark(&self, mask: u64) -> bool {
        let before = self.flags.fetch_or(mask, Ordering::AcqRel);
        if before & PARKED != 0 && mask & (WRITTEN | FAILED) != 0 {
            self.wake();
        }
        before & mask != mask
    }

    /// Park this thread on the slot for at most `patience`, unless `ready`
    /// holds once the thread is on the slot's list. `true` when it held and
    /// the thread did not park. Whoever makes `ready` hold changes what it
    /// reads first and then looks for [`PARKED`] (or reads a count the
    /// caller made after this returns), so one of the two sees the other.
    /// A loom build parks until it is woken: the model then shows that the
    /// wake comes, with no time to fall back on.
    pub(super) fn park(&self, patience: std::time::Duration, ready: impl Fn() -> bool) -> bool {
        // A list that never closes takes every push.
        let _ = self.sleepers.push(thread::current(), 0);
        self.flags.fetch_or(PARKED, Ordering::SeqCst);
        if ready() {
            return true;
        }
        super::super::io::scope::waits(
            "a slot's record or its decision, under way on another thread",
        );
        #[cfg(not(loom))]
        thread::park_timeout(patience);
        #[cfg(loom)]
        {
            let _ = patience;
            thread::park();
        }
        false
    }

    /// Whether a thread parked on the slot since it was made.
    pub(super) fn has_parked(&self) -> bool {
        self.flags.load(Ordering::SeqCst) & PARKED != 0
    }

    /// Wake every thread parked on the slot. Each looks again at what it
    /// waits for, and parks again if it still waits.
    pub(super) fn wake(&self) {
        for sleeper in self.sleepers.take_open() {
            sleeper.unpark();
        }
    }

    /// Set the flags of `mask` and return every flag as it was before: one
    /// locked instruction that claims several hints and says which of them
    /// this call claimed.
    pub(super) fn claim(&self, mask: u64) -> u64 {
        self.flags.fetch_or(mask, Ordering::AcqRel)
    }

    /// Clear the hints of `mask`, which this thread claimed and gives up.
    pub(super) fn unclaim(&self, mask: u64) {
        self.flags.fetch_and(!mask, Ordering::AcqRel);
    }
}

impl std::fmt::Debug for Descriptor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Descriptor")
            .field("index", &self.index())
            .field("decided", &self.decision().is_some())
            .field("flags", &self.flags.load(Ordering::Acquire))
            .finish_non_exhaustive()
    }
}

/// Whether a slot's durability is `Immediate`.
pub(super) fn is_immediate(durability: DurabilityMode) -> bool {
    matches!(durability, DurabilityMode::Immediate)
}
