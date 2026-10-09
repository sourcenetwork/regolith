//! The owner's side of a per-thread I/O queue.

use crate::portability::{AtomicU64, Ordering};
use std::cell::Cell;
use std::collections::{HashMap, VecDeque};
use std::marker::PhantomData;
use std::sync::Arc;
use std::task::Waker;

use super::{IoBudget, IoProgress, QueueId};
use crate::engine::block_cache::BlockCache;
use crate::engine::io::IoRuntime;
use crate::engine::io::shared::{Landing, Message, QueueShared, WaitSlot};
use crate::engine::io::unit::{Outcome, Unit, UnitKey};

/// Queue ids are unique in the process, so a handle that names a queue of
/// another database is caught instead of read through a stranger's queue.
static NEXT_QUEUE: AtomicU64 = AtomicU64::new(1);

/// One thread's pending device reads: the blocks its `CacheOnly` handles
/// missed. Made by [`Db::io_queue`](crate::Db::io_queue).
///
/// The thread that holds the queue polls it, and only that thread: it is
/// `Send`, so it can move to the thread that will own it, but not `Sync`, so
/// two threads cannot poll it at once. Handles name it by [`IoQueue::id`] in
/// [`ReadMode::CacheOnly`](crate::ReadMode::CacheOnly); a read through such a
/// handle may run on any thread, and its miss is recorded here all the same.
///
/// [`poll`](Self::poll) runs the reads this thread waits on and delivers the
/// completions other threads pushed. Every completion of a read recorded
/// here arrives here and nowhere else, and wakes only the waits of reads
/// recorded here. A thread with nothing to run registers
/// [`idle_waker`](Self::idle_waker) and idles; the next completion pushed to
/// it wakes it, once.
///
/// What a queue owes is bounded by bytes: once the reads it waits on reach
/// the bound (a few hundred blocks of the database's block size), a further
/// miss waits for room instead of adding a read, and records its read when it
/// is run again. One read larger than the bound is still admitted when the
/// queue owes nothing else.
///
/// Dropping the queue completes every wait recorded on it; a read run again
/// through a handle that still names it fails with
/// [`Error::InvalidArgument`](crate::Error::InvalidArgument). A read the
/// queue had not finished is closed, and any other queue waiting on it runs
/// its own read again.
///
/// Two threads cannot share one:
///
/// ```compile_fail
/// fn shared<T: Sync>() {}
/// shared::<regolith::IoQueue>();
/// ```
pub struct IoQueue {
    shared: Arc<QueueShared>,
    /// Holds the database's unit table and is what a unit fills.
    cache: Arc<BlockCache>,
    /// The units this queue registered on, by address, with the reads that
    /// wait on each.
    waiting: HashMap<usize, Waiting>,
    /// Registered units in arrival order, for `poll` to run.
    order: VecDeque<Arc<Unit>>,
    /// Reads that found the byte bound full.
    room: Vec<Arc<WaitSlot>>,
    /// What landed for this queue, oldest first, with what each costs.
    landed: VecDeque<(UnitKey, usize)>,
    landed_bytes: usize,
    /// `Send` but not `Sync`: only the holder polls.
    _owner: PhantomData<Cell<()>>,
}

/// One unit this queue waits on.
struct Waiting {
    unit: Arc<Unit>,
    /// Each read recorded on the queue for this unit.
    slots: Vec<Arc<WaitSlot>>,
}

/// The `waiting` key of `unit`: its address, unique while `waiting` holds it.
fn address(unit: &Arc<Unit>) -> usize {
    Arc::as_ptr(unit).addr()
}

impl IoQueue {
    /// A new queue on the database `cache` belongs to, owing at most `bound`
    /// bytes of reads.
    pub(crate) fn open(cache: Arc<BlockCache>, bound: usize) -> Self {
        let raw = NEXT_QUEUE.fetch_add(1, Ordering::Relaxed);
        // Starts at one and cannot wrap in a process's lifetime.
        let id = QueueId::new(std::num::NonZeroU64::new(raw).unwrap_or(std::num::NonZeroU64::MIN));
        let shared = cache.io().open_queue(id, bound.max(1));
        Self {
            shared,
            cache,
            waiting: HashMap::new(),
            order: VecDeque::new(),
            room: Vec::new(),
            landed: VecDeque::new(),
            landed_bytes: 0,
            _owner: PhantomData,
        }
    }

    /// The name handles carry in [`ReadMode::CacheOnly`](crate::ReadMode::CacheOnly).
    pub fn id(&self) -> QueueId {
        self.shared.id()
    }

    /// Bytes of device reads this queue owes now: one block per read
    /// recorded on it and not yet completed. At most the queue's bound,
    /// except for one read larger than the bound, admitted alone.
    pub fn pending_bytes(&self) -> usize {
        self.shared.pending()
    }

    /// Run at most `budget` of the reads this thread waits on, and take in
    /// the completions other threads pushed.
    ///
    /// A read nobody has claimed is claimed with one compare-and-swap and run
    /// here, on this thread, filling the block cache; a read another thread
    /// is running is left to it, and its completion arrives when it is done.
    /// Each finished read completes every wait recorded on this queue for it,
    /// waking the tasks that await them. Returns at once when the queue owes
    /// nothing.
    ///
    /// Only the thread holding the queue calls this; it is the only place a
    /// wait recorded here is completed.
    pub fn poll(&mut self, budget: IoBudget) -> IoProgress {
        // The owner is running: a push from now on must not wake it.
        let _ = self.shared.wake_up();
        if self.waiting.is_empty() && self.room.is_empty() && self.shared.inbox_is_empty() {
            return IoProgress::default();
        }
        let mut completed = 0;
        self.take_inbox(&mut completed);
        let mut ran = 0;
        while ran < budget.limit() {
            let Some(unit) = self.order.pop_front() else {
                break;
            };
            if !self.waiting.contains_key(&address(&unit)) {
                continue;
            }
            // Lost the claim: the winner pushes the completion here.
            if unit.claim() {
                self.cache.io().run(&unit, &self.cache);
                ran += 1;
            }
        }
        if ran > 0 {
            // The units run above pushed their completions to this inbox.
            self.take_inbox(&mut completed);
        }
        self.make_room();
        IoProgress {
            completed,
            more_pending: !self.waiting.is_empty()
                || !self.room.is_empty()
                || !self.shared.inbox_is_empty(),
        }
    }

    /// Register `waker` as this thread is about to idle: the next completion
    /// pushed to this queue wakes it, once. A queue whose owner is running is
    /// never woken; it sees its completions at its next [`poll`](Self::poll),
    /// which also cancels the registration.
    ///
    /// When something is already waiting to be taken in, or a read only this
    /// thread can run is pending, `waker` is woken at once: the owner has work
    /// and should poll rather than idle.
    pub fn idle_waker(&self, waker: &Waker) {
        let runnable = self
            .order
            .iter()
            .any(|unit| unit.is_free() && self.waiting.contains_key(&address(unit)));
        if runnable {
            waker.wake_by_ref();
            return;
        }
        self.shared.rest(waker);
    }

    fn take_inbox(&mut self, completed: &mut usize) {
        for message in self.shared.take_inbox() {
            match message {
                Message::Read { unit, slot } => self.accept(unit, slot, completed),
                Message::Room(slot) => self.room.push(slot),
                Message::Done(unit) => {
                    if let Some(waiting) = self.waiting.remove(&address(&unit)) {
                        self.land(&unit);
                        self.complete(&unit, waiting.slots);
                        *completed += 1;
                    }
                }
            }
        }
    }

    /// Record a read of `unit` on this queue, registering the queue on the
    /// unit the first time. A unit that finished before the registration is
    /// read here, as its completion would have been.
    fn accept(&mut self, unit: Arc<Unit>, slot: Arc<WaitSlot>, completed: &mut usize) {
        if let Some(waiting) = self.waiting.get_mut(&address(&unit)) {
            waiting.slots.push(slot);
            return;
        }
        if unit.register(Arc::clone(&self.shared)) {
            self.order.push_back(Arc::clone(&unit));
            self.waiting.insert(
                address(&unit),
                Waiting {
                    unit,
                    slots: vec![slot],
                },
            );
            return;
        }
        self.land(&unit);
        self.complete(&unit, vec![slot]);
        *completed += 1;
    }

    /// Complete `slots`, reads of `unit`, and give back the bytes they owed.
    fn complete(&self, unit: &Unit, slots: Vec<Arc<WaitSlot>>) {
        for slot in slots {
            self.shared.release(unit.bytes());
            slot.complete();
        }
    }

    /// Keep what `unit` read, or the error it met, for the reads run again on
    /// this queue, and let the oldest landings go past the byte bound.
    fn land(&mut self, unit: &Unit) {
        let (landing, charge) = match unit.outcome() {
            Some(Outcome::Landed(landed)) => (Landing::Ready(landed.clone()), landed.charge()),
            Some(Outcome::Failed(err)) => (
                Landing::Failed(Arc::clone(err)),
                std::mem::size_of::<std::io::Error>(),
            ),
            Some(Outcome::Released) | None => return,
        };
        self.shared.land(unit.key(), landing);
        self.landed.push_back((unit.key(), charge));
        self.landed_bytes = self.landed_bytes.saturating_add(charge);
        while self.landed_bytes > self.shared.bound() && self.landed.len() > 1 {
            let Some((key, charge)) = self.landed.pop_front() else {
                break;
            };
            self.landed_bytes -= charge;
            if !self.landed.iter().any(|(held, _)| *held == key) {
                self.shared.forget(&key);
            }
        }
    }

    /// Wake the reads that waited for room, once the queue owes less than its
    /// bound.
    fn make_room(&mut self) {
        if !self.room.is_empty() && self.shared.pending() < self.shared.bound() {
            for slot in self.room.drain(..) {
                slot.complete();
            }
        }
    }

    /// The database's unit table.
    #[cfg(test)]
    pub(crate) fn runtime(&self) -> &IoRuntime {
        self.cache.io()
    }
}

impl Drop for IoQueue {
    fn drop(&mut self) {
        let runtime: &IoRuntime = self.cache.io();
        runtime.close_queue(self.shared.id());
        // Every later push is refused, so nothing is left behind unread.
        for message in self.shared.shut_inbox() {
            match message {
                Message::Read { unit, slot } => {
                    self.shared.release(unit.bytes());
                    slot.complete();
                    if !self.waiting.contains_key(&address(&unit)) {
                        runtime.release(&unit);
                    }
                }
                Message::Room(slot) => slot.complete(),
                // Its unit is in `waiting`, and is handled there.
                Message::Done(_) => {}
            }
        }
        for (_, waiting) in self.waiting.drain() {
            runtime.release(&waiting.unit);
            for slot in waiting.slots {
                slot.complete();
            }
        }
        for slot in self.room.drain(..) {
            slot.complete();
        }
        for (key, _) in self.landed.drain(..) {
            self.shared.forget(&key);
        }
    }
}

impl std::fmt::Debug for IoQueue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("IoQueue")
            .field("id", &self.id())
            .field("waiting", &self.waiting.len())
            .field("pending_bytes", &self.shared.pending())
            .finish_non_exhaustive()
    }
}
