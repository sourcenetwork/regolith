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
use crate::engine::io::job::{Delivery, Job};
use crate::engine::io::shared::{Landing, Message, QueueShared, WaitSlot};
use crate::engine::io::unit::{Outcome, Unit, UnitKey};

/// Queue ids are unique in the process, so a handle that names a queue of
/// another database is caught instead of read through a stranger's queue.
static NEXT_QUEUE: AtomicU64 = AtomicU64::new(1);

/// One thread's pending I/O: the blocks its `CacheOnly` handles missed, the
/// fsyncs its [`commit_nowait`](crate::Transaction::commit_nowait) commits
/// owe, the stalls its writes wait out, and the background work its calls
/// left owing with no worker. Made by [`Db::io_queue`](crate::Db::io_queue).
///
/// The thread that holds the queue polls it, and only that thread: it is
/// `Send`, so it can move to the thread that will own it, but not `Sync`, so
/// two threads cannot poll it at once. Handles name it by [`IoQueue::id`] in
/// [`ReadMode::CacheOnly`](crate::ReadMode::CacheOnly); a read through such a
/// handle may run on any thread, and its miss is recorded here all the same.
///
/// [`poll`](Self::poll) runs the reads and jobs this thread waits on and
/// delivers the completions other threads pushed. Every completion of work
/// recorded here arrives here and nowhere else, and wakes only the waits
/// recorded here: a read's [`IoWait`](crate::IoWait), a commit's
/// [`CommitTicket`](crate::CommitTicket), a stall's
/// [`StallWait`](crate::StallWait), a job's [`JobTicket`](crate::JobTicket).
/// A thread with nothing to run registers [`idle_waker`](Self::idle_waker)
/// and idles; the next completion pushed to it wakes it, once.
///
/// The queue is its thread's for the I/O regolith starts itself on that
/// thread's calls: made on a thread, or polled on one, it takes that
/// thread's owed steps, stalls and foreground jobs. A thread with no queue
/// open runs that I/O inline, bounded.
///
/// What a queue owes is bounded by bytes: once the reads it waits on reach
/// the bound (a few hundred blocks of the database's block size), a further
/// miss waits for room instead of adding a read, and records its read when it
/// is run again. One read larger than the bound is still admitted when the
/// queue owes nothing else.
///
/// Dropping the queue completes every wait recorded on it, on the dropping
/// thread; a read run again through a handle that still names it fails with
/// [`Error::InvalidArgument`](crate::Error::InvalidArgument). A read the
/// queue had not finished is closed, and any other queue waiting on it runs
/// its own read again. A commit's fsync the queue waits on is run here if
/// nobody runs it yet, and waited for if another thread does, so every
/// ticket on the queue still gets its true outcome and every callback on it
/// still runs exactly once. A job the queue owns alone is settled without
/// running: the step a write left owing is owed again, and a foreground
/// job's ticket fails, saying the queue that would have run it is gone.
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
    /// The jobs this queue registered on, by address, with what waits on
    /// each.
    jobs: HashMap<usize, JobWait>,
    /// Registered units and jobs in arrival order, for `poll` to run.
    order: VecDeque<Pending>,
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

/// One job this queue waits on.
struct JobWait {
    job: Arc<Job>,
    /// What each call recorded on the queue for this job waits with.
    waiters: Vec<Arc<dyn Delivery>>,
}

/// A unit or a job, in the order `poll` runs them.
enum Pending {
    Read(Arc<Unit>),
    Job(Arc<Job>),
}

/// The `waiting` key of `unit`: its address, unique while `waiting` holds it.
fn address(unit: &Arc<Unit>) -> usize {
    Arc::as_ptr(unit).addr()
}

/// The `jobs` key of `job`: its address, unique while `jobs` holds it.
fn job_address(job: &Arc<Job>) -> usize {
    Arc::as_ptr(job).addr()
}

impl IoQueue {
    /// A new queue on the database `cache` belongs to, owing at most `bound`
    /// bytes of reads.
    pub(crate) fn open(cache: Arc<BlockCache>, bound: usize) -> Self {
        let raw = NEXT_QUEUE.fetch_add(1, Ordering::Relaxed);
        // Starts at one and cannot wrap in a process's lifetime.
        let id = QueueId::new(std::num::NonZeroU64::new(raw).unwrap_or(std::num::NonZeroU64::MIN));
        let shared = cache.io().open_queue(id, bound.max(1));
        shared.own();
        cache.io().bind_current(id);
        Self {
            shared,
            cache,
            waiting: HashMap::new(),
            jobs: HashMap::new(),
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

    /// Run at most `budget` of the reads and jobs this thread waits on, and
    /// take in the completions other threads pushed.
    ///
    /// A read or a job nobody has claimed is claimed with one
    /// compare-and-swap and run here, on this thread: a read fills the block
    /// cache, a commit group's fsync makes the group durable and visible. One
    /// another thread is running is left to it, and its completion arrives
    /// when it is done. Each finished one completes every wait recorded on
    /// this queue for it, waking the tasks that await them and running, on
    /// this thread, the callbacks a commit or a job owes. Returns at once when
    /// the queue owes nothing.
    ///
    /// Only the thread holding the queue calls this; it is the only place a
    /// wait recorded here is completed. A poll also makes this the calling
    /// thread's queue for the I/O regolith starts itself (see the type docs).
    pub fn poll(&mut self, budget: IoBudget) -> IoProgress {
        // The owner is running: a push from now on must not wake it.
        let _ = self.shared.wake_up();
        if self.shared.own() {
            self.cache.io().bind_current(self.id());
        }
        if !self.owes() {
            return IoProgress::default();
        }
        let mut completed = 0;
        self.take_inbox(&mut completed);
        let mut ran = 0;
        while ran < budget.limit() {
            let Some(next) = self.order.pop_front() else {
                break;
            };
            match next {
                Pending::Read(unit) => {
                    if !self.waiting.contains_key(&address(&unit)) {
                        continue;
                    }
                    // Lost the claim: the winner pushes the completion here.
                    if unit.claim() {
                        self.cache.io().run(&unit, &self.cache);
                        ran += 1;
                    }
                }
                Pending::Job(job) => {
                    if !self.jobs.contains_key(&job_address(&job)) {
                        continue;
                    }
                    // A passive job, or one another thread claimed, lands
                    // without this thread; its completion comes here.
                    if job.claim() {
                        self.cache.io().run_job(&job);
                        ran += 1;
                    }
                }
            }
        }
        if ran > 0 {
            // What ran above pushed its completions to this inbox.
            self.take_inbox(&mut completed);
        }
        self.make_room();
        IoProgress {
            completed,
            more_pending: self.owes(),
        }
    }

    /// Run `future` to completion on this thread, polling this queue whenever
    /// the future cannot make progress, and idling, with no busy wait, while
    /// neither can.
    ///
    /// The executor for a caller with nothing else to run: a wait, a commit
    /// ticket, or a [`transact_async`](crate::OptimisticTransactionDb::transact_async)
    /// attempt whose completions are delivered to this queue finishes here.
    /// A future that waits on something no thread will ever complete (a wait
    /// recorded on another queue nobody polls) never returns.
    ///
    /// Not on `wasm32`, which has no thread to park: there the owner polls
    /// the queue from its own event loop when it has nothing else to run.
    #[cfg(not(target_arch = "wasm32"))]
    pub fn block_on<F: std::future::Future>(&mut self, future: F) -> F::Output {
        use std::task::{Context, Poll};

        let mut future = std::pin::pin!(future);
        let waker = Waker::from(Arc::new(Unpark(std::thread::current())));
        let mut cx = Context::from_waker(&waker);
        loop {
            if let Poll::Ready(output) = future.as_mut().poll(&mut cx) {
                return output;
            }
            if self.poll(IoBudget::ALL).completed > 0 {
                continue;
            }
            // Wakes at once when this queue already has work, so the park
            // below returns and the loop polls again.
            self.idle_waker(&waker);
            if let Poll::Ready(output) = future.as_mut().poll(&mut cx) {
                let _ = self.shared.wake_up();
                return output;
            }
            std::thread::park();
        }
    }

    /// The queue waits on something, or holds completions not yet taken in.
    fn owes(&self) -> bool {
        !self.waiting.is_empty()
            || !self.jobs.is_empty()
            || !self.room.is_empty()
            || !self.shared.inbox_is_empty()
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
        let runnable = self.order.iter().any(|pending| match pending {
            Pending::Read(unit) => unit.is_free() && self.waiting.contains_key(&address(unit)),
            Pending::Job(job) => job.is_runnable() && self.jobs.contains_key(&job_address(job)),
        });
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
                Message::Job { job, waiter } => self.accept_job(job, waiter, completed),
                Message::JobDone(job) => {
                    if let Some(wait) = self.jobs.remove(&job_address(&job)) {
                        for waiter in wait.waiters {
                            waiter.deliver();
                        }
                        *completed += 1;
                    }
                }
                Message::Deliver(waiter) => {
                    waiter.deliver();
                    *completed += 1;
                }
            }
        }
    }

    /// Record a wait on `job` on this queue, registering the queue on the job
    /// the first time. A job that landed before the registration is told
    /// here, as its completion would have been.
    fn accept_job(
        &mut self,
        job: Arc<Job>,
        waiter: Option<Arc<dyn Delivery>>,
        completed: &mut usize,
    ) {
        let key = job_address(&job);
        if let Some(wait) = self.jobs.get_mut(&key) {
            wait.waiters.extend(waiter);
            return;
        }
        if job.register(Arc::clone(&self.shared)) {
            self.order.push_back(Pending::Job(Arc::clone(&job)));
            self.jobs.insert(
                key,
                JobWait {
                    job,
                    waiters: waiter.into_iter().collect(),
                },
            );
            return;
        }
        if let Some(waiter) = waiter {
            waiter.deliver();
        }
        *completed += 1;
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
            self.order.push_back(Pending::Read(Arc::clone(&unit)));
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
                // Its unit or job is in `waiting` or `jobs`, and is handled
                // there.
                Message::Done(_) | Message::JobDone(_) => {}
                Message::Job { job, waiter } => {
                    let wait = self
                        .jobs
                        .entry(job_address(&job))
                        .or_insert_with(|| JobWait {
                            job,
                            waiters: Vec::new(),
                        });
                    wait.waiters.extend(waiter);
                }
                Message::Deliver(waiter) => waiter.deliver(),
            }
        }
        // Each job is settled before what waits on it is told, so a commit's
        // ticket is told its group's true outcome.
        for (_, wait) in self.jobs.drain() {
            settle_on_drop(runtime, &wait.job);
            for waiter in wait.waiters {
                waiter.deliver();
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

/// What a dropped queue does with a job it waits on, before it tells the
/// job's waiters. A passive job (a stall) lands with the event it stands
/// for; its waiters are told now and run their call again. A job nobody runs
/// yet is settled here by its body's release: a commit group's fsync runs,
/// an owed step is owed again, a foreground job fails. A job another thread
/// runs is waited for, so its outcome is the one told.
fn settle_on_drop(runtime: &IoRuntime, job: &Arc<Job>) {
    if job.is_done() || job.is_passive() || runtime.release_job(job) {
        return;
    }
    job.wait_landed();
}

/// Wakes a thread parked in [`IoQueue::block_on`].
#[cfg(not(target_arch = "wasm32"))]
struct Unpark(std::thread::Thread);

#[cfg(not(target_arch = "wasm32"))]
impl std::task::Wake for Unpark {
    fn wake(self: Arc<Self>) {
        self.0.unpark();
    }

    fn wake_by_ref(self: &Arc<Self>) {
        self.0.unpark();
    }
}

impl std::fmt::Debug for IoQueue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("IoQueue")
            .field("id", &self.id())
            .field("waiting", &self.waiting.len())
            .field("jobs", &self.jobs.len())
            .field("pending_bytes", &self.shared.pending())
            .finish_non_exhaustive()
    }
}
