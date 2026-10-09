//! The phase-fair core of [`RwLock`](super::RwLock), which
//! [`ReentrantRwLock`](super::ReentrantRwLock) builds on.
//!
//! Phase-fair means readers and writers take turns whenever both wait:
//! when a writer leaves, every reader waiting at that moment enters
//! together, and when that reader phase drains, the oldest waiting writer
//! enters. A reader arriving while a writer waits waits for that writer,
//! so neither side starves: a reader waits for at most one writer phase,
//! and a writer for at most one reader phase per writer ahead of it.
//!
//! The state word holds the reader count, a writer bit, which kind of
//! phase admitted the lock last, and a queued flag per waiting kind. An
//! upgrade (a reader of a [`ReentrantRwLock`](super::ReentrantRwLock)
//! asking to write) queues ahead of plain writers, which could not run
//! before it gives up its read anyway, and is granted when its own read is
//! the only one left.

#![allow(unsafe_code)]

use core::task::{Poll, Waker};

use super::internal::{Ordering, UnsafeCell};
use super::list::List;
use super::queue::{Arrivals, FIRST_BIT, Policy, Step, WaitQueue};
use super::waiter::{Cancel, Wait, WakeList, release_queued};

const QUEUED_R: usize = 1 << FIRST_BIT;
const QUEUED_W: usize = 1 << (FIRST_BIT + 1);
const WRITER: usize = 1 << (FIRST_BIT + 2);
/// The phase that last admitted anyone was a reader phase.
const LAST_READ: usize = 1 << (FIRST_BIT + 3);
const READER_SHIFT: u32 = FIRST_BIT + 4;
const ONE_READER: usize = 1 << READER_SHIFT;
const MAX_READERS: usize = usize::MAX >> READER_SHIFT;

/// What a waiter asks for.
pub(super) const READ: usize = 0;
pub(super) const WRITE: usize = 1;
/// A write by a reader that keeps its read until the write is granted.
pub(super) const UPGRADE: usize = 2;

fn readers(state: usize) -> usize {
    state >> READER_SHIFT
}

fn add_reader(state: usize) -> usize {
    assert!(
        readers(state) < MAX_READERS,
        "too many readers hold one RwLock"
    );
    (state + ONE_READER) | LAST_READ
}

struct Waiting {
    readers: List,
    writers: List,
    upgrades: List,
}

/// The phase-fair core with no value attached.
pub(super) struct RawRwLock {
    queue: WaitQueue,
    waiting: UnsafeCell<Waiting>,
}

// SAFETY: the waiting lists are touched only by the drain role's holder.
unsafe impl Send for RawRwLock {}
// SAFETY: as above.
unsafe impl Sync for RawRwLock {}

impl RawRwLock {
    loom_const_fn! {
        pub(super) fn new() -> Self {
            Self {
                queue: WaitQueue::new(LAST_READ),
                waiting: UnsafeCell::new(Waiting {
                    readers: List::new(),
                    writers: List::new(),
                    upgrades: List::new(),
                }),
            }
        }
    }

    pub(super) fn try_read(&self) -> bool {
        let mut state = self.queue.state.load(Ordering::Relaxed);
        loop {
            if state & (WRITER | QUEUED_W) != 0 {
                return false;
            }
            match self.queue.state.compare_exchange_weak(
                state,
                add_reader(state),
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => return true,
                Err(actual) => state = actual,
            }
        }
    }

    /// Takes the write side; `held` is 1 when the caller converts its own
    /// read into the write.
    fn try_write_holding(&self, held: usize) -> bool {
        let mut state = self.queue.state.load(Ordering::Relaxed);
        loop {
            if state & (WRITER | QUEUED_W | QUEUED_R) != 0 || readers(state) != held {
                return false;
            }
            let next = ((state - held * ONE_READER) | WRITER) & !LAST_READ;
            match self.queue.state.compare_exchange_weak(
                state,
                next,
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => return true,
                Err(actual) => state = actual,
            }
        }
    }

    pub(super) fn try_write(&self) -> bool {
        self.try_write_holding(0)
    }

    /// Converts the caller's read into the write if it is the only one.
    pub(super) fn try_upgrade(&self) -> bool {
        self.try_write_holding(1)
    }

    pub(super) fn try_kind(&self, kind: usize) -> bool {
        match kind {
            READ => self.try_read(),
            WRITE => self.try_write(),
            _ => self.try_upgrade(),
        }
    }

    /// Drops one read. One `fetch_sub` when nobody waits; a waiter that
    /// queues concurrently was either flagged already, and is drained
    /// here, or flags itself afterwards and sees the read gone.
    pub(super) fn read_unlock(&self) {
        let before = self.queue.state.fetch_sub(ONE_READER, Ordering::AcqRel);
        // One reader left may be an upgrader waiting for exactly that.
        if readers(before) <= 2 && before & (QUEUED_R | QUEUED_W) != 0 {
            self.transition(Step::Drain);
        }
    }

    /// Drops the write, the same way [`read_unlock`](Self::read_unlock)
    /// drops a read.
    pub(super) fn write_unlock(&self) {
        let before = self.queue.state.fetch_and(!WRITER, Ordering::AcqRel);
        if before & (QUEUED_R | QUEUED_W) != 0 {
            self.transition(Step::Drain);
        }
    }

    /// Turns the held write into a read, letting the readers waiting
    /// behind the writer phase in with it.
    pub(super) fn downgrade(&self) {
        self.transition(|state| {
            let next = (state & !WRITER) + ONE_READER;
            if state & (QUEUED_R | QUEUED_W) != 0 {
                Step::Drain(next)
            } else {
                Step::Set(next)
            }
        });
    }

    /// Gives back what a granted `kind` holds.
    pub(super) fn unlock_kind(&self, kind: usize) {
        match kind {
            READ => self.read_unlock(),
            WRITE => self.write_unlock(),
            _ => self.downgrade(),
        }
    }

    /// Admits every waiting reader. False when a writer got in first.
    fn admit_readers(&self, readers: &mut List, woken: &mut WakeList<'_>) -> bool {
        let pool = self.queue.pool();
        while let Some(node) = readers.front(pool) {
            let mut state = self.queue.state.load(Ordering::Acquire);
            loop {
                if state & WRITER != 0 {
                    return false;
                }
                match self.queue.state.compare_exchange_weak(
                    state,
                    add_reader(state),
                    Ordering::AcqRel,
                    Ordering::Acquire,
                ) {
                    Ok(_) => break,
                    Err(actual) => state = actual,
                }
            }
            readers.pop_front();
            if !woken.grant(node) {
                self.queue.state.fetch_sub(ONE_READER, Ordering::AcqRel);
            }
        }
        true
    }

    /// Puts back a write grant whose waiter withdrew in the meantime.
    fn undo_write_grant(&self, held: usize, last_read: usize) {
        let mut state = self.queue.state.load(Ordering::Acquire);
        loop {
            let next = ((state & !(WRITER | LAST_READ)) | last_read) + held * ONE_READER;
            match self.queue.state.compare_exchange_weak(
                state,
                next,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => return,
                Err(actual) => state = actual,
            }
        }
    }
}

impl Policy for RawRwLock {
    fn queue(&self) -> &WaitQueue {
        &self.queue
    }

    fn pass(&self, arrivals: Arrivals, woken: &mut WakeList<'_>) -> usize {
        let queue = &self.queue;
        let pool = queue.pool();
        // SAFETY: only the drain role's holder runs a pass.
        self.waiting.with_mut(|waiting| unsafe {
            let waiting = &mut *waiting;
            for node in arrivals {
                let list = match node.as_ref().payload() {
                    READ => &mut waiting.readers,
                    WRITE => &mut waiting.writers,
                    _ => &mut waiting.upgrades,
                };
                if node.as_ref().is_cancelled() {
                    release_queued(node, pool);
                } else {
                    list.push_back(node);
                }
            }
            waiting.readers.tidy(queue);
            waiting.writers.tidy(queue);
            waiting.upgrades.tidy(queue);
            loop {
                let state = queue.state.load(Ordering::Acquire);
                if state & WRITER != 0 {
                    break;
                }
                let upgrade = waiting.upgrades.front(pool);
                let writer = waiting.writers.front(pool);
                let readers_turn =
                    state & LAST_READ == 0 || (upgrade.is_none() && writer.is_none());
                if readers_turn && waiting.readers.front(pool).is_some() {
                    if !self.admit_readers(&mut waiting.readers, woken) {
                        break;
                    }
                    continue;
                }
                let (node, list, held) = match (upgrade, writer) {
                    (Some(node), _) => (node, &mut waiting.upgrades, 1),
                    (None, Some(node)) => (node, &mut waiting.writers, 0),
                    (None, None) => break,
                };
                if readers(state) != held {
                    break;
                }
                let next = ((state - held * ONE_READER) | WRITER) & !LAST_READ;
                if queue
                    .state
                    .compare_exchange(state, next, Ordering::AcqRel, Ordering::Acquire)
                    .is_err()
                {
                    continue;
                }
                list.pop_front();
                if !woken.grant(node) {
                    self.undo_write_grant(held, state & LAST_READ);
                }
            }
            let mut clear = 0;
            if waiting.readers.front(pool).is_none() {
                clear |= QUEUED_R;
            }
            if waiting.writers.front(pool).is_none() && waiting.upgrades.front(pool).is_none() {
                clear |= QUEUED_W;
            }
            clear
        })
    }
}

impl Drop for RawRwLock {
    fn drop(&mut self) {
        let pool = self.queue.pool();
        // SAFETY: `&mut self` rules out a concurrent pass.
        self.waiting.with_mut(|waiting| unsafe {
            let waiting = &mut *waiting;
            waiting.readers.clear(pool);
            waiting.writers.clear(pool);
            waiting.upgrades.clear(pool);
        });
    }
}

/// A future's wait for one side of a [`RawRwLock`].
pub(super) struct RwWait {
    wait: Wait,
}

impl RwWait {
    pub(super) const fn new() -> Self {
        Self { wait: Wait::new() }
    }

    pub(super) fn is_queued(&self) -> bool {
        self.wait.is_queued()
    }

    pub(super) fn poll(&mut self, lock: &RawRwLock, kind: usize, waker: &Waker) -> Poll<()> {
        if self.wait.is_queued() {
            return self.wait.poll(&lock.queue, Some(waker)).map(drop);
        }
        if lock.try_kind(kind) {
            return Poll::Ready(());
        }
        let flag = if kind == READ { QUEUED_R } else { QUEUED_W };
        lock.enqueue(&mut self.wait, kind, waker, flag);
        self.wait.poll(&lock.queue, None).map(drop)
    }

    /// Withdraws a pending wait, passing on a grant made meanwhile.
    pub(super) fn cancel(&mut self, lock: &RawRwLock, kind: usize) {
        match self.wait.cancel(&lock.queue) {
            Cancel::Idle => {}
            Cancel::Withdrawn => lock.withdrawn(),
            Cancel::Granted(_) => lock.unlock_kind(kind),
        }
    }
}
