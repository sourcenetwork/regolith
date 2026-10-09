//! The core of [`RwLock`](super::RwLock), which
//! [`ReentrantRwLock`](super::ReentrantRwLock) builds on.
//!
//! The state word holds the reader count, a writer bit, an upgradable bit
//! and an upgrading bit above the queue's bits.
//!
//! - **Barging with bounded bypass, both ways.** A read enters whenever no
//!   writer holds the lock and no upgrade is under way; a write whenever
//!   the lock is free; either even past queued waiters, unless a handoff is
//!   owed (see `contend`). A release nudges the waiter at the front: a
//!   writer there is nudged on every release, so readers that keep
//!   overlapping still make it lose and count bypasses until it is owed a
//!   handoff, which holds every new reader back until the readers inside
//!   have left. Readers at the front are nudged together, with an
//!   upgradable read among them.
//! - **One upgradable read at a time.** It shares the lock with plain
//!   readers and excludes writers and other upgradable reads. Its upgrade
//!   sets the upgrading bit, which holds new readers back, and becomes the
//!   write once the readers inside have left. Since only one upgrader can
//!   exist, an upgrade never deadlocks on another.

#![allow(unsafe_code)]

use core::ptr::NonNull;
use core::task::{Poll, Waker};

use super::contend::{Contend, Lock};
use super::internal::{Ordering, UnsafeCell};
use super::list::List;
use super::queue::{
    Arrivals, FIRST_BIT, HANDOFF, Nudges, Policy, QUEUED, Step, WAKE_FRONT, WaitQueue, wants_drain,
};
use super::waiter::{Cancel, Park, Wait, Waiter, WakeList, release_queued};

const WRITER: usize = 1 << FIRST_BIT;
const UPGRADABLE: usize = 1 << (FIRST_BIT + 1);
/// The upgradable read is waiting to become the write.
const UPGRADING: usize = 1 << (FIRST_BIT + 2);
const READER_SHIFT: u32 = FIRST_BIT + 3;
const ONE_READER: usize = 1 << READER_SHIFT;
const MAX_READERS: usize = usize::MAX >> READER_SHIFT;

/// What a waiter asks for.
pub(super) const READ: usize = 0;
pub(super) const WRITE: usize = 1;
pub(super) const UPGRADABLE_READ: usize = 2;
/// The upgradable read's wait to become the write.
const UPGRADE: usize = 3;

fn readers(state: usize) -> usize {
    state >> READER_SHIFT
}

/// Whether `kind` could enter a lock in `state`, the owed bit aside.
fn admits(kind: usize, state: usize) -> bool {
    match kind {
        READ => state & (WRITER | UPGRADING) == 0,
        WRITE => state & (WRITER | UPGRADABLE) == 0 && readers(state) == 0,
        _ => state & (WRITER | UPGRADABLE) == 0,
    }
}

/// `state` with `kind` entered.
fn enter(kind: usize, state: usize) -> usize {
    match kind {
        READ => {
            assert!(
                readers(state) < MAX_READERS,
                "too many readers hold one RwLock"
            );
            state + ONE_READER
        }
        WRITE => state | WRITER,
        _ => state | UPGRADABLE,
    }
}

struct Waiting {
    list: List,
    /// The upgradable read's node while its upgrade waits.
    upgrade: Option<NonNull<Waiter>>,
}

/// The reader-writer core with no value attached.
pub(super) struct RawRwLock {
    queue: WaitQueue,
    waiting: UnsafeCell<Waiting>,
}

// SAFETY: the waiting list is touched only by the drain role's holder.
unsafe impl Send for RawRwLock {}
// SAFETY: as above.
unsafe impl Sync for RawRwLock {}

impl RawRwLock {
    loom_const_fn! {
        pub(super) fn new() -> Self {
            Self {
                queue: WaitQueue::new(0),
                waiting: UnsafeCell::new(Waiting { list: List::new(), upgrade: None }),
            }
        }
    }

    pub(super) fn try_kind(&self, kind: usize) -> bool {
        self.try_take(kind).is_ok()
    }

    /// Drops one read. One `fetch_sub` when no waiter needs telling.
    pub(super) fn read_unlock(&self) {
        let before = self.queue.state.fetch_sub(ONE_READER, Ordering::AcqRel);
        let upgrade_ready = readers(before) == 1 && before & UPGRADING != 0;
        if wants_drain(before) || upgrade_ready {
            self.released();
        }
    }

    /// Drops the write. One `fetch_and` when no waiter needs telling.
    pub(super) fn write_unlock(&self) {
        let before = self.queue.state.fetch_and(!WRITER, Ordering::AcqRel);
        if wants_drain(before) {
            self.released();
        }
    }

    /// Drops the upgradable read, and an upgrade it had begun.
    pub(super) fn upgradable_unlock(&self) {
        let before = self
            .queue
            .state
            .fetch_and(!(UPGRADABLE | UPGRADING), Ordering::AcqRel);
        if wants_drain(before) || before & UPGRADING != 0 {
            self.released();
        }
    }

    /// Turns the held write into a read.
    pub(super) fn downgrade(&self) {
        self.transition(|state| {
            let next = (state & !WRITER) + ONE_READER;
            if state & QUEUED != 0 {
                Step::Drain(next | WAKE_FRONT)
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
            _ => self.upgradable_unlock(),
        }
    }

    /// Turns the held upgradable read into the write if no reader is
    /// inside.
    pub(super) fn try_upgrade(&self) -> bool {
        let mut state = self.queue.state.load(Ordering::Relaxed);
        loop {
            if readers(state) != 0 {
                return false;
            }
            match self.queue.state.compare_exchange_weak(
                state,
                (state & !(UPGRADABLE | UPGRADING)) | WRITER,
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => return true,
                Err(actual) => state = actual,
            }
        }
    }

    /// Hands the write to the waiting upgrade once the readers have left.
    /// False when it is still waiting.
    fn grant_upgrade(&self, node: NonNull<Waiter>, woken: &mut WakeList<'_>) -> bool {
        let mut state = self.queue.state.load(Ordering::Acquire);
        loop {
            // The upgrading bit is gone when the upgrade was dropped: the
            // drop releases the upgradable read itself.
            if state & UPGRADING == 0 {
                release_queued(node, &self.queue);
                return true;
            }
            if readers(state) != 0 {
                return false;
            }
            match self.queue.state.compare_exchange_weak(
                state,
                (state & !(UPGRADABLE | UPGRADING)) | WRITER,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => break,
                Err(actual) => state = actual,
            }
        }
        if !woken.grant(node) {
            // Dropped after the write was taken for it: the drop found
            // nothing left to release, so release it here.
            self.queue.state.fetch_and(!WRITER, Ordering::AcqRel);
        }
        true
    }
}

impl Lock for RawRwLock {
    fn admit(&self, state: usize, kind: usize) -> Option<usize> {
        admits(kind, state).then(|| enter(kind, state))
    }

    fn give_back(&self, kind: usize) {
        self.unlock_kind(kind);
    }
}

impl Policy for RawRwLock {
    fn queue(&self) -> &WaitQueue {
        &self.queue
    }

    fn pass(&self, arrivals: Arrivals, woken: &mut WakeList<'_>, wake_front: bool) -> usize {
        let queue = &self.queue;
        // SAFETY: only the drain role's holder runs a pass.
        self.waiting.with_mut(|waiting| unsafe {
            let waiting = &mut *waiting;
            for node in arrivals {
                if node.as_ref().is_cancelled() {
                    release_queued(node, queue);
                } else if node.as_ref().payload() == UPGRADE {
                    debug_assert!(waiting.upgrade.is_none(), "two upgrades at once");
                    waiting.upgrade = Some(node);
                } else {
                    waiting.list.push_back(node);
                }
            }
            waiting.list.tidy(queue);
            if let Some(node) = waiting.upgrade
                && self.grant_upgrade(node, woken)
            {
                waiting.upgrade = None;
            }
            let list = &mut waiting.list;
            if queue.state.load(Ordering::Acquire) & HANDOFF != 0 {
                while let Some(node) = list.front(queue) {
                    let kind = node.as_ref().payload();
                    if !self.take_for_waiter(kind) {
                        break;
                    }
                    list.pop_front();
                    if !woken.grant(node) {
                        self.undo(kind);
                    } else if kind == WRITE {
                        break;
                    }
                }
            }
            // While nobody is owed, the queue competes: wake the front if it
            // could enter, or after any release even if it cannot yet, so a
            // writer that overlapping readers keep out still loses, counts
            // the bypass, and is owed a handoff in the end. Readers and an
            // upgradable read behind a sharing front are woken with it
            // while they could share.
            if !queue.hands_off()
                && let Some(front) = list.front(queue)
            {
                let mut sharing = queue.state.load(Ordering::Acquire);
                let mut nudges = Nudges::new(woken, queue);
                for (at, node) in list.iter().enumerate() {
                    let kind = node.as_ref().payload();
                    let fits = admits(kind, sharing);
                    if at == 0 && (fits || wake_front) {
                        nudges.nudge(node);
                    }
                    if !fits || kind == WRITE || (at > 0 && front.as_ref().payload() == WRITE) {
                        break;
                    }
                    if at > 0 {
                        nudges.nudge(node);
                    }
                    sharing = enter(kind, sharing);
                }
                nudges.finish();
            }
            if list.front(queue).is_none() && waiting.upgrade.is_none() {
                QUEUED
            } else {
                0
            }
        })
    }
}

impl RawRwLock {
    /// Puts back a grant whose waiter withdrew in the meantime. The drain
    /// pass that called this goes on to reconsider the queue.
    fn undo(&self, kind: usize) {
        let gone = match kind {
            READ => ONE_READER,
            WRITE => WRITER,
            _ => UPGRADABLE,
        };
        if kind == READ {
            self.queue.state.fetch_sub(gone, Ordering::AcqRel);
        } else {
            self.queue.state.fetch_and(!gone, Ordering::AcqRel);
        }
    }
}

impl Drop for RawRwLock {
    fn drop(&mut self) {
        let queue = &self.queue;
        // SAFETY: `&mut self` rules out a concurrent pass.
        self.waiting.with_mut(|waiting| unsafe {
            let waiting = &mut *waiting;
            waiting.list.clear(queue);
            if let Some(node) = waiting.upgrade.take() {
                release_queued(node, queue);
            }
        });
    }
}

/// A future's wait for one side of a [`RawRwLock`].
pub(super) struct RwWait {
    contend: Contend,
}

impl RwWait {
    pub(super) const fn new() -> Self {
        Self {
            contend: Contend::new(),
        }
    }

    pub(super) fn is_queued(&self) -> bool {
        self.contend.is_queued()
    }

    pub(super) fn poll(&mut self, lock: &RawRwLock, kind: usize, waker: &Waker) -> Poll<()> {
        self.contend.poll(lock, kind, waker)
    }

    /// Withdraws a pending wait, passing on a grant made meanwhile.
    pub(super) fn cancel(&mut self, lock: &RawRwLock, kind: usize) {
        self.contend.cancel(lock, kind);
    }
}

/// The upgradable read's wait to become the write.
pub(super) struct UpgradeWait {
    wait: Wait,
    started: bool,
}

impl UpgradeWait {
    pub(super) const fn new() -> Self {
        Self {
            wait: Wait::new(),
            started: false,
        }
    }

    /// Ready once the caller, which holds the upgradable read, holds the
    /// write instead.
    pub(super) fn poll(&mut self, lock: &RawRwLock, waker: &Waker) -> Poll<()> {
        if self.wait.is_queued() {
            return match self.wait.park(&lock.queue, Some(waker)) {
                Park::Granted(_) => Poll::Ready(()),
                Park::Nudged | Park::Pending => Poll::Pending,
            };
        }
        if !self.started {
            self.started = true;
            lock.queue.state.fetch_or(UPGRADING, Ordering::AcqRel);
        }
        if lock.try_upgrade() {
            return Poll::Ready(());
        }
        lock.enqueue(&mut self.wait, UPGRADE, waker);
        match self.wait.park(&lock.queue, None) {
            Park::Granted(_) => Poll::Ready(()),
            Park::Nudged | Park::Pending => Poll::Pending,
        }
    }

    /// Gives up an upgrade that has not completed, with the upgradable
    /// read the caller held; a write granted meanwhile is released.
    pub(super) fn cancel(&mut self, lock: &RawRwLock) {
        match self.wait.cancel(&lock.queue) {
            Cancel::Granted(_) => lock.write_unlock(),
            Cancel::Withdrawn(_) => {
                lock.upgradable_unlock();
                lock.withdrawn(false);
            }
            Cancel::Idle => lock.upgradable_unlock(),
        }
    }
}
