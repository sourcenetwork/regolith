//! The pessimistic lock table: one exclusive lock per key, held by a
//! transaction from the call that takes it until the transaction ends or its
//! commit lands (plan 4.6, 4.10, 4.11).
//!
//! A key's lock is an [`OwnedLock`] in a lock-free map. Taking it is one
//! compare-and-swap that writes the transaction's [`LockOwner`] name into the
//! lock's state word; releasing it is one more. A transaction that finds the
//! lock taken either returns at once with a [`LockWait`](crate::LockWait)
//! (`try_get_for_update`) or waits for it (`get_for_update`, `put`, `delete`,
//! `merge`), and both wait the same way: in the lock's queue, with barging and
//! bounded bypass (D49), so a free lock goes to whoever asks first and a
//! waiter passed over [`MAX_BYPASS`](crate::sync::MAX_BYPASS) times is handed
//! it.
//!
//! # Invariants
//!
//! - **One holder per key.** The holder's name is in the lock's state word,
//!   written by the compare-and-swap that takes the lock, so two owners
//!   cannot both hold it, and one owner's second call on any thread reads its
//!   own name back. A key has at most one lock in the table: an entry leaves
//!   only once its use count is retired from zero, by one compare-and-swap
//!   inside the map's removal of exactly that entry, and a use is taken by a
//!   compare-and-swap that refuses a retired count. So nobody can hold or wait
//!   on an entry that left the table while another one stands for its key.
//! - **What bounds the table.** An entry is in the table only while it is
//!   used: by its holder, by each waiting transaction, and by each call
//!   between its lookup and its outcome. The last use out removes it. So the
//!   table holds the keys locked or waited on now, never every key ever
//!   locked.
//! - **A wait completes on the waiter's own queue.** A waiting transaction's
//!   lock waker delivers each [`LockWait`](crate::LockWait) it handed out to
//!   the queue that wait names, as one completion its `poll` takes in; it
//!   wakes an idle owner once and a busy one never (`QueueShared::deliver`).
//!   A blocking wait parks the waiting thread, and the waker unparks it.
//! - **No waiter outlives close.** A call that may queue a waiter counts
//!   itself in through a [`CloseGate`] before and out after; close marks the
//!   gate, releases the locks of the transactions it aborted, and wakes every
//!   waiter in the table. A call under way when the mark lands abandons its
//!   own wait. Every wait therefore becomes ready, and the call run again
//!   finds the gate closed and fails with `Closed`.

#![allow(unsafe_code)]

use std::sync::Arc;
use std::task::{Wake, Waker};
use std::thread::Thread;

use kovan_map::HashMap;

use crate::engine::io::CloseGate;
use crate::engine::io::job::Delivery;
use crate::engine::io::shared::{Message, QueueShared, WaitSlot};
use crate::engine::io::stack::Stack;
use crate::sync::internal::{AtomicUsize, Ordering, UnsafeCell};
use crate::sync::{OwnedLock, OwnedWait, OwnerId};

/// Buckets the table starts with; it grows past this on demand.
const KEY_BUCKETS: usize = 64;

/// The use count of an entry taken out of the table.
const RETIRED: usize = usize::MAX;

/// The table of key locks one [`TransactionDb`](super::TransactionDb) keeps.
pub(crate) struct LockTable {
    keys: HashMap<Vec<u8>, Arc<KeyLock>>,
    /// Where close and the calls that may queue a waiter meet.
    gate: CloseGate,
}

/// One key's lock and the count of what uses it.
pub(crate) struct KeyLock {
    pub(super) lock: OwnedLock,
    /// The holder, each waiting transaction and each call between lookup and
    /// outcome, one each; [`RETIRED`] once the entry left the table.
    uses: AtomicUsize,
}

impl KeyLock {
    /// A lock used once already, by the call that makes it.
    fn new() -> Self {
        Self {
            lock: OwnedLock::new(),
            uses: AtomicUsize::new(1),
        }
    }

    /// Take a use, unless the entry left the table.
    fn pin(&self) -> bool {
        let mut uses = self.uses.load(Ordering::Acquire);
        loop {
            if uses == RETIRED {
                return false;
            }
            match self.uses.compare_exchange_weak(
                uses,
                uses + 1,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => return true,
                Err(actual) => uses = actual,
            }
        }
    }

    /// Mark an unused entry as leaving the table. `false` when a use came in
    /// first.
    fn retire(&self) -> bool {
        self.uses
            .compare_exchange(0, RETIRED, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
    }
}

impl LockTable {
    pub(crate) fn new() -> Self {
        Self {
            keys: HashMap::with_capacity(KEY_BUCKETS),
            gate: CloseGate::new(),
        }
    }

    /// `key`'s lock with a use taken for the caller, made when the key has
    /// none. Every pin is matched by one [`unpin`](Self::unpin).
    pub(super) fn pin(&self, key: &[u8]) -> Arc<KeyLock> {
        loop {
            let found = match self.keys.get(key) {
                Some(lock) => lock,
                None => {
                    let fresh = Arc::new(KeyLock::new());
                    match self.keys.insert_if_absent(key.to_vec(), Arc::clone(&fresh)) {
                        None => return fresh,
                        Some(lock) => lock,
                    }
                }
            };
            if found.pin() {
                return found;
            }
            // Retired: the thread that retired it is taking it out of the
            // table right now, in the same removal; look again once it is out.
            core::hint::spin_loop();
        }
    }

    /// Give back a use of `key`'s `lock`; the last one out takes the entry
    /// out of the table.
    pub(super) fn unpin(&self, key: &[u8], lock: &Arc<KeyLock>) {
        if lock.uses.fetch_sub(1, Ordering::AcqRel) == 1 {
            self.keys
                .remove_if(key, |held| Arc::ptr_eq(held, lock) && held.retire());
        }
    }

    /// Count a call that may queue a waiter in. `false` once close began:
    /// the call then queues nothing and fails with `Closed`.
    pub(super) fn enter(&self) -> bool {
        self.gate.enter()
    }

    /// Count the call out. `true` when close began while it was under way:
    /// close's sweep may have missed its waiter, so the call abandons it.
    pub(super) fn leave(&self) -> bool {
        self.gate.leave()
    }

    /// `close`: refuse new waiters, release the locks `aborted` (the
    /// transactions close aborted) hold, and wake every waiter, so each runs
    /// its call again and fails with `Closed`.
    pub(crate) fn close(&self, aborted: &[Arc<LockOwner>]) {
        self.gate.close();
        let names: std::collections::HashMap<usize, OwnerId> = aborted
            .iter()
            .map(|owner| (owner.id().word(), owner.id()))
            .collect();
        for lock in self.keys.values() {
            if let Some(&owner) = names.get(&lock.lock.holder()) {
                lock.lock.unlock(owner);
            }
            lock.lock.wake_all();
        }
    }

    /// A close that failed and left the database open: waiters queue again.
    pub(crate) fn reopen(&self) {
        self.gate.reopen();
    }

    /// Entries in the table now.
    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.keys.len()
    }
}

/// A pessimistic transaction's name in the key locks it holds or waits for.
///
/// Its address is the name, so it is aligned past the lock's queue bits and
/// has a size of its own. Held through an `Arc` by the transaction, by the
/// commit whose locks wait for their group to land, and by the transaction's
/// close claim, so the name stays unique while any lock can carry it.
#[repr(align(64))]
pub(crate) struct LockOwner {
    /// Gives the owner a size, so no two owners share an address.
    _place: u8,
}

impl LockOwner {
    pub(super) fn new() -> Arc<Self> {
        Arc::new(Self { _place: 0 })
    }

    /// The name this owner's locks carry.
    pub(crate) fn id(&self) -> OwnerId {
        OwnerId::of(self)
    }
}

/// A [`PendingLock`] no call is polling.
const IDLE: usize = 0;
/// A call is polling the wait; another call of the transaction waits for the
/// lock's next wake instead.
const POLLING: usize = 1;
/// The wait is over: the lock was taken, found held by the transaction, or
/// the wait was abandoned.
const DONE: usize = 2;

/// What one poll of a [`PendingLock`] found.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Polled {
    /// The transaction now holds the lock, and the wait's use is the
    /// holder's.
    Acquired,
    /// Another call of the transaction holds the lock; the wait left the
    /// queue and its use is the caller's to give back.
    Mine,
    /// Still waiting.
    Pending,
    /// Another call of the transaction is polling the wait right now.
    Busy,
    /// The wait was over before this poll.
    Done,
}

/// One transaction's wait for one key's lock, shared by every call of the
/// transaction that wants the key, and kept across calls so its place in
/// the queue and the losses it counted stay the transaction's.
pub(super) struct PendingLock {
    /// The key's lock, with a use taken for this wait.
    key_lock: Arc<KeyLock>,
    /// The place in the lock's queue. Touched only by the call that moved
    /// `state` from `IDLE`.
    wait: UnsafeCell<OwnedWait>,
    state: AtomicUsize,
    wakeup: Arc<Wakeup>,
    waker: Waker,
}

// SAFETY: `wait` is touched only by the one call that moved `state` from
// `IDLE` (to `POLLING`, or to `DONE` when it abandons the wait), so no two
// threads ever reach it at once; everything else is atomic or `Sync`.
unsafe impl Send for PendingLock {}
// SAFETY: as above.
unsafe impl Sync for PendingLock {}

impl PendingLock {
    /// A wait on `key_lock`, which the caller pinned for it.
    pub(super) fn new(key_lock: Arc<KeyLock>) -> Self {
        let wakeup = Arc::new(Wakeup {
            notes: Stack::new(),
            sleepers: Stack::new(),
        });
        Self {
            key_lock,
            wait: UnsafeCell::new(OwnedWait::new()),
            state: AtomicUsize::new(IDLE),
            waker: Waker::from(Arc::clone(&wakeup)),
            wakeup,
        }
    }

    pub(super) fn key_lock(&self) -> &Arc<KeyLock> {
        &self.key_lock
    }

    pub(super) fn is_done(&self) -> bool {
        self.state.load(Ordering::Acquire) == DONE
    }

    /// Complete `slot` on `queue` (directly with none) at the lock's next
    /// wake. Recorded before the poll it is for, so no wake falls between.
    pub(super) fn note(&self, slot: Arc<WaitSlot>, queue: Option<Arc<QueueShared>>) {
        if let Err(note) = self.wakeup.notes.push(Note { slot, queue }, 0) {
            note.deliver();
        }
    }

    /// Unpark this thread at the lock's next wake. Recorded before the poll
    /// it is for, so no wake falls between.
    pub(super) fn sleep_here(&self) {
        let _ = self.wakeup.sleepers.push(std::thread::current(), 0);
    }

    /// Poll the wait once for `owner`. `told` is the completion the calling
    /// call recorded for itself with [`note`](Self::note), if it did: a poll
    /// that ends the wait voids it, since that call does not wait after all.
    pub(super) fn poll(&self, owner: OwnerId, told: Option<&WaitSlot>) -> Polled {
        match self
            .state
            .compare_exchange(IDLE, POLLING, Ordering::AcqRel, Ordering::Acquire)
        {
            Ok(_) => {}
            Err(DONE) => {
                if let Some(told) = told {
                    told.complete();
                }
                return Polled::Done;
            }
            // Another call of the transaction is polling: this one's
            // completion stays recorded, for the lock's next wake.
            Err(_) => return Polled::Busy,
        }
        let lock = &self.key_lock.lock;
        // SAFETY: `POLLING` gives this call the wait (see the `Sync` impl).
        let ready = self
            .wait
            .with_mut(|wait| unsafe { (*wait).poll(lock, owner, &self.waker) });
        let polled = if ready.is_ready() {
            Polled::Acquired
        } else if lock.holder() == owner.word() {
            // Another call of the transaction took it while this one waited;
            // the lock cannot be handed to this wait while its own owner
            // holds it, so the cancel only withdraws.
            // SAFETY: as above.
            self.wait
                .with_mut(|wait| unsafe { (*wait).cancel(lock, owner) });
            Polled::Mine
        } else {
            Polled::Pending
        };
        if polled == Polled::Pending {
            self.state.store(IDLE, Ordering::Release);
        } else {
            if let Some(told) = told {
                told.complete();
            }
            self.finish();
        }
        polled
    }

    /// End the wait if no call is polling it: leave the queue, giving back a
    /// handoff that reached it. `true` when this call ended it, and the
    /// wait's use is the caller's to give back.
    pub(super) fn abandon(&self, owner: OwnerId) -> bool {
        if self
            .state
            .compare_exchange(IDLE, DONE, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            return false;
        }
        // SAFETY: moving `state` from `IDLE` gave this call the wait.
        self.wait
            .with_mut(|wait| unsafe { (*wait).cancel(&self.key_lock.lock, owner) });
        self.wakeup.wake_all();
        true
    }

    /// The wait is over: every other call of the transaction waiting on it
    /// runs again.
    fn finish(&self) {
        self.state.store(DONE, Ordering::Release);
        self.wakeup.wake_all();
    }
}

/// What a wake of a [`PendingLock`] tells: every [`LockWait`](crate::LockWait)
/// handed out since the last wake, each on its own queue, and every thread
/// that blocks on the wait.
struct Wakeup {
    notes: Stack<Note>,
    sleepers: Stack<Thread>,
}

impl Wakeup {
    fn wake_all(&self) {
        for note in self.notes.take(0) {
            note.deliver();
        }
        for sleeper in self.sleepers.take(0) {
            sleeper.unpark();
        }
    }
}

impl Wake for Wakeup {
    fn wake(self: Arc<Self>) {
        self.wake_all();
    }

    fn wake_by_ref(self: &Arc<Self>) {
        self.wake_all();
    }
}

/// One handed-out wait to complete: on its queue, at that queue's poll, or
/// directly when it has none or the queue was dropped.
struct Note {
    slot: Arc<WaitSlot>,
    queue: Option<Arc<QueueShared>>,
}

impl Note {
    fn deliver(self) {
        let Self { slot, queue } = self;
        // Voided by the call it was for, which did not wait after all.
        if slot.is_ready() {
            return;
        }
        let Some(queue) = queue else {
            slot.complete();
            return;
        };
        let own = Arc::clone(&slot);
        if queue
            .deliver(Message::Deliver(slot as Arc<dyn Delivery>))
            .is_err()
        {
            own.complete();
        }
    }
}

/// The key locks a pessimistic commit holds until its outcome is delivered:
/// released then, so no transaction that takes one of them can read past a
/// commit that is written but not yet visible.
pub(super) struct LandingLocks {
    table: Arc<LockTable>,
    owner: Arc<LockOwner>,
    keys: Vec<(Vec<u8>, Arc<KeyLock>)>,
    released: AtomicUsize,
}

impl LandingLocks {
    pub(super) fn new(
        table: Arc<LockTable>,
        owner: Arc<LockOwner>,
        keys: Vec<(Vec<u8>, Arc<KeyLock>)>,
    ) -> Self {
        Self {
            table,
            owner,
            keys,
            released: AtomicUsize::new(0),
        }
    }

    /// Release every lock, once whoever calls it.
    pub(super) fn release(&self) {
        if self.released.swap(1, Ordering::AcqRel) != 0 {
            return;
        }
        let owner = self.owner.id();
        for (key, key_lock) in &self.keys {
            key_lock.lock.unlock(owner);
            self.table.unpin(key, key_lock);
        }
    }
}

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;
    use crate::sync::TryLock;

    #[test]
    fn an_entry_leaves_the_table_with_its_last_use() {
        let table = LockTable::new();
        let owner = LockOwner::new();
        let lock = table.pin(b"k");
        assert_eq!(lock.lock.try_lock(owner.id()), TryLock::Taken);
        let again = table.pin(b"k");
        assert!(Arc::ptr_eq(&lock, &again), "one lock per key");
        assert_eq!(table.len(), 1);
        table.unpin(b"k", &again);
        assert_eq!(table.len(), 1, "still held");
        assert!(lock.lock.unlock(owner.id()));
        table.unpin(b"k", &lock);
        assert_eq!(table.len(), 0, "the last use took it out");
        let fresh = table.pin(b"k");
        assert!(!Arc::ptr_eq(&lock, &fresh), "a new entry for the key");
        table.unpin(b"k", &fresh);
        assert_eq!(table.len(), 0);
    }

    #[test]
    fn a_retired_entry_refuses_a_use() {
        let lock = KeyLock::new();
        assert_eq!(lock.uses.fetch_sub(1, Ordering::AcqRel), 1);
        assert!(lock.retire());
        assert!(!lock.pin(), "a retired entry is never used again");
        let busy = KeyLock::new();
        assert!(!busy.retire(), "a used entry is not retired");
    }

    #[test]
    fn pins_and_unpins_across_threads_leave_the_table_empty() {
        let table = Arc::new(LockTable::new());
        let threads: Vec<_> = (0..4)
            .map(|_| {
                let table = Arc::clone(&table);
                std::thread::spawn(move || {
                    for i in 0..if cfg!(miri) { 30u32 } else { 2_000 } {
                        let key = (i % 3).to_le_bytes();
                        let lock = table.pin(&key);
                        table.unpin(&key, &lock);
                    }
                })
            })
            .collect();
        for thread in threads {
            thread.join().expect("worker");
        }
        assert_eq!(table.len(), 0);
    }

    #[test]
    fn close_releases_the_aborted_owners_locks_and_only_theirs() {
        let table = LockTable::new();
        let (aborted, kept) = (LockOwner::new(), LockOwner::new());
        let a = table.pin(b"a");
        let b = table.pin(b"b");
        assert_eq!(a.lock.try_lock(aborted.id()), TryLock::Taken);
        assert_eq!(b.lock.try_lock(kept.id()), TryLock::Taken);
        table.close(std::slice::from_ref(&aborted));
        assert_eq!(a.lock.holder(), 0, "the aborted owner's lock is free");
        assert_eq!(b.lock.holder(), kept.id().word(), "the other stays held");
        assert!(!table.enter(), "no waiter queues after close");
        table.reopen();
        assert!(table.enter());
        assert!(!table.leave());
        table.unpin(b"a", &a);
        assert!(b.lock.unlock(kept.id()));
        table.unpin(b"b", &b);
        assert_eq!(table.len(), 0);
    }

    #[test]
    fn a_note_completes_on_its_queue_and_a_dropped_queue_completes_it_directly() {
        use crate::engine::io::shared::test_id;
        let queue = Arc::new(QueueShared::new(test_id(), 1 << 20));
        let slot = Arc::new(WaitSlot::new());
        Note {
            slot: Arc::clone(&slot),
            queue: Some(Arc::clone(&queue)),
        }
        .deliver();
        assert!(!slot.is_ready(), "ready only at the queue's poll");
        for message in queue.take_inbox() {
            match message {
                Message::Deliver(waiter) => waiter.deliver(),
                _ => panic!("a lock wait is delivered, nothing else"),
            }
        }
        assert!(slot.is_ready());
        assert_eq!(queue.shut_inbox().count(), 0);
        let late = Arc::new(WaitSlot::new());
        Note {
            slot: Arc::clone(&late),
            queue: Some(queue),
        }
        .deliver();
        assert!(late.is_ready(), "a dropped queue's wait completes directly");
    }
}
