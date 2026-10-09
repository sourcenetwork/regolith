//! A phase-fair asynchronous reader-writer lock its holders may lock
//! again, keyed by [`Owner`].
//!
//! The lock queues owners, not calls. An owner that already reads reads
//! again at once, even with a writer waiting, because that writer waits
//! for this owner's read anyway; an owner that writes may also read; and
//! an owner that reads and asks to write queues as an upgrade, ahead of
//! plain writers, and is granted when its own read is the last one. So an
//! owner never deadlocks on itself. Two readers that both ask to upgrade
//! still deadlock each other, as with any reader-writer lock.
//!
//! Each reading owner has a record (owner id, read depth) in a lock-free
//! list that only grows: a record is reused once its owner stops reading,
//! so the list is as long as the most owners that ever read at once.

#![allow(unsafe_code)]

use core::fmt;
use core::future::Future;
use core::ops::Deref;
use core::pin::Pin;
use core::ptr;
use core::task::{Context, Poll};

use super::internal::{AtomicPtr, AtomicU64, AtomicUsize, Ordering, UnsafeCell};
use super::owner::Owner;
use super::raw_rwlock::{READ, RawRwLock, RwWait, UPGRADE, WRITE};

/// One reading owner: its id (zero when free) and how many reads it holds.
struct Record {
    owner: AtomicU64,
    reads: AtomicUsize,
    /// Set before the record is published and never again.
    next: *mut Record,
}

struct Records {
    head: AtomicPtr<Record>,
}

impl Records {
    loom_const_fn! {
        fn new() -> Self {
            Self { head: AtomicPtr::new(ptr::null_mut()) }
        }
    }

    fn iter(&self) -> impl Iterator<Item = &Record> {
        let mut cursor = self.head.load(Ordering::Acquire);
        core::iter::from_fn(move || {
            // SAFETY: records are freed only when the list is dropped.
            let record = unsafe { cursor.as_ref() }?;
            cursor = record.next;
            Some(record)
        })
    }

    /// The record `id` holds. Only an owner stores its own id, so only
    /// that owner can find it.
    fn find(&self, id: u64) -> Option<&Record> {
        self.iter()
            .find(|record| record.owner.load(Ordering::Relaxed) == id)
    }

    /// A free record, now held by `id`.
    fn claim(&self, id: u64) -> &Record {
        if let Some(record) = self.iter().find(|record| {
            record.owner.load(Ordering::Relaxed) == 0
                && record
                    .owner
                    .compare_exchange(0, id, Ordering::Acquire, Ordering::Relaxed)
                    .is_ok()
        }) {
            return record;
        }
        let fresh = Box::into_raw(Box::new(Record {
            owner: AtomicU64::new(id),
            reads: AtomicUsize::new(0),
            next: ptr::null_mut(),
        }));
        let mut head = self.head.load(Ordering::Relaxed);
        loop {
            // SAFETY: `fresh` is unpublished, so this thread owns it.
            unsafe { (*fresh).next = head };
            match self
                .head
                .compare_exchange_weak(head, fresh, Ordering::Release, Ordering::Relaxed)
            {
                // SAFETY: published; it lives until the list is dropped.
                Ok(_) => return unsafe { &*fresh },
                Err(actual) => head = actual,
            }
        }
    }
}

impl Drop for Records {
    fn drop(&mut self) {
        let mut cursor = self.head.load(Ordering::Acquire);
        while !cursor.is_null() {
            // SAFETY: `&mut self` leaves the list unreachable to others.
            let record = unsafe { Box::from_raw(cursor) };
            cursor = record.next;
        }
    }
}

/// A phase-fair reader-writer lock its holders may lock again.
///
/// Both guards give `&T`, since one owner may hold several at once; the
/// write side excludes every other owner, so mutate through interior
/// mutability that is `Sync` (an atomic, a [`Mutex`](super::Mutex)), as
/// readers on other threads share the value. Guards and lock futures
/// borrow their [`Owner`] and stay on its thread.
///
/// ```
/// use regolith::sync::{Owner, ReentrantRwLock};
/// use std::sync::atomic::{AtomicU32, Ordering};
///
/// let lock = ReentrantRwLock::new(AtomicU32::new(0));
/// let me = Owner::new();
/// let write = lock.try_write(&me).expect("free");
/// let read = lock.try_read(&me).expect("a writer may also read");
/// write.store(7, Ordering::Relaxed);
/// drop(write);
/// assert!(lock.try_write(&Owner::new()).is_none(), "the read is still held");
/// assert_eq!(read.load(Ordering::Relaxed), 7);
/// ```
pub struct ReentrantRwLock<T: ?Sized> {
    raw: RawRwLock,
    /// The writing owner's id, or zero; only the writer stores its own id.
    writer: AtomicU64,
    /// How many write guards the writer holds; touched only by the writer.
    write_depth: UnsafeCell<usize>,
    readers: Records,
    value: core::cell::UnsafeCell<T>,
}

// SAFETY: the value moves with the lock.
unsafe impl<T: ?Sized + Send> Send for ReentrantRwLock<T> {}
// SAFETY: readers on several threads share `&T`, so `T: Sync`; the writer
// gets nothing more than `&T`.
unsafe impl<T: ?Sized + Send + Sync> Sync for ReentrantRwLock<T> {}

impl<T> ReentrantRwLock<T> {
    loom_const_fn! {
        /// An unlocked lock holding `value`.
        pub fn new(value: T) -> Self {
            Self {
                raw: RawRwLock::new(),
                writer: AtomicU64::new(0),
                write_depth: UnsafeCell::new(0),
                readers: Records::new(),
                value: core::cell::UnsafeCell::new(value),
            }
        }
    }

    /// Consumes the lock and returns its value.
    pub fn into_inner(self) -> T {
        self.value.into_inner()
    }
}

impl<T: ?Sized> ReentrantRwLock<T> {
    /// Reads if `owner` already reads or writes, or if no writer holds or
    /// waits for the lock.
    pub fn try_read<'a>(&'a self, owner: &'a Owner) -> Option<ReentrantReadGuard<'a, T>> {
        let record = match self.reenter_read(owner) {
            Some(record) => record,
            None if self.raw.try_read() => self.enter_read(owner),
            None => return None,
        };
        Some(ReentrantReadGuard::new(self, owner, record))
    }

    /// Writes if `owner` already writes; upgrades if `owner` is the only
    /// reader; or writes if nobody holds or waits for the lock.
    pub fn try_write<'a>(&'a self, owner: &'a Owner) -> Option<ReentrantWriteGuard<'a, T>> {
        if self.reenter_write(owner) {
            return Some(ReentrantWriteGuard::new(self, owner));
        }
        let taken = if self.readers.find(owner.id()).is_some() {
            self.raw.try_upgrade()
        } else {
            self.raw.try_write()
        };
        taken.then(|| {
            self.enter_write(owner);
            ReentrantWriteGuard::new(self, owner)
        })
    }

    /// Waits to read, at once if `owner` already reads or writes.
    pub fn read<'a>(&'a self, owner: &'a Owner) -> ReentrantRead<'a, T> {
        ReentrantRead {
            lock: self,
            owner,
            wait: RwWait::new(),
        }
    }

    /// Waits to write, at once if `owner` already writes. An owner that
    /// reads waits only for the other readers.
    pub fn write<'a>(&'a self, owner: &'a Owner) -> ReentrantWrite<'a, T> {
        ReentrantWrite {
            lock: self,
            owner,
            kind: WRITE,
            pin: None,
            wait: RwWait::new(),
        }
    }

    /// The value, borrowed mutably; `&mut self` proves no guard exists.
    pub fn get_mut(&mut self) -> &mut T {
        self.value.get_mut()
    }

    fn reenter_read(&self, owner: &Owner) -> Option<&Record> {
        let id = owner.id();
        if let Some(record) = self.readers.find(id) {
            record.reads.fetch_add(1, Ordering::Relaxed);
            return Some(record);
        }
        (self.writer.load(Ordering::Relaxed) == id).then(|| self.enter_read(owner))
    }

    /// Records a first read by `owner`, which holds a share or the write.
    fn enter_read(&self, owner: &Owner) -> &Record {
        let record = self.readers.claim(owner.id());
        record.reads.store(1, Ordering::Relaxed);
        record
    }

    fn read_unlock(&self, id: u64, record: &Record) {
        if record.reads.fetch_sub(1, Ordering::Relaxed) == 1 {
            record.owner.store(0, Ordering::Release);
            // While the owner writes, its reads hold no share of their own.
            if self.writer.load(Ordering::Relaxed) != id {
                self.raw.read_unlock();
            }
        }
    }

    fn reenter_write(&self, owner: &Owner) -> bool {
        if self.writer.load(Ordering::Relaxed) != owner.id() {
            return false;
        }
        // SAFETY: only the writer touches the depth, and this is it.
        self.write_depth.with_mut(|depth| unsafe {
            *depth = (*depth)
                .checked_add(1)
                .unwrap_or_else(|| panic!("a ReentrantRwLock was write-locked usize::MAX times"));
        });
        true
    }

    fn enter_write(&self, owner: &Owner) {
        // SAFETY: the write side makes this caller the only writer.
        self.write_depth.with_mut(|depth| unsafe { *depth = 1 });
        self.writer.store(owner.id(), Ordering::Relaxed);
    }

    fn write_unlock(&self, id: u64) {
        // SAFETY: only the writer drops a write guard.
        let left = self.write_depth.with_mut(|depth| unsafe {
            *depth -= 1;
            *depth
        });
        if left == 0 {
            self.writer.store(0, Ordering::Relaxed);
            if self.readers.find(id).is_some() {
                self.raw.downgrade();
            } else {
                self.raw.write_unlock();
            }
        }
    }
}

impl<T: Default> Default for ReentrantRwLock<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T: ?Sized> fmt::Debug for ReentrantRwLock<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ReentrantRwLock").finish_non_exhaustive()
    }
}

/// One read of a [`ReentrantRwLock`]; drops one level of the owner's
/// reads.
#[must_use = "dropping the guard releases one read at once"]
pub struct ReentrantReadGuard<'a, T: ?Sized> {
    lock: &'a ReentrantRwLock<T>,
    owner: &'a Owner,
    record: &'a Record,
}

impl<'a, T: ?Sized> ReentrantReadGuard<'a, T> {
    fn new(lock: &'a ReentrantRwLock<T>, owner: &'a Owner, record: &'a Record) -> Self {
        Self {
            lock,
            owner,
            record,
        }
    }
}

impl<T: ?Sized> Deref for ReentrantReadGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // SAFETY: a read excludes every other owner's write, and the
        // writer, if it is this owner, only ever has `&T` too.
        unsafe { &*self.lock.value.get() }
    }
}

impl<T: ?Sized> Drop for ReentrantReadGuard<'_, T> {
    fn drop(&mut self) {
        self.lock.read_unlock(self.owner.id(), self.record);
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for ReentrantReadGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

/// One write of a [`ReentrantRwLock`]; drops one level of the owner's
/// writes.
#[must_use = "dropping the guard releases one write at once"]
pub struct ReentrantWriteGuard<'a, T: ?Sized> {
    lock: &'a ReentrantRwLock<T>,
    owner: &'a Owner,
}

impl<'a, T: ?Sized> ReentrantWriteGuard<'a, T> {
    fn new(lock: &'a ReentrantRwLock<T>, owner: &'a Owner) -> Self {
        Self { lock, owner }
    }
}

impl<T: ?Sized> Deref for ReentrantWriteGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // SAFETY: the write excludes every other owner, and this owner's
        // guards only ever hand out `&T`.
        unsafe { &*self.lock.value.get() }
    }
}

impl<T: ?Sized> Drop for ReentrantWriteGuard<'_, T> {
    fn drop(&mut self) {
        self.lock.write_unlock(self.owner.id());
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for ReentrantWriteGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

/// The future [`ReentrantRwLock::read`] returns.
#[must_use = "futures do nothing unless polled"]
pub struct ReentrantRead<'a, T: ?Sized> {
    lock: &'a ReentrantRwLock<T>,
    owner: &'a Owner,
    wait: RwWait,
}

impl<'a, T: ?Sized> Future for ReentrantRead<'a, T> {
    type Output = ReentrantReadGuard<'a, T>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<ReentrantReadGuard<'a, T>> {
        let this = self.get_mut();
        if !this.wait.is_queued()
            && let Some(record) = this.lock.reenter_read(this.owner)
        {
            return Poll::Ready(ReentrantReadGuard::new(this.lock, this.owner, record));
        }
        this.wait.poll(&this.lock.raw, READ, cx.waker()).map(|()| {
            let record = this.lock.enter_read(this.owner);
            ReentrantReadGuard::new(this.lock, this.owner, record)
        })
    }
}

impl<T: ?Sized> Drop for ReentrantRead<'_, T> {
    fn drop(&mut self) {
        self.wait.cancel(&self.lock.raw, READ);
    }
}

impl<T: ?Sized> fmt::Debug for ReentrantRead<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ReentrantRead")
            .field("owner", self.owner)
            .finish_non_exhaustive()
    }
}

/// The future [`ReentrantRwLock::write`] returns.
#[must_use = "futures do nothing unless polled"]
pub struct ReentrantWrite<'a, T: ?Sized> {
    lock: &'a ReentrantRwLock<T>,
    owner: &'a Owner,
    kind: usize,
    /// While an upgrade waits it holds one more of the owner's reads, so
    /// the read it converts cannot be released underneath it.
    pin: Option<&'a Record>,
    wait: RwWait,
}

impl<'a, T: ?Sized> Future for ReentrantWrite<'a, T> {
    type Output = ReentrantWriteGuard<'a, T>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<ReentrantWriteGuard<'a, T>> {
        let this = self.get_mut();
        if !this.wait.is_queued() {
            if this.lock.reenter_write(this.owner) {
                return Poll::Ready(ReentrantWriteGuard::new(this.lock, this.owner));
            }
            if this.pin.is_none()
                && let Some(record) = this.lock.readers.find(this.owner.id())
            {
                record.reads.fetch_add(1, Ordering::Relaxed);
                this.pin = Some(record);
            }
            this.kind = if this.pin.is_some() { UPGRADE } else { WRITE };
        }
        this.wait
            .poll(&this.lock.raw, this.kind, cx.waker())
            .map(|()| {
                this.lock.enter_write(this.owner);
                if let Some(record) = this.pin.take() {
                    this.lock.read_unlock(this.owner.id(), record);
                }
                ReentrantWriteGuard::new(this.lock, this.owner)
            })
    }
}

impl<T: ?Sized> Drop for ReentrantWrite<'_, T> {
    fn drop(&mut self) {
        self.wait.cancel(&self.lock.raw, self.kind);
        if let Some(record) = self.pin.take() {
            self.lock.read_unlock(self.owner.id(), record);
        }
    }
}

impl<T: ?Sized> fmt::Debug for ReentrantWrite<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ReentrantWrite")
            .field("owner", self.owner)
            .finish_non_exhaustive()
    }
}

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;
    use crate::sync::test_support::Polled;

    #[test]
    fn a_reader_reads_again_past_a_waiting_writer() {
        let lock = ReentrantRwLock::new(());
        let (me, writer) = (Owner::new(), Owner::new());
        let first = lock.try_read(&me).expect("free");
        let mut write = Polled::new(lock.write(&writer));
        write.pending();
        assert!(
            lock.try_read(&Owner::new()).is_none(),
            "a new owner waits for the writer"
        );
        let second = Polled::new(lock.read(&me)).ready();
        drop(first);
        assert_eq!(write.wakes(), 0, "the owner still reads");
        drop(second);
        assert_eq!(write.wakes(), 1);
        drop(write.ready());
        assert!(lock.try_write(&Owner::new()).is_some());
    }

    #[test]
    fn a_writer_reads_and_keeps_its_read_after_the_write() {
        let lock = ReentrantRwLock::new(());
        let (me, other) = (Owner::new(), Owner::new());
        let write = lock.try_write(&me).expect("free");
        let nested = lock.try_write(&me).expect("the writer re-enters");
        let read = lock.try_read(&me).expect("a writer may also read");
        drop((nested, write));
        assert!(
            lock.try_write(&other).is_none(),
            "the read survives the write"
        );
        let shared = lock.try_read(&other).expect("the write became a read");
        drop((read, shared));
        assert!(lock.try_write(&other).is_some());
    }

    #[test]
    fn the_only_reader_upgrades_at_once() {
        let lock = ReentrantRwLock::new(());
        let me = Owner::new();
        let read = lock.try_read(&me).expect("free");
        let write = Polled::new(lock.write(&me)).ready();
        assert!(lock.try_read(&Owner::new()).is_none());
        drop(write);
        assert!(
            lock.try_write(&Owner::new()).is_none(),
            "the read is still held"
        );
        drop(read);
        assert!(lock.try_write(&Owner::new()).is_some());
    }

    #[test]
    fn an_upgrade_waits_for_the_other_readers_ahead_of_plain_writers() {
        let lock = ReentrantRwLock::new(());
        let (me, them, writer) = (Owner::new(), Owner::new(), Owner::new());
        let mine = lock.try_read(&me).expect("free");
        let theirs = lock.try_read(&them).expect("readers share");
        let mut write = Polled::new(lock.write(&writer));
        write.pending();
        let mut upgrade = Polled::new(lock.write(&me));
        upgrade.pending();
        drop(theirs);
        assert_eq!((upgrade.wakes(), write.wakes()), (1, 0));
        let upgraded = upgrade.ready();
        drop(upgraded);
        assert_eq!(write.wakes(), 0, "the upgrader still reads");
        drop(mine);
        assert_eq!(write.wakes(), 1);
        drop(write.ready());
    }

    #[test]
    fn a_withdrawn_upgrade_keeps_the_read_it_came_with() {
        let lock = ReentrantRwLock::new(());
        let (me, them) = (Owner::new(), Owner::new());
        let mine = lock.try_read(&me).expect("free");
        let theirs = lock.try_read(&them).expect("readers share");
        Polled::new(lock.write(&me)).pending();
        drop(theirs);
        assert!(lock.try_write(&them).is_none(), "the owner still reads");
        drop(mine);
        assert!(lock.try_write(&them).is_some());
    }

    #[test]
    fn a_granted_upgrade_dropped_unseen_turns_back_into_a_read() {
        let lock = ReentrantRwLock::new(());
        let (me, them) = (Owner::new(), Owner::new());
        let mine = lock.try_read(&me).expect("free");
        let theirs = lock.try_read(&them).expect("readers share");
        let mut upgrade = Polled::new(lock.write(&me));
        upgrade.pending();
        drop(theirs);
        assert_eq!(upgrade.wakes(), 1);
        drop(upgrade);
        assert!(lock.try_read(&them).is_some(), "back to a read phase");
        drop(mine);
        assert!(lock.try_write(&them).is_some());
    }
}
