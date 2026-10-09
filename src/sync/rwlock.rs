//! A phase-fair asynchronous reader-writer lock; the order it grants in
//! is described on its core, `raw_rwlock`.

#![allow(unsafe_code)]

use core::fmt;
use core::future::Future;
use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};
use core::pin::Pin;
use core::task::{Context, Poll};

use super::raw_rwlock::{READ, RawRwLock, RwWait, WRITE};

/// A phase-fair reader-writer lock whose waits are futures.
///
/// Uncontended, a read or write lock and its release are one
/// compare-and-swap each and allocate nothing. Under contention readers
/// and writers take turns: when a writer leaves, every reader waiting at
/// that moment enters together; when that reader phase drains, the oldest
/// waiting writer enters; and a reader arriving while a writer waits
/// waits for it. A reader waits for at most one writer phase, and a
/// writer for at most one reader phase per writer ahead of it. A `try_`
/// form fails while anyone waits for what it would overtake.
///
/// ```
/// use regolith::sync::RwLock;
///
/// let lock = RwLock::new(5);
/// let a = lock.try_read().expect("free");
/// let b = lock.try_read().expect("readers share");
/// assert!(lock.try_write().is_none());
/// drop((a, b));
/// *lock.try_write().expect("free again") += 1;
/// assert_eq!(lock.into_inner(), 6);
/// ```
pub struct RwLock<T: ?Sized> {
    raw: RawRwLock,
    value: core::cell::UnsafeCell<T>,
}

// SAFETY: the value moves with the lock.
unsafe impl<T: ?Sized + Send> Send for RwLock<T> {}
// SAFETY: readers share `&T` across threads and a writer gets `&mut T`
// alone, the same contract as `std::sync::RwLock`.
unsafe impl<T: ?Sized + Send + Sync> Sync for RwLock<T> {}

impl<T> RwLock<T> {
    loom_const_fn! {
        /// An unlocked lock holding `value`.
        pub fn new(value: T) -> Self {
            Self { raw: RawRwLock::new(), value: core::cell::UnsafeCell::new(value) }
        }
    }

    /// Consumes the lock and returns its value.
    pub fn into_inner(self) -> T {
        self.value.into_inner()
    }
}

impl<T: ?Sized> RwLock<T> {
    /// Shares the lock if no writer holds it or waits for it.
    pub fn try_read(&self) -> Option<RwLockReadGuard<'_, T>> {
        self.raw.try_read().then(|| RwLockReadGuard {
            lock: self,
            _value: PhantomData,
        })
    }

    /// Takes the lock alone if nobody holds it or waits for it.
    pub fn try_write(&self) -> Option<RwLockWriteGuard<'_, T>> {
        self.raw.try_write().then(|| RwLockWriteGuard {
            lock: self,
            _value: PhantomData,
        })
    }

    /// Waits to share the lock.
    pub fn read(&self) -> Read<'_, T> {
        Read {
            lock: self,
            wait: RwWait::new(),
        }
    }

    /// Waits to hold the lock alone.
    pub fn write(&self) -> Write<'_, T> {
        Write {
            lock: self,
            wait: RwWait::new(),
        }
    }

    /// The value, borrowed mutably; `&mut self` proves no guard exists.
    pub fn get_mut(&mut self) -> &mut T {
        self.value.get_mut()
    }
}

impl<T: Default> Default for RwLock<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T: ?Sized> fmt::Debug for RwLock<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RwLock").finish_non_exhaustive()
    }
}

/// Shared access to a [`RwLock`]'s value; releases on drop.
#[must_use = "dropping the guard releases the lock at once"]
pub struct RwLockReadGuard<'a, T: ?Sized> {
    lock: &'a RwLock<T>,
    _value: PhantomData<&'a T>,
}

impl<T: ?Sized> Deref for RwLockReadGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // SAFETY: a read share excludes every writer.
        unsafe { &*self.lock.value.get() }
    }
}

impl<T: ?Sized> Drop for RwLockReadGuard<'_, T> {
    fn drop(&mut self) {
        self.lock.raw.read_unlock();
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for RwLockReadGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

/// Exclusive access to a [`RwLock`]'s value; releases on drop.
#[must_use = "dropping the guard releases the lock at once"]
pub struct RwLockWriteGuard<'a, T: ?Sized> {
    lock: &'a RwLock<T>,
    _value: PhantomData<&'a mut T>,
}

impl<T: ?Sized> Deref for RwLockWriteGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // SAFETY: the write side excludes every other guard.
        unsafe { &*self.lock.value.get() }
    }
}

impl<T: ?Sized> DerefMut for RwLockWriteGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: as in `deref`, and `&mut self` makes this borrow unique.
        unsafe { &mut *self.lock.value.get() }
    }
}

impl<T: ?Sized> Drop for RwLockWriteGuard<'_, T> {
    fn drop(&mut self) {
        self.lock.raw.write_unlock();
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for RwLockWriteGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

/// The future [`RwLock::read`] returns.
#[must_use = "futures do nothing unless polled"]
pub struct Read<'a, T: ?Sized> {
    lock: &'a RwLock<T>,
    wait: RwWait,
}

impl<'a, T: ?Sized> Future for Read<'a, T> {
    type Output = RwLockReadGuard<'a, T>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<RwLockReadGuard<'a, T>> {
        let this = self.get_mut();
        this.wait
            .poll(&this.lock.raw, READ, cx.waker())
            .map(|()| RwLockReadGuard {
                lock: this.lock,
                _value: PhantomData,
            })
    }
}

impl<T: ?Sized> Drop for Read<'_, T> {
    fn drop(&mut self) {
        self.wait.cancel(&self.lock.raw, READ);
    }
}

impl<T: ?Sized> fmt::Debug for Read<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Read").finish_non_exhaustive()
    }
}

/// The future [`RwLock::write`] returns.
#[must_use = "futures do nothing unless polled"]
pub struct Write<'a, T: ?Sized> {
    lock: &'a RwLock<T>,
    wait: RwWait,
}

impl<'a, T: ?Sized> Future for Write<'a, T> {
    type Output = RwLockWriteGuard<'a, T>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<RwLockWriteGuard<'a, T>> {
        let this = self.get_mut();
        this.wait
            .poll(&this.lock.raw, WRITE, cx.waker())
            .map(|()| RwLockWriteGuard {
                lock: this.lock,
                _value: PhantomData,
            })
    }
}

impl<T: ?Sized> Drop for Write<'_, T> {
    fn drop(&mut self) {
        self.wait.cancel(&self.lock.raw, WRITE);
    }
}

impl<T: ?Sized> fmt::Debug for Write<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Write").finish_non_exhaustive()
    }
}

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;
    use crate::sync::test_support::{Polled, block_on};
    use std::sync::Arc;
    use std::sync::atomic::{AtomicIsize, Ordering as StdOrdering};

    const ITERATIONS: usize = if cfg!(miri) { 20 } else { 2_000 };

    #[test]
    fn readers_share_and_a_writer_excludes() {
        let lock = RwLock::new(0);
        let a = lock.try_read().expect("free");
        let b = lock.try_read().expect("readers share");
        assert!(lock.try_write().is_none());
        drop((a, b));
        let w = lock.try_write().expect("free");
        assert!(lock.try_read().is_none());
        drop(w);
    }

    #[test]
    fn every_reader_waiting_when_a_writer_leaves_enters_before_the_next_writer() {
        let lock = RwLock::new(());
        let w0 = lock.try_write().expect("free");
        let mut r1 = Polled::new(lock.read());
        r1.pending();
        let mut w1 = Polled::new(lock.write());
        w1.pending();
        let mut r2 = Polled::new(lock.read());
        r2.pending();
        drop(w0);
        assert_eq!((r1.wakes(), r2.wakes(), w1.wakes()), (1, 1, 0));
        let (r1, r2) = (r1.ready(), r2.ready());
        w1.pending();
        drop(r1);
        assert_eq!(w1.wakes(), 0, "the reader phase is not over yet");
        drop(r2);
        assert_eq!(w1.wakes(), 1);
        drop(w1.ready());
    }

    #[test]
    fn a_waiting_writer_holds_back_new_readers_and_goes_next() {
        let lock = RwLock::new(());
        let r0 = lock.try_read().expect("free");
        let mut w1 = Polled::new(lock.write());
        w1.pending();
        assert!(
            lock.try_read().is_none(),
            "a reader must not overtake a waiting writer"
        );
        let mut r2 = Polled::new(lock.read());
        r2.pending();
        drop(r0);
        assert_eq!((w1.wakes(), r2.wakes()), (1, 0));
        drop(w1.ready());
        assert_eq!(r2.wakes(), 1);
        drop(r2.ready());
    }

    #[test]
    fn a_withdrawn_writer_lets_the_readers_behind_it_join() {
        let lock = RwLock::new(());
        let r0 = lock.try_read().expect("free");
        let mut w1 = Polled::new(lock.write());
        w1.pending();
        let mut r2 = Polled::new(lock.read());
        r2.pending();
        drop(w1);
        assert_eq!(r2.wakes(), 1);
        drop(r2.ready());
        drop(r0);
        assert!(lock.try_write().is_some());
    }

    #[test]
    fn a_writer_that_never_saw_its_grant_passes_the_lock_on() {
        let lock = RwLock::new(());
        let r0 = lock.try_read().expect("free");
        let mut w1 = Polled::new(lock.write());
        w1.pending();
        let mut r2 = Polled::new(lock.read());
        r2.pending();
        drop(r0);
        assert_eq!(w1.wakes(), 1);
        drop(w1);
        assert_eq!(r2.wakes(), 1);
        drop(r2.ready());
        assert!(lock.try_write().is_some());
    }

    #[test]
    fn threads_see_readers_xor_one_writer() {
        let lock = Arc::new(RwLock::new(()));
        let inside = Arc::new(AtomicIsize::new(0));
        let threads: Vec<_> = (0..4)
            .map(|t| {
                let (lock, inside) = (Arc::clone(&lock), Arc::clone(&inside));
                std::thread::spawn(move || {
                    for i in 0..ITERATIONS {
                        if (i + t) % 3 == 0 {
                            let _w = block_on(lock.write());
                            assert_eq!(inside.swap(-1, StdOrdering::SeqCst), 0);
                            std::hint::spin_loop();
                            assert_eq!(inside.swap(0, StdOrdering::SeqCst), -1);
                        } else {
                            let _r = block_on(lock.read());
                            assert!(inside.fetch_add(1, StdOrdering::SeqCst) >= 0);
                            std::hint::spin_loop();
                            inside.fetch_sub(1, StdOrdering::SeqCst);
                        }
                    }
                })
            })
            .collect();
        for thread in threads {
            thread.join().expect("worker");
        }
        assert!(lock.try_write().is_some());
    }
}
