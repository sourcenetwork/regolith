//! A fair asynchronous mutex: a one-permit semaphore around a value.

#![allow(unsafe_code)]

use core::cell::UnsafeCell;
use core::fmt;
use core::future::Future;
use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};
use core::pin::Pin;
use core::task::{Context, Poll};
use std::sync::Arc;

use super::raw_semaphore::{PermitWait, RawSemaphore};

/// A mutual-exclusion lock whose wait is a future.
///
/// Uncontended, [`try_lock`](Self::try_lock) and a guard's drop are one
/// atomic read-modify-write each and allocate nothing. A caller takes the
/// lock whenever it is free, even while others wait; under contention
/// [`lock`](Self::lock) spins briefly, then queues and returns `Pending`.
/// An unlock wakes the oldest waiter to try again; a waiter that loses
/// [`MAX_BYPASS`](super::MAX_BYPASS) times is handed the lock directly,
/// and `try_lock` fails until it has had it.
///
/// ```
/// use regolith::sync::Mutex;
///
/// let counter = Mutex::new(0u32);
/// *counter.try_lock().expect("uncontended") += 1;
/// assert_eq!(counter.into_inner(), 1);
/// ```
pub struct Mutex<T: ?Sized> {
    sem: RawSemaphore,
    value: UnsafeCell<T>,
}

// SAFETY: the value moves with the mutex.
unsafe impl<T: ?Sized + Send> Send for Mutex<T> {}
// SAFETY: the semaphore admits one guard at a time, and a guard hands out
// the value only as `&mut T` or `&T` under that exclusion.
unsafe impl<T: ?Sized + Send> Sync for Mutex<T> {}

impl<T> Mutex<T> {
    loom_const_fn! {
        /// An unlocked mutex holding `value`.
        pub fn new(value: T) -> Self {
            Self { sem: RawSemaphore::new(1), value: UnsafeCell::new(value) }
        }
    }

    /// Consumes the mutex and returns its value.
    pub fn into_inner(self) -> T {
        self.value.into_inner()
    }
}

impl<T: ?Sized> Mutex<T> {
    /// Locks the mutex if it is free and no handoff is owed.
    pub fn try_lock(&self) -> Option<MutexGuard<'_, T>> {
        self.sem.try_acquire(1).then(|| MutexGuard::new(self))
    }

    /// Waits for the lock.
    pub fn lock(&self) -> Lock<'_, T> {
        Lock {
            mutex: self,
            wait: PermitWait::new(),
        }
    }

    /// Waits for the lock through an `Arc`, so the guard can outlive the
    /// borrow.
    pub fn lock_owned(self: &Arc<Self>) -> LockOwned<T> {
        LockOwned {
            mutex: Arc::clone(self),
            wait: PermitWait::new(),
        }
    }

    /// The value, borrowed mutably; `&mut self` proves no guard exists.
    pub fn get_mut(&mut self) -> &mut T {
        self.value.get_mut()
    }
}

impl<T: Default> Default for Mutex<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T: ?Sized> fmt::Debug for Mutex<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Mutex")
            .field("locked", &(self.sem.available() == 0))
            .finish_non_exhaustive()
    }
}

/// Exclusive access to a [`Mutex`]'s value; unlocks on drop.
#[must_use = "dropping the guard unlocks the mutex at once"]
pub struct MutexGuard<'a, T: ?Sized> {
    mutex: &'a Mutex<T>,
    // `Sync` only when `T: Sync`, since `&MutexGuard` reaches `&T`.
    _value: PhantomData<&'a mut T>,
}

impl<'a, T: ?Sized> MutexGuard<'a, T> {
    fn new(mutex: &'a Mutex<T>) -> Self {
        Self {
            mutex,
            _value: PhantomData,
        }
    }
}

impl<T: ?Sized> Deref for MutexGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // SAFETY: this guard holds the mutex's only permit.
        unsafe { &*self.mutex.value.get() }
    }
}

impl<T: ?Sized> DerefMut for MutexGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: as in `deref`, and `&mut self` makes this borrow unique.
        unsafe { &mut *self.mutex.value.get() }
    }
}

impl<T: ?Sized> Drop for MutexGuard<'_, T> {
    fn drop(&mut self) {
        self.mutex.sem.release(1);
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for MutexGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

/// Exclusive access to a [`Mutex`] held through an `Arc`; unlocks on drop.
#[must_use = "dropping the guard unlocks the mutex at once"]
pub struct OwnedMutexGuard<T: ?Sized> {
    mutex: Arc<Mutex<T>>,
    // `Sync` only when `T: Sync`, since `&OwnedMutexGuard` reaches `&T`.
    _value: PhantomData<UnsafeCell<T>>,
}

// SAFETY: sharing the guard shares `&T`, which needs `T: Sync`.
unsafe impl<T: ?Sized + Send + Sync> Sync for OwnedMutexGuard<T> {}

impl<T: ?Sized> OwnedMutexGuard<T> {
    /// The mutex this guard locks.
    pub fn mutex(&self) -> &Arc<Mutex<T>> {
        &self.mutex
    }
}

impl<T: ?Sized> Deref for OwnedMutexGuard<T> {
    type Target = T;

    fn deref(&self) -> &T {
        // SAFETY: this guard holds the mutex's only permit.
        unsafe { &*self.mutex.value.get() }
    }
}

impl<T: ?Sized> DerefMut for OwnedMutexGuard<T> {
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: as in `deref`, and `&mut self` makes this borrow unique.
        unsafe { &mut *self.mutex.value.get() }
    }
}

impl<T: ?Sized> Drop for OwnedMutexGuard<T> {
    fn drop(&mut self) {
        self.mutex.sem.release(1);
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for OwnedMutexGuard<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

/// The future [`Mutex::lock`] returns.
#[must_use = "futures do nothing unless polled"]
pub struct Lock<'a, T: ?Sized> {
    mutex: &'a Mutex<T>,
    wait: PermitWait,
}

impl<'a, T: ?Sized> Future for Lock<'a, T> {
    type Output = MutexGuard<'a, T>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<MutexGuard<'a, T>> {
        let this = self.get_mut();
        this.wait
            .poll(&this.mutex.sem, 1, cx.waker())
            .map(|()| MutexGuard::new(this.mutex))
    }
}

impl<T: ?Sized> Drop for Lock<'_, T> {
    fn drop(&mut self) {
        self.wait.cancel(&self.mutex.sem, 1);
    }
}

impl<T: ?Sized> fmt::Debug for Lock<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Lock").finish_non_exhaustive()
    }
}

/// The future [`Mutex::lock_owned`] returns.
#[must_use = "futures do nothing unless polled"]
pub struct LockOwned<T: ?Sized> {
    mutex: Arc<Mutex<T>>,
    wait: PermitWait,
}

impl<T: ?Sized> Future for LockOwned<T> {
    type Output = OwnedMutexGuard<T>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<OwnedMutexGuard<T>> {
        let this = self.get_mut();
        this.wait
            .poll(&this.mutex.sem, 1, cx.waker())
            .map(|()| OwnedMutexGuard {
                mutex: Arc::clone(&this.mutex),
                _value: PhantomData,
            })
    }
}

impl<T: ?Sized> Drop for LockOwned<T> {
    fn drop(&mut self) {
        self.wait.cancel(&self.mutex.sem, 1);
    }
}

impl<T: ?Sized> fmt::Debug for LockOwned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LockOwned").finish_non_exhaustive()
    }
}

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;
    use crate::sync::test_support::{Polled, block_on};

    const ITERATIONS: usize = if cfg!(miri) { 20 } else { 5_000 };

    #[test]
    fn releases_wake_waiters_in_arrival_order() {
        let mutex = Mutex::new(Vec::new());
        let held = mutex.try_lock().expect("free");
        let mut waiters: Vec<_> = (0..3).map(|_| Polled::new(mutex.lock())).collect();
        for waiter in &mut waiters {
            waiter.pending();
        }
        drop(held);
        for (i, waiter) in waiters.iter_mut().enumerate() {
            assert_eq!(
                waiter.wakes(),
                1,
                "waiter {i} is woken by the release before it"
            );
            let mut guard = waiter.ready();
            guard.push(i);
            assert!(mutex.try_lock().is_none(), "the woken waiter holds it");
        }
        assert_eq!(*mutex.try_lock().expect("free"), vec![0, 1, 2]);
    }

    #[test]
    fn a_waiter_that_never_saw_its_grant_passes_the_lock_on() {
        let mutex = Mutex::new(());
        let held = mutex.try_lock().expect("free");
        let mut first = Polled::new(mutex.lock());
        first.pending();
        let mut second = Polled::new(mutex.lock());
        second.pending();
        drop(held);
        drop(first);
        drop(second.ready());
        assert!(mutex.try_lock().is_some());
    }

    #[test]
    fn a_waker_changed_between_polls_is_the_one_woken() {
        let mutex = Mutex::new(());
        let held = mutex.try_lock().expect("free");
        let mut lock = core::pin::pin!(mutex.lock());
        let first = Polled::new(core::future::pending::<()>());
        let second = Polled::new(core::future::pending::<()>());
        let poll_with = |lock: &mut Pin<&mut Lock<'_, ()>>, waker: &core::task::Waker| {
            lock.as_mut()
                .poll(&mut Context::from_waker(waker))
                .is_pending()
        };
        let (first_waker, second_waker) = (first.waker(), second.waker());
        assert!(poll_with(&mut lock, &first_waker));
        assert!(poll_with(&mut lock, &second_waker));
        drop(held);
        assert_eq!((first.wakes(), second.wakes()), (0, 1));
        assert!(!poll_with(&mut lock, &second_waker));
    }

    #[test]
    fn owned_guards_and_get_mut() {
        let mut mutex = Mutex::new(1);
        *mutex.get_mut() += 1;
        let mutex = Arc::new(mutex);
        let guard = block_on(mutex.lock_owned());
        let mut next = Polled::new(mutex.lock_owned());
        next.pending();
        assert_eq!(*guard, 2);
        drop(guard);
        assert_eq!(*next.ready(), 2);
    }

    #[test]
    fn threads_never_overlap_inside_the_lock() {
        let mutex = Arc::new(Mutex::new(0usize));
        let threads: Vec<_> = (0..4)
            .map(|_| {
                let mutex = Arc::clone(&mutex);
                std::thread::spawn(move || {
                    for _ in 0..ITERATIONS {
                        let mut guard = block_on(mutex.lock());
                        let seen = *guard;
                        std::hint::spin_loop();
                        *guard = seen + 1;
                    }
                })
            })
            .collect();
        for thread in threads {
            thread.join().expect("worker");
        }
        assert_eq!(*mutex.try_lock().expect("free"), 4 * ITERATIONS);
    }
}
