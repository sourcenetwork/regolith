//! Asynchronous synchronization primitives that never block a thread.
//!
//! Every wait in this module is a [`Future`] that
//! needs no runtime: async code awaits it, and a pinned-thread pool polls
//! it with its own [`Waker`](core::task::Waker). Every primitive also has
//! `try_` forms that never wait. Nothing here makes a system call: no
//! futex, no thread park, no sleep and no clock read. The one exception is
//! inside kovan's queues, which recycle waiter nodes and yield the thread
//! when they meet contention.
//!
//! # What every primitive guarantees
//!
//! - **No runtime.** A contended acquire queues a waiter, registers the
//!   caller's `Waker` and returns `Pending`. What a wake does belongs to
//!   the caller's executor.
//! - **Fast under contention.** The locks and the semaphore let a caller
//!   take what is free even while others wait, after a brief spin before
//!   it queues, so a release never waits for a suspended task to run: the
//!   thread that released takes the lock straight back.
//! - **Bounded bypass.** A release wakes the oldest waiters it could
//!   serve to compete again. One that loses [`MAX_BYPASS`] times is owed a
//!   handoff: nobody gets in ahead of it, and the next release hands it
//!   what it waits for directly. Fairness is counted, never timed.
//! - **Cancellation-safe.** Dropping a pending future withdraws its
//!   waiter. If something was handed to it concurrently, the drop passes
//!   it on. No wakeup is lost.
//! - **Reentrancy by [`Owner`].** The reentrant locks are keyed by an
//!   owner token rather than a thread, because a task can move between
//!   threads and many tasks can share one.
//! - **Every target.** State lives in word-sized atomics. On
//!   single-threaded wasm the same code runs on one thread, where only
//!   interleaved tasks contend. The fast paths allocate nothing; a waiter
//!   node comes from a per-primitive free list and reaches the allocator
//!   only when that list is empty.
//!
//! # How a wait works
//!
//! Each primitive keeps one state word, a lock-free stack of arriving
//! waiters and a FIFO of the waiters already sorted. Uncontended calls
//! touch the state word only, one atomic read-modify-write each. Anything
//! that can make a waiter runnable (a release, a new waiter, a
//! cancellation) takes the drain role with one compare-and-swap, or, when
//! another thread holds it, marks the state dirty and returns, so no call
//! ever waits for another. The holder wakes what the state allows (or,
//! while a handoff is owed, grants it in queue order), rechecks until
//! nothing changed while it worked, and calls the wakers after it has
//! given the role up.
//!
//! Besides the primitives, this module re-exports kovan's lock-free
//! channels (their non-blocking half), map, queues and [`Atom`], so one
//! module holds every synchronization structure.

/// Defines a constructor as a `const fn` in an ordinary build and as a
/// plain `fn` under `--cfg loom`, whose instrumented atomics cannot be
/// built in a constant context.
macro_rules! loom_const_fn {
    ($(#[$attr:meta])* $vis:vis fn $name:ident($($arg:ident : $ty:ty),* $(,)?) -> $ret:ty $body:block) => {
        $(#[$attr])*
        #[cfg(not(loom))]
        $vis const fn $name($($arg: $ty),*) -> $ret $body

        $(#[$attr])*
        #[cfg(loom)]
        $vis fn $name($($arg: $ty),*) -> $ret $body
    };
}

mod barrier;
mod channel;
mod contend;
mod event;
pub(crate) mod internal;
mod latch;
mod lazy;
mod list;
mod mutex;
mod notify;
mod once_cell;
mod owner;
mod queue;
mod raw_rwlock;
mod raw_semaphore;
mod reentrant_mutex;
mod reentrant_rwlock;
mod rwlock;
mod semaphore;
#[cfg(all(test, not(loom)))]
mod test_support;
mod waiter;

pub use barrier::{Barrier, BarrierWait, BarrierWaitResult};
pub use channel::{
    BoundedReceiver, BoundedSender, UnboundedReceiver, UnboundedSender, bounded, unbounded,
};
pub use contend::MAX_BYPASS;
pub use event::{Event, EventWait};
pub use latch::{Latch, LatchWait};
pub use lazy::Lazy;
pub use mutex::{Lock, LockOwned, Mutex, MutexGuard, OwnedMutexGuard};
pub use notify::{Notified, Notify};
pub use once_cell::OnceCell;
pub use owner::{Owner, ThreadOwner};
pub use reentrant_mutex::{ReentrantMutex, ReentrantMutexGuard, ReentrantMutexLock};
pub use reentrant_rwlock::{
    ReadHeldByOwner, ReentrantRead, ReentrantReadGuard, ReentrantRwLock, ReentrantWrite,
    ReentrantWriteGuard,
};
pub use rwlock::{
    Read, RwLock, RwLockReadGuard, RwLockUpgradableReadGuard, RwLockWriteGuard, UpgradableRead,
    Upgrade, Write,
};
pub use semaphore::{Acquire, AcquireOwned, OwnedSemaphorePermit, Semaphore, SemaphorePermit};

pub use kovan::Atom;
pub use kovan_map::HopscotchMap;
pub use kovan_queue::array_queue::ArrayQueue;
pub use kovan_queue::seg_queue::SegQueue;

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;

    fn send_sync<T: Send + Sync>() {}

    fn future_is_send_sync<F: core::future::Future + Send + Sync>(_: &F) {}

    #[test]
    fn handles_futures_and_guards_are_send_and_sync() {
        send_sync::<Mutex<u8>>();
        send_sync::<Lock<'static, u8>>();
        send_sync::<LockOwned<u8>>();
        send_sync::<MutexGuard<'static, u8>>();
        send_sync::<OwnedMutexGuard<u8>>();
        send_sync::<RwLock<u8>>();
        send_sync::<Read<'static, u8>>();
        send_sync::<Write<'static, u8>>();
        send_sync::<RwLockReadGuard<'static, u8>>();
        send_sync::<RwLockWriteGuard<'static, u8>>();
        send_sync::<RwLockUpgradableReadGuard<'static, u8>>();
        send_sync::<UpgradableRead<'static, u8>>();
        send_sync::<Upgrade<'static, u8>>();
        send_sync::<ReadHeldByOwner>();
        send_sync::<Semaphore>();
        send_sync::<Acquire<'static>>();
        send_sync::<AcquireOwned>();
        send_sync::<SemaphorePermit<'static>>();
        send_sync::<OwnedSemaphorePermit>();
        send_sync::<Notify>();
        send_sync::<Notified<'static>>();
        send_sync::<Event>();
        send_sync::<EventWait<'static>>();
        send_sync::<Latch>();
        send_sync::<LatchWait<'static>>();
        send_sync::<Barrier>();
        send_sync::<BarrierWait<'static>>();
        send_sync::<OnceCell<u8>>();
        send_sync::<Lazy<u8>>();
        send_sync::<ReentrantMutex<core::cell::RefCell<u8>>>();
        send_sync::<ReentrantRwLock<u8>>();
        send_sync::<UnboundedSender<u8>>();
        send_sync::<UnboundedReceiver<u8>>();
        send_sync::<BoundedSender<u8>>();
        send_sync::<BoundedReceiver<u8>>();
        // An owner moves with its task but is never shared (see `Owner`).
        send::<Owner>();
    }

    fn send<T: Send>() {}

    #[test]
    fn async_entry_points_return_send_and_sync_futures() {
        let cell = OnceCell::<u8>::new();
        future_is_send_sync(&cell.get_or_init(async { 1 }));
        future_is_send_sync(&cell.get_or_try_init(async { Ok::<u8, ()>(1) }));
        let (tx, rx) = bounded::<u8>(1);
        future_is_send_sync(&tx.send_async(1));
        future_is_send_sync(&rx.recv_async());
        let (tx, rx) = unbounded::<u8>();
        future_is_send_sync(&tx.send_async(1));
        future_is_send_sync(&rx.recv_async());
    }
}
