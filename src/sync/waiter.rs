//! Waiter nodes, the free list that recycles them, and the wake list a
//! drain pass hands granted waiters to.
//!
//! A contended future parks one [`Waiter`] in its primitive's queue. Two
//! parties hold the node at once: the future, until it completes or is
//! dropped, and the queue, until a drain pass grants or prunes it. Each
//! holds one reference bit in the node's state word, and whichever party
//! clears the last bit returns the node to its primitive's [`Pool`]. No
//! other path frees a node, so a node is never reachable by a party that
//! has let it go, and no epoch scheme is needed.
//!
//! # State word
//!
//! | bits | meaning |
//! |---|---|
//! | 0-1 | phase: waiting, granted or cancelled; it leaves waiting once |
//! | 2 | the future is replacing its waker |
//! | 3 | the queue's reference |
//! | 4 | the future's reference |
//!
//! The future writes the waker slot only while it holds the registering
//! bit in the waiting phase. A drainer reads the slot only after it moved
//! the phase to granted while that bit was clear. A cancelling future
//! reads it only after it moved the phase to cancelled. So no two parties
//! ever touch the slot at once.

#![allow(unsafe_code)]

use core::mem;
use core::ptr::{self, NonNull};
use core::task::{Poll, Waker};

use super::internal::{AtomicPtr, AtomicUsize, Ordering, UnsafeCell};
use super::queue::WaitQueue;

const PHASE: usize = 0b11;
const WAITING: usize = 0;
const GRANTED: usize = 1;
const CANCELLED: usize = 2;
const REGISTERING: usize = 1 << 2;
const QUEUE_REF: usize = 1 << 3;
const FUTURE_REF: usize = 1 << 4;

/// Nodes a primitive keeps for reuse; past this the allocator gets them
/// back, so a burst of contention cannot pin memory forever.
#[cfg(not(loom))]
const POOL_CAPACITY: usize = 16;

/// One parked wait.
pub(super) struct Waiter {
    state: AtomicUsize,
    next: AtomicPtr<Waiter>,
    payload: AtomicUsize,
    waker: UnsafeCell<Option<Waker>>,
}

/// What a drainer's grant found.
enum Granted {
    /// Granted; the drainer owns the waker and must wake it.
    Wake,
    /// Granted while the future was mid-poll; it sees the grant itself.
    Polling,
    /// The future withdrew first.
    Cancelled,
}

impl Waiter {
    fn new() -> Self {
        Self {
            state: AtomicUsize::new(0),
            next: AtomicPtr::new(ptr::null_mut()),
            payload: AtomicUsize::new(0),
            waker: UnsafeCell::new(None),
        }
    }

    /// The link the arrival stack, a waiting list or a wake list threads
    /// through; only the party holding the node in that structure uses it.
    pub(super) fn next(&self) -> *mut Waiter {
        self.next.load(Ordering::Relaxed)
    }

    pub(super) fn set_next(&self, next: *mut Waiter) {
        self.next.store(next, Ordering::Relaxed);
    }

    /// What the waiter asked for: a permit count, a lock kind, a
    /// generation. Written before the node is published, so a drainer
    /// that took the node sees it.
    pub(super) fn payload(&self) -> usize {
        self.payload.load(Ordering::Relaxed)
    }

    /// Overwrites the payload. A drainer uses this before a grant to tell
    /// the future how it was granted; the grant publishes the store.
    pub(super) fn set_payload(&self, payload: usize) {
        self.payload.store(payload, Ordering::Relaxed);
    }

    pub(super) fn is_cancelled(&self) -> bool {
        self.state.load(Ordering::Acquire) & PHASE == CANCELLED
    }

    fn arm(&self, payload: usize, waker: Waker) {
        self.state
            .store(WAITING | QUEUE_REF | FUTURE_REF, Ordering::Relaxed);
        self.next.store(ptr::null_mut(), Ordering::Relaxed);
        self.payload.store(payload, Ordering::Relaxed);
        // SAFETY: the node came out of the pool, so nobody else sees it.
        self.waker.with_mut(|slot| unsafe { *slot = Some(waker) });
    }

    /// Moves a waiting node to granted.
    fn grant(&self) -> Granted {
        let mut state = self.state.load(Ordering::Acquire);
        loop {
            if state & PHASE == CANCELLED {
                return Granted::Cancelled;
            }
            debug_assert_eq!(state & PHASE, WAITING, "a waiter is granted twice");
            match self.state.compare_exchange_weak(
                state,
                state | GRANTED,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) if state & REGISTERING != 0 => return Granted::Polling,
                Ok(_) => return Granted::Wake,
                Err(actual) => state = actual,
            }
        }
    }

    /// Replaces the waker unless the node is already granted. Returns
    /// whether it is granted.
    fn register(&self, waker: &Waker) -> bool {
        let mut state = self.state.load(Ordering::Acquire);
        loop {
            if state & PHASE == GRANTED {
                return true;
            }
            match self.state.compare_exchange_weak(
                state,
                state | REGISTERING,
                Ordering::Acquire,
                Ordering::Acquire,
            ) {
                Ok(_) => break,
                Err(actual) => state = actual,
            }
        }
        // SAFETY: the registering bit in the waiting phase keeps every
        // drainer off the slot (module docs).
        self.waker.with_mut(|slot| unsafe {
            if !(*slot).as_ref().is_some_and(|w| w.will_wake(waker)) {
                *slot = Some(waker.clone());
            }
        });
        self.state.fetch_and(!REGISTERING, Ordering::AcqRel) & PHASE == GRANTED
    }

    /// Moves a waiting node to cancelled. Returns false when it was
    /// already granted.
    fn withdraw(&self) -> bool {
        let mut state = self.state.load(Ordering::Acquire);
        loop {
            if state & PHASE == GRANTED {
                return false;
            }
            match self.state.compare_exchange_weak(
                state,
                state | CANCELLED,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => return true,
                Err(actual) => state = actual,
            }
        }
    }

    /// # Safety
    ///
    /// The caller has exclusive access to the waker slot (module docs).
    unsafe fn take_waker(&self) -> Option<Waker> {
        // SAFETY: forwarded from the caller.
        self.waker.with_mut(|slot| unsafe { (*slot).take() })
    }
}

/// Drops one party's reference; the last party out recycles the node.
///
/// The caller must hold `bit` on `node`.
fn release(node: NonNull<Waiter>, bit: usize, pool: &Pool) {
    // SAFETY: the caller still holds `bit`, so the node is live.
    let prev = unsafe { node.as_ref() }
        .state
        .fetch_and(!bit, Ordering::AcqRel);
    if prev & (QUEUE_REF | FUTURE_REF) == bit {
        pool.put(node);
    }
}

/// Lets go of the queue's reference to `node`, which the caller took off
/// its arrival stack or waiting list.
pub(super) fn release_queued(node: NonNull<Waiter>, pool: &Pool) {
    release(node, QUEUE_REF, pool);
}

/// A pooled node, owned by whoever holds this value.
#[cfg(not(loom))]
struct Pooled(NonNull<Waiter>);

// SAFETY: a pooled node is referenced by nothing but its `Pooled`.
#[cfg(not(loom))]
unsafe impl Send for Pooled {}

/// A primitive's free list of waiter nodes.
///
/// The ring is kovan's bounded lock-free MPMC queue, allocated the first
/// time a node is returned, so a primitive that never contends never
/// allocates. Under `--cfg loom` the pool is a pass-through to the
/// allocator: loom cannot see inside kovan's queue, and a hand-off it
/// cannot see would read to it as a data race.
pub(super) struct Pool {
    #[cfg(not(loom))]
    ring: core::sync::atomic::AtomicPtr<kovan_queue::array_queue::ArrayQueue<Pooled>>,
}

impl Pool {
    pub(super) const fn new() -> Self {
        Self {
            #[cfg(not(loom))]
            ring: core::sync::atomic::AtomicPtr::new(ptr::null_mut()),
        }
    }

    fn take(&self) -> NonNull<Waiter> {
        #[cfg(not(loom))]
        {
            let ring = self.ring.load(Ordering::Acquire);
            // SAFETY: a published ring lives until the pool drops.
            if let Some(Pooled(node)) = unsafe { ring.as_ref() }.and_then(|ring| ring.pop()) {
                return node;
            }
        }
        NonNull::from(Box::leak(Box::new(Waiter::new())))
    }

    fn put(&self, node: NonNull<Waiter>) {
        // SAFETY: both references are gone, so the caller owns the node
        // and its waker slot outright.
        drop(unsafe { node.as_ref().take_waker() });
        #[cfg(not(loom))]
        let node = match self.ring().push(Pooled(node)) {
            Ok(()) => return,
            Err(Pooled(node)) => node,
        };
        // SAFETY: every node is a leaked `Box` and this one is unreferenced.
        drop(unsafe { Box::from_raw(node.as_ptr()) });
    }

    #[cfg(not(loom))]
    fn ring(&self) -> &kovan_queue::array_queue::ArrayQueue<Pooled> {
        let ring = self.ring.load(Ordering::Acquire);
        // SAFETY: a published ring lives until the pool drops.
        if let Some(ring) = unsafe { ring.as_ref() } {
            return ring;
        }
        let fresh = Box::into_raw(Box::new(kovan_queue::array_queue::ArrayQueue::new(
            POOL_CAPACITY,
        )));
        match self.ring.compare_exchange(
            ptr::null_mut(),
            fresh,
            Ordering::AcqRel,
            Ordering::Acquire,
        ) {
            // SAFETY: just published; it lives until the pool drops.
            Ok(_) => unsafe { &*fresh },
            Err(winner) => {
                // SAFETY: `fresh` lost the race and was never shared.
                drop(unsafe { Box::from_raw(fresh) });
                // SAFETY: as above, for the winner's ring.
                unsafe { &*winner }
            }
        }
    }
}

impl Drop for Pool {
    fn drop(&mut self) {
        #[cfg(not(loom))]
        {
            let ring = *self.ring.get_mut();
            if !ring.is_null() {
                // SAFETY: the pool owns its ring and is being dropped.
                let ring = unsafe { Box::from_raw(ring) };
                while let Some(Pooled(node)) = ring.pop() {
                    // SAFETY: a pooled node is an unreferenced leaked `Box`.
                    drop(unsafe { Box::from_raw(node.as_ptr()) });
                }
            }
        }
    }
}

/// Waiters a drain pass granted, woken in grant order once the pass has
/// given up the drain role, so no executor code runs while it holds it.
pub(super) struct WakeList<'a> {
    head: *mut Waiter,
    tail: *mut Waiter,
    pool: &'a Pool,
}

impl<'a> WakeList<'a> {
    pub(super) fn new(pool: &'a Pool) -> Self {
        Self {
            head: ptr::null_mut(),
            tail: ptr::null_mut(),
            pool,
        }
    }

    /// Grants `node`, which the caller took off its waiting list with the
    /// queue's reference. Returns false when the future had withdrawn, in
    /// which case the caller gives back whatever it set aside for it.
    pub(super) fn grant(&mut self, node: NonNull<Waiter>) -> bool {
        // SAFETY: the caller holds the queue's reference.
        match unsafe { node.as_ref() }.grant() {
            Granted::Wake => {
                // SAFETY: as above; the node is off every list.
                unsafe { node.as_ref() }.set_next(ptr::null_mut());
                match NonNull::new(self.tail) {
                    // SAFETY: the tail is a node this list holds.
                    Some(tail) => unsafe { tail.as_ref() }.set_next(node.as_ptr()),
                    None => self.head = node.as_ptr(),
                }
                self.tail = node.as_ptr();
                true
            }
            Granted::Polling => {
                release(node, QUEUE_REF, self.pool);
                true
            }
            Granted::Cancelled => {
                release(node, QUEUE_REF, self.pool);
                false
            }
        }
    }

    fn pop(&mut self) -> Option<Option<Waker>> {
        let node = NonNull::new(self.head)?;
        // SAFETY: this list holds the queue's reference to `node`.
        let waiter = unsafe { node.as_ref() };
        self.head = waiter.next();
        if self.head.is_null() {
            self.tail = ptr::null_mut();
        }
        // SAFETY: granted while the future was not registering, so the
        // slot is the drainer's (module docs).
        let waker = unsafe { waiter.take_waker() };
        release(node, QUEUE_REF, self.pool);
        Some(waker)
    }
}

impl Drop for WakeList<'_> {
    fn drop(&mut self) {
        while let Some(waker) = self.pop() {
            if let Some(waker) = waker {
                // A waker that panics must not strand the waiters behind
                // it: they already own what they were granted.
                let rest = WakeRest(self);
                waker.wake();
                mem::forget(rest);
            }
        }
    }
}

struct WakeRest<'b, 'a>(&'b mut WakeList<'a>);

impl Drop for WakeRest<'_, '_> {
    fn drop(&mut self) {
        while let Some(waker) = self.0.pop() {
            if let Some(waker) = waker {
                waker.wake();
            }
        }
    }
}

/// How a cancelled future left its queue.
pub(super) enum Cancel {
    /// It never queued, or it already completed.
    Idle,
    /// It withdrew before anyone granted it; its owner tells the queue.
    Withdrawn,
    /// It had been granted, so its owner passes the grant on. Carries the
    /// payload the drainer left.
    Granted(usize),
}

/// A future's hold on its waiter node.
pub(super) struct Wait {
    node: Option<NonNull<Waiter>>,
}

impl Wait {
    pub(super) const fn new() -> Self {
        Self { node: None }
    }

    pub(super) fn is_queued(&self) -> bool {
        self.node.is_some()
    }

    /// Arms a node from `queue`'s pool and pushes it on the arrival
    /// stack. The caller then publishes it with a draining transition.
    pub(super) fn enqueue(&mut self, queue: &WaitQueue, payload: usize, waker: &Waker) {
        debug_assert!(self.node.is_none(), "a future queues twice");
        let node = queue.pool().take();
        // SAFETY: fresh from the pool, so this future owns it alone.
        unsafe { node.as_ref() }.arm(payload, waker.clone());
        queue.push(node);
        self.node = Some(node);
    }

    /// Ready once granted, with the payload the drainer left; the node is
    /// released then. With `waker`, registers it first.
    pub(super) fn poll(&mut self, queue: &WaitQueue, waker: Option<&Waker>) -> Poll<usize> {
        let Some(node) = self.node else {
            return Poll::Ready(0);
        };
        // SAFETY: this future holds its reference until it clears `node`.
        let waiter = unsafe { node.as_ref() };
        let granted = match waker {
            Some(waker) => waiter.register(waker),
            None => waiter.state.load(Ordering::Acquire) & PHASE == GRANTED,
        };
        if !granted {
            return Poll::Pending;
        }
        let payload = waiter.payload();
        self.node = None;
        release(node, FUTURE_REF, queue.pool());
        Poll::Ready(payload)
    }

    /// Withdraws the waiter, or reports that it was granted first.
    pub(super) fn cancel(&mut self, queue: &WaitQueue) -> Cancel {
        let Some(node) = self.node.take() else {
            return Cancel::Idle;
        };
        // SAFETY: this future held its reference until now.
        let waiter = unsafe { node.as_ref() };
        let outcome = if waiter.withdraw() {
            // SAFETY: a cancelled node's slot is the future's (module docs).
            drop(unsafe { waiter.take_waker() });
            Cancel::Withdrawn
        } else {
            Cancel::Granted(waiter.payload())
        };
        release(node, FUTURE_REF, queue.pool());
        outcome
    }
}

// SAFETY: the node is shared only through the protocol in the module
// docs, which every access follows whichever thread makes it.
unsafe impl Send for Wait {}
// SAFETY: `&Wait` exposes nothing.
unsafe impl Sync for Wait {}
