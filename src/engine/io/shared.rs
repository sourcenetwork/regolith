//! The half of an I/O queue other threads reach: its inbox, its idle waker,
//! the bytes of reads it owes, and the reads that landed for it.
//!
//! Only the queue's owner takes from the inbox; any thread pushes to it. A
//! `CacheOnly` read pushes a request there, whatever thread it runs on, the
//! thread that finishes a unit pushes the completion there, and the thread
//! whose read frees an open-file slot a parked unit wanted pushes that
//! there. A push that finds the owner idle wakes it, once; a push to a busy
//! owner wakes nobody.

use std::io;
use std::sync::{Arc, OnceLock};

use kovan_map::HashMap;

use super::Landed;
use super::atomic_waker::AtomicWaker;
use super::stack::{IDLE, Rest, SHUT, Stack};
use super::unit::{Unit, UnitKey};
use crate::env::open_file_limit::slots::SlotWaiter;
use crate::io_queue::QueueId;
use crate::sync::internal::{AtomicUsize, Ordering};

/// Buckets a queue's landing table starts with. It holds at most what the
/// queue's byte bound admits, so it stays small.
const LANDED_BUCKETS: usize = 64;

/// What reaches an owner through its inbox.
pub(crate) enum Message {
    /// A read on this queue missed `unit`; `slot` is the read's wait.
    Read {
        unit: Arc<Unit>,
        slot: Arc<WaitSlot>,
    },
    /// A read found the queue's byte bound full; `slot` is ready once the
    /// queue owes less.
    Room(Arc<WaitSlot>),
    /// `unit` finished; one per unit this queue registered on.
    Done(Arc<Unit>),
    /// An open-file slot freed that a unit this queue parked was waiting
    /// for (D60): run the queue's parked units again.
    SlotFreed,
}

/// What a finished unit left for the reads of one queue.
#[derive(Clone)]
pub(crate) enum Landing {
    /// The block, metadata block or filter the unit read.
    Ready(Landed),
    /// The read failed; the next read of the block on this queue reports it.
    Failed(Arc<io::Error>),
}

pub(crate) struct QueueShared {
    id: QueueId,
    inbox: Stack<Message>,
    idle: AtomicWaker,
    /// Bytes of device reads this queue owes: one unit's frame per pending
    /// request, released when the request completes.
    pending: AtomicUsize,
    /// The most `pending` may reach; a single read larger than it is still
    /// admitted when nothing else is pending.
    bound: usize,
    /// Reads that landed for this queue, so a read run again finds its block
    /// even when the block cache did not keep it. Made by the first landing.
    landed: OnceLock<HashMap<UnitKey, Landing>>,
}

impl QueueShared {
    pub(crate) fn new(id: QueueId, bound: usize) -> Self {
        Self {
            id,
            inbox: Stack::new(),
            idle: AtomicWaker::new(),
            pending: AtomicUsize::new(0),
            bound,
            landed: OnceLock::new(),
        }
    }

    pub(crate) fn id(&self) -> QueueId {
        self.id
    }

    pub(crate) fn bound(&self) -> usize {
        self.bound
    }

    /// Push `message` to the inbox, and wake the owner when the push found it
    /// idle: `Ok(true)` then, for exactly one push per rest. `Err` hands the
    /// message back when the queue was dropped.
    pub(crate) fn deliver(&self, message: Message) -> Result<bool, Message> {
        let flags = self.inbox.push(message, SHUT)?;
        let idle = flags & IDLE != 0;
        if idle {
            self.idle.wake();
        }
        Ok(idle)
    }

    /// Take the whole inbox, oldest first, and mark the owner awake.
    pub(crate) fn take_inbox(&self) -> super::stack::Taken<Message> {
        self.inbox.take(0)
    }

    /// Take the whole inbox for good: every later push is refused.
    pub(crate) fn shut_inbox(&self) -> super::stack::Taken<Message> {
        self.inbox.take(SHUT)
    }

    pub(crate) fn inbox_is_empty(&self) -> bool {
        self.inbox.is_empty()
    }

    /// The owner is busy again: a push from now on wakes nobody. `true` when
    /// the owner was still resting, so no push woke it.
    pub(crate) fn wake_up(&self) -> bool {
        self.inbox.wake_if_resting()
    }

    /// The owner is about to idle: the next push wakes `waker`, once. When a
    /// push is already waiting, `waker` is woken now, since the owner has
    /// work.
    pub(crate) fn rest(&self, waker: &core::task::Waker) {
        self.idle.register(waker);
        match self.inbox.rest_if_empty() {
            Rest::Set | Rest::Already => {}
            Rest::Busy => waker.wake_by_ref(),
        }
    }

    /// Reserve `bytes` of reads, unless that would pass the bound while
    /// something else is pending.
    pub(crate) fn admit(&self, bytes: usize) -> bool {
        let mut pending = self.pending.load(Ordering::Acquire);
        loop {
            let after = pending.saturating_add(bytes);
            if pending != 0 && after > self.bound {
                return false;
            }
            match self
                .pending
                .compare_exchange(pending, after, Ordering::AcqRel, Ordering::Acquire)
            {
                Ok(_) => return true,
                Err(actual) => pending = actual,
            }
        }
    }

    /// Give back `bytes` a completed request reserved.
    pub(crate) fn release(&self, bytes: usize) {
        self.pending.fetch_sub(bytes, Ordering::AcqRel);
    }

    /// Bytes of reads owed now.
    pub(crate) fn pending(&self) -> usize {
        self.pending.load(Ordering::Acquire)
    }

    /// What landed for `key` on this queue, if anything. A failure is handed
    /// out once and then forgotten, so the read after it tries the device
    /// again.
    pub(crate) fn landed(&self, key: &UnitKey) -> Option<Landing> {
        let landed = self.landed.get()?;
        match landed.get(key)? {
            Landing::Failed(err) => landed
                .remove_if(
                    key,
                    |landing| matches!(landing, Landing::Failed(e) if Arc::ptr_eq(e, &err)),
                )
                .map(|_| Landing::Failed(err)),
            ready => Some(ready),
        }
    }

    /// Keep `landing` for `key` until the owner lets it go.
    pub(crate) fn land(&self, key: UnitKey, landing: Landing) {
        self.landed
            .get_or_init(|| HashMap::with_capacity(LANDED_BUCKETS))
            .insert(key, landing);
    }

    /// Let go of what landed for `key`.
    pub(crate) fn forget(&self, key: &UnitKey) {
        if let Some(landed) = self.landed.get() {
            landed.remove(key);
        }
    }
}

/// A queue is what a unit's reopen parks on the open-file table: a freed
/// slot reaches the queue's owner as a message, so the owner learns of it at
/// its next poll, or is woken for it when idle, and a busy owner never is.
impl SlotWaiter for QueueShared {
    fn slot_freed(&self) {
        // A dropped queue refuses, and its drop released its parked units.
        let _ = self.deliver(Message::SlotFreed);
    }
}

/// One waiting read: ready once its queue's owner says so, with any number
/// of tasks listening.
pub(crate) struct WaitSlot {
    /// One waker per listening `IoWait`, closed with [`SHUT`] when ready.
    wakers: Stack<Arc<AtomicWaker>>,
}

impl WaitSlot {
    pub(crate) fn new() -> Self {
        Self {
            wakers: Stack::new(),
        }
    }

    pub(crate) fn is_ready(&self) -> bool {
        self.wakers.flags() & SHUT != 0
    }

    /// Mark the read ready and wake every listener. Only the owner's `poll`
    /// (or the drop of its queue) does this.
    pub(crate) fn complete(&self) {
        for waker in self.wakers.take(SHUT) {
            waker.wake();
        }
    }

    /// Listen for readiness through `waker`. `false` when the read is already
    /// ready, and nothing was added.
    pub(crate) fn listen(&self, waker: Arc<AtomicWaker>) -> bool {
        self.wakers.push(waker, SHUT).is_ok()
    }
}

/// A queue id for tests that need one.
#[cfg(test)]
pub(crate) fn test_id() -> QueueId {
    QueueId::new(std::num::NonZeroU64::MIN)
}

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;

    #[test]
    fn admission_stops_at_the_bound_but_never_refuses_a_lone_read() {
        let queue = QueueShared::new(test_id(), 100);
        assert!(queue.admit(150), "a read larger than the bound goes alone");
        assert!(!queue.admit(1));
        queue.release(150);
        assert!(queue.admit(60));
        assert!(queue.admit(40));
        assert!(!queue.admit(1));
        queue.release(40);
        assert!(queue.admit(40));
        assert_eq!(queue.pending(), 100);
    }

    #[test]
    fn a_failure_is_handed_out_once() {
        let queue = QueueShared::new(test_id(), 100);
        let key = UnitKey {
            file_id: 1,
            offset: 0,
            guard: None,
        };
        queue.land(key, Landing::Failed(Arc::new(io::Error::other("bad"))));
        assert!(matches!(queue.landed(&key), Some(Landing::Failed(_))));
        assert!(queue.landed(&key).is_none());
    }

    #[test]
    fn a_dropped_queue_refuses_deliveries() {
        let queue = QueueShared::new(test_id(), 100);
        assert_eq!(queue.shut_inbox().count(), 0);
        let slot = Arc::new(WaitSlot::new());
        assert!(queue.deliver(Message::Room(slot)).is_err());
    }

    #[test]
    fn a_ready_slot_takes_no_more_listeners() {
        let slot = WaitSlot::new();
        assert!(!slot.is_ready());
        assert!(slot.listen(Arc::new(AtomicWaker::new())));
        slot.complete();
        assert!(slot.is_ready());
        assert!(!slot.listen(Arc::new(AtomicWaker::new())));
    }
}
