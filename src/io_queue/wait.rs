//! What a non-blocking read hands back instead of waiting.

use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
use std::task::{Context, Poll};

use super::QueueId;
use crate::engine::io::atomic_waker::AtomicWaker;
use crate::engine::io::shared::{QueueShared, WaitSlot};
use crate::engine::io::unit::UnitKey;

/// Why a call returned instead of waiting, and what to wait on.
///
/// Every call that would otherwise wait returns one of these at once,
/// carried by [`Error::WouldBlock`](crate::Error::WouldBlock) or
/// [`TransactionError::WouldBlock`](crate::TransactionError::WouldBlock).
/// Wait on what it holds, then run the call again.
#[derive(Clone, Debug, thiserror::Error)]
#[non_exhaustive]
pub enum WouldBlock {
    /// A `CacheOnly` read needs a block the cache does not hold. The read is
    /// recorded on the queue the handle's [`ReadMode`](crate::ReadMode)
    /// names; poll that queue, then run the read again.
    #[error("the read needs a block that is not cached; poll its I/O queue and run the read again")]
    Io(IoWait),
}

/// Names the device read an [`IoWait`] waits on. Two waits name the same
/// unit exactly when one read of the device serves them both.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct IoUnit {
    file: u64,
    offset: u64,
    guard: Option<usize>,
}

impl From<UnitKey> for IoUnit {
    fn from(key: UnitKey) -> Self {
        Self {
            file: key.file_id,
            offset: key.offset,
            guard: key.guard,
        }
    }
}

/// A wait for one `CacheOnly` read, ready once the queue it was recorded on
/// has finished the read.
///
/// It is a [`Future`] with output `()`, and is woken only by its own queue's
/// [`IoQueue::poll`](crate::IoQueue::poll), on the thread that owns the
/// queue: a task that awaits it resumes once that thread polls. Ready means
/// the read can be run again; it does not mean the read will now succeed (the
/// database may have closed, or the block may have failed its checksum, which
/// the read run again reports).
///
/// A clone waits on the same read and is woken with it; each clone is woken
/// through its own registration, so several tasks may await clones at once.
/// Dropping a wait never cancels the read: the queue completes it all the
/// same.
pub struct IoWait {
    slot: Arc<WaitSlot>,
    /// This wait's own registration on `slot`, made by its first pending
    /// poll and reused after.
    listener: Option<Arc<AtomicWaker>>,
    queue: QueueId,
    unit: Option<IoUnit>,
}

impl IoWait {
    /// A wait on `slot`, recorded on `queue` for `unit` (`None` for a wait for
    /// room in the queue's byte bound).
    pub(crate) fn new(queue: &QueueShared, unit: Option<UnitKey>, slot: Arc<WaitSlot>) -> Self {
        Self {
            slot,
            listener: None,
            queue: queue.id(),
            unit: unit.map(IoUnit::from),
        }
    }

    /// The queue this wait was recorded on: the only one whose poll makes it
    /// ready.
    pub fn queue(&self) -> QueueId {
        self.queue
    }

    /// The device read this wait waits on. `None` for a read that found its
    /// queue's byte bound full: it waits until the queue owes less, and then
    /// records its read when it is run again.
    pub fn unit(&self) -> Option<IoUnit> {
        self.unit
    }

    /// Whether the queue finished this read. Never waits.
    pub fn is_ready(&self) -> bool {
        self.slot.is_ready()
    }

    /// This wait as the `io::Error` the engine's read paths carry it in; the
    /// public error types take it back out by value.
    pub(crate) fn into_io_error(self) -> std::io::Error {
        std::io::Error::new(std::io::ErrorKind::WouldBlock, WouldBlock::Io(self))
    }
}

impl Clone for IoWait {
    fn clone(&self) -> Self {
        Self {
            slot: Arc::clone(&self.slot),
            listener: None,
            queue: self.queue,
            unit: self.unit,
        }
    }
}

impl std::fmt::Debug for IoWait {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("IoWait")
            .field("queue", &self.queue)
            .field("unit", &self.unit)
            .field("ready", &self.is_ready())
            .finish()
    }
}

impl Future for IoWait {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        let this = self.get_mut();
        if this.slot.is_ready() {
            return Poll::Ready(());
        }
        match &this.listener {
            Some(listener) => listener.register(cx.waker()),
            None => {
                let listener = Arc::new(AtomicWaker::new());
                listener.register(cx.waker());
                // Refused only when the read is ready already.
                if !this.slot.listen(Arc::clone(&listener)) {
                    return Poll::Ready(());
                }
                this.listener = Some(listener);
            }
        }
        // The queue may have completed the read between the check above and
        // the registration: it then woke the old waker or none, so look again.
        if this.slot.is_ready() {
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    }
}

/// Whether `err` carries a [`WouldBlock`].
pub(crate) fn is_would_block(err: &std::io::Error) -> bool {
    err.kind() == std::io::ErrorKind::WouldBlock
        && err.get_ref().is_some_and(|inner| inner.is::<WouldBlock>())
}

/// The [`WouldBlock`] `err` carries, taken out by value, or `err` back.
pub(crate) fn take_would_block(err: std::io::Error) -> Result<WouldBlock, std::io::Error> {
    if !is_would_block(&err) {
        return Err(err);
    }
    match err.into_inner().map(|inner| inner.downcast::<WouldBlock>()) {
        Some(Ok(would_block)) => Ok(*would_block),
        Some(Err(inner)) => Err(std::io::Error::new(std::io::ErrorKind::WouldBlock, inner)),
        None => Err(std::io::Error::from(std::io::ErrorKind::WouldBlock)),
    }
}

/// A copy of the [`WouldBlock`] `err` carries: a clone of its wait.
pub(crate) fn copy_would_block(err: &std::io::Error) -> Option<WouldBlock> {
    if err.kind() != std::io::ErrorKind::WouldBlock {
        return None;
    }
    err.get_ref()?.downcast_ref::<WouldBlock>().cloned()
}
