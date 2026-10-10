//! How a handle's [`ReadMode`](crate::ReadMode) reaches the device seam.
//!
//! A `CacheOnly` handle names a queue, and every read path below it has to
//! know that at the one place it would touch the device: the four block
//! reads of `SsTableReader` and the scan readahead. Those sit far below the
//! handle, behind every read path's own signatures, so the mode travels in a
//! thread-local set for the length of one call instead of as a parameter.
//!
//! That is exact because a read call runs synchronously on the thread that
//! made it: nothing between the handle and the seam hands work to another
//! thread, and a scope ends (on return or unwind) before the call does. A
//! `Blocking` handle sets nothing, so the default path costs nothing at all:
//! the seam reads the thread-local only after the block cache missed, where
//! a device read would cost far more than the read of one word.
//!
//! [`unit_run`] clears the mode for the stretch a unit run by
//! `IoQueue::poll` reads the device, whoever calls it, and marks that
//! stretch as one that may not wait for an open-file slot (D60): a reopen
//! under `max_open_files` that finds every slot busy parks on the queue
//! running the unit instead, and the run sees that it did.

use std::cell::{Cell, RefCell};
use std::num::NonZeroU64;
use std::sync::Arc;

use super::shared::QueueShared;
use crate::env::open_file_limit::slots::SlotWaiter;
use crate::io_queue::QueueId;

thread_local! {
    /// The queue misses go to on this thread right now; `0` is `Blocking`.
    static QUEUE: Cell<u64> = const { Cell::new(0) };
    /// The queue whose unit this thread is running, while it runs one.
    static RUNNING: RefCell<Option<Running>> = const { RefCell::new(None) };
}

/// A unit run in progress on this thread.
struct Running {
    queue: Arc<QueueShared>,
    /// A reopen in this run found every open-file slot busy and parked.
    parked: bool,
}

/// A mode set on this thread until it is dropped, which restores the one
/// before it.
#[must_use = "the mode holds only while the scope is alive"]
pub(crate) struct Scope {
    previous: u64,
}

impl Drop for Scope {
    fn drop(&mut self) {
        QUEUE.with(|queue| queue.set(self.previous));
    }
}

/// Send this thread's device misses to queue `id` until the scope drops.
pub(crate) fn cache_only(id: QueueId) -> Scope {
    Scope {
        previous: QUEUE.with(|queue| queue.replace(id.get())),
    }
}

/// The queue this thread's misses go to, or `None` when it may read the
/// device. The seam calls this only after the block cache missed.
pub(crate) fn current() -> Option<QueueId> {
    NonZeroU64::new(QUEUE.with(Cell::get)).map(QueueId::new)
}

/// The run of one unit on this thread, from [`unit_run`]: the device may be
/// read, but no slot may be waited for.
#[must_use = "the run holds only while the scope is alive"]
pub(crate) struct UnitRun {
    _device: Scope,
    previous: Option<Running>,
}

impl UnitRun {
    /// Whether a reopen in this run parked instead of reading.
    pub(crate) fn parked(&self) -> bool {
        RUNNING.with(|running| running.borrow().as_ref().is_some_and(|run| run.parked))
    }
}

impl Drop for UnitRun {
    fn drop(&mut self) {
        RUNNING.with(|running| *running.borrow_mut() = self.previous.take());
    }
}

/// Run a unit of `queue`'s on this thread until the scope drops: read the
/// device, and park a reopen that finds no open-file slot on `queue`.
pub(crate) fn unit_run(queue: &Arc<QueueShared>) -> UnitRun {
    let device = Scope {
        previous: QUEUE.with(|queue| queue.replace(0)),
    };
    let run = Running {
        queue: Arc::clone(queue),
        parked: false,
    };
    UnitRun {
        _device: device,
        previous: RUNNING.with(|running| running.borrow_mut().replace(run)),
    }
}

/// Who a reopen on this thread parks, when it may not wait for a slot: the
/// queue whose unit runs here. `None` outside a unit run, where the reopen
/// belongs to a `Blocking` read and may wait.
pub(crate) fn reopen_waiter() -> Option<Arc<dyn SlotWaiter>> {
    RUNNING.with(|running| {
        running
            .borrow()
            .as_ref()
            .map(|run| Arc::clone(&run.queue) as Arc<dyn SlotWaiter>)
    })
}

/// A reopen in the unit run on this thread parked.
pub(crate) fn note_parked() {
    RUNNING.with(|running| {
        if let Some(run) = running.borrow_mut().as_mut() {
            run.parked = true;
        }
    });
}

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;
    use crate::engine::io::shared::test_id;

    fn id(n: u64) -> QueueId {
        QueueId::new(NonZeroU64::new(n).unwrap())
    }

    fn queue() -> Arc<QueueShared> {
        Arc::new(QueueShared::new(test_id(), 1 << 20))
    }

    #[test]
    fn scopes_nest_and_restore_what_they_replaced() {
        assert_eq!(current(), None);
        {
            let _outer = cache_only(id(7));
            assert_eq!(current(), Some(id(7)));
            {
                let _inner = unit_run(&queue());
                assert_eq!(current(), None);
            }
            assert_eq!(current(), Some(id(7)));
        }
        assert_eq!(current(), None);
    }

    #[test]
    fn an_unwind_restores_the_mode() {
        let caught = std::panic::catch_unwind(|| {
            let _scope = cache_only(id(3));
            let _run = unit_run(&queue());
            panic!("unwind through the scope");
        });
        assert!(caught.is_err());
        assert_eq!(current(), None);
        assert!(reopen_waiter().is_none());
    }

    #[test]
    fn the_mode_is_per_thread() {
        let _scope = cache_only(id(9));
        let _run = unit_run(&queue());
        std::thread::spawn(|| {
            assert_eq!(current(), None);
            assert!(reopen_waiter().is_none());
        })
        .join()
        .unwrap();
        assert!(reopen_waiter().is_some());
    }

    #[test]
    fn only_a_unit_run_parks_a_reopen_and_sees_that_it_did() {
        assert!(reopen_waiter().is_none(), "a Blocking read may wait");
        note_parked();
        let run = unit_run(&queue());
        assert!(reopen_waiter().is_some());
        assert!(!run.parked());
        note_parked();
        assert!(run.parked());
        drop(run);
        assert!(reopen_waiter().is_none());
        // A new run starts unparked.
        assert!(!unit_run(&queue()).parked());
    }
}
