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
//! [`blocking`] clears the mode for a stretch that must read the device, a
//! unit run by `IoQueue::poll` in particular, whoever calls it.

use std::cell::Cell;
use std::num::NonZeroU64;

use crate::io_queue::QueueId;

thread_local! {
    /// The queue misses go to on this thread right now; `0` is `Blocking`.
    static QUEUE: Cell<u64> = const { Cell::new(0) };
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

/// Let this thread read the device until the scope drops.
pub(crate) fn blocking() -> Scope {
    Scope {
        previous: QUEUE.with(|queue| queue.replace(0)),
    }
}

/// The queue this thread's misses go to, or `None` when it may read the
/// device. The seam calls this only after the block cache missed.
pub(crate) fn current() -> Option<QueueId> {
    NonZeroU64::new(QUEUE.with(Cell::get)).map(QueueId::new)
}

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;

    fn id(n: u64) -> QueueId {
        QueueId::new(NonZeroU64::new(n).unwrap())
    }

    #[test]
    fn scopes_nest_and_restore_what_they_replaced() {
        assert_eq!(current(), None);
        {
            let _outer = cache_only(id(7));
            assert_eq!(current(), Some(id(7)));
            {
                let _inner = blocking();
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
            panic!("unwind through the scope");
        });
        assert!(caught.is_err());
        assert_eq!(current(), None);
    }

    #[test]
    fn the_mode_is_per_thread() {
        let _scope = cache_only(id(9));
        std::thread::spawn(|| assert_eq!(current(), None))
            .join()
            .unwrap();
        assert_eq!(current(), Some(id(9)));
    }
}
