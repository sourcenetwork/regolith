//! Tracks the sequence numbers of every live `Snapshot` handed out by
//! the engine so that compaction can decide which older versions of a
//! user key are safe to drop.
//!
//! # Pin semantics
//!
//! Every call to [`Db::snapshot`](crate::Db::snapshot) registers a
//! sequence number, and the corresponding [`Snapshot`](crate::Snapshot)
//! releases it on drop. Multiple snapshots can pin the same seq; the
//! registry keeps a refcount per seq and removes the entry when the
//! refcount reaches zero.
//!
//! [`SnapshotRegistry::oldest_live_seq`] returns the smallest currently
//! registered seq - or `u64::MAX` when no snapshot is live. Compaction
//! uses this as the **pin seq**: any version with a smaller seq than
//! the largest visible version at `pin_seq` is invisible to every
//! live snapshot and to current reads, and can be discarded.

use std::collections::BTreeMap;
use std::sync::Arc;

use crate::sync::{AtomicUsize, Condvar, Mutex, Ordering};

use crate::env::Env;

/// Thread-safe registry of live snapshot sequence numbers.
pub(crate) struct SnapshotRegistry {
    /// `seq -> (refcount, earliest_register_unix)`. `BTreeMap`
    /// keeps the smallest seq at the front so `oldest_live_seq`
    /// is O(log n). `earliest_register_unix` is captured on the
    /// first `register` call at a given seq and reused by
    /// subsequent increments so the property
    /// `regolith.oldest-snapshot-time` is stable across refcount
    /// changes.
    active: Mutex<BTreeMap<u64, SlotState>>,
    /// Signalled when the last pin is released and somebody is waiting for
    /// that, so a caller shutting the database down can wait for readers
    /// to finish instead of polling a counter.
    drained: Condvar,
    /// Threads inside [`Self::wait_until_drained`]. A release that empties
    /// the map wakes the condvar only when this is nonzero: std's futex
    /// condvar issues the wake syscall unconditionally, and in single-writer
    /// use the map empties on every commit.
    ///
    /// No wake is lost. A waiter raises the count before it takes the
    /// registry mutex and checks the map; a releaser reads the count after
    /// it has dropped the mutex. If the waiter found a pin and parked, the
    /// release that removes the last pin enters the mutex after the
    /// waiter's critical section left it, so the increment happens-before
    /// the releaser's load and the wake is issued. If the release emptied
    /// the map before the waiter's check, the waiter sees the empty map and
    /// returns without parking. The only wake skipped is one nobody would
    /// have received.
    waiters: AtomicUsize,
    /// Wakes actually issued. Test-only: it is how a test proves the
    /// no-waiter path issued none and the waiter path issued one.
    #[cfg(test)]
    wakes: AtomicUsize,
    env: Arc<dyn Env>,
}

#[derive(Debug, Clone, Copy)]
struct SlotState {
    refcount: usize,
    /// `None` on a platform with no wall clock. The
    /// `regolith.oldest-snapshot-time` property then reports the
    /// timestamp as absent rather than as the epoch.
    registered_at_unix: Option<u64>,
}

impl SnapshotRegistry {
    /// A registry whose timestamps come from `env`.
    pub(crate) fn with_env(env: Arc<dyn Env>) -> Self {
        Self {
            active: Mutex::new(BTreeMap::new()),
            drained: Condvar::new(),
            waiters: AtomicUsize::new(0),
            #[cfg(test)]
            wakes: AtomicUsize::new(0),
            env,
        }
    }

    /// A registry timed by the standard environment.
    #[cfg(test)]
    pub(crate) fn new() -> Self {
        Self::with_env(crate::env::std_env())
    }

    /// Register a new pin at `seq`. Must be balanced by a later
    /// [`release`](Self::release) call - typically from the
    /// `Drop` impl of the owning snapshot type.
    pub(crate) fn register(&self, seq: u64) {
        let now = self.env.unix_secs();
        let mut active = self.active.lock();
        active
            .entry(seq)
            .or_insert(SlotState {
                refcount: 0,
                registered_at_unix: now,
            })
            .refcount += 1;
    }

    /// Register a pin at the sequence `sample` returns, reading that
    /// sequence while the registry mutex is held.
    ///
    /// Sampling the read horizon and registering the pin have to be one
    /// step. If they are two, a compaction that reads
    /// [`oldest_live_seq`](Self::oldest_live_seq) in between sees no
    /// pin at all, computes its GC horizon as `u64::MAX`, and is free
    /// to drop the very version the new snapshot was about to read.
    pub(crate) fn register_at(&self, sample: impl FnOnce() -> u64) -> u64 {
        // Through the env: a target without a wall clock reports none
        // rather than panicking, and the age is simply unknown there.
        let now = self.env.unix_secs();
        let mut active = self.active.lock();
        let seq = sample();
        active
            .entry(seq)
            .or_insert(SlotState {
                refcount: 0,
                registered_at_unix: now,
            })
            .refcount += 1;
        seq
    }

    /// Release one pin at `seq`. A no-op if no pin at that seq is
    /// currently registered, which should only happen in test
    /// teardown races.
    pub(crate) fn release(&self, seq: u64) {
        let mut active = self.active.lock();
        if let Some(slot) = active.get_mut(&seq) {
            slot.refcount -= 1;
            if slot.refcount == 0 {
                active.remove(&seq);
            }
        }
        let empty = active.is_empty();
        drop(active);
        if empty && self.waiters.load(Ordering::Acquire) > 0 {
            #[cfg(test)]
            self.wakes.fetch_add(1, Ordering::Relaxed);
            self.drained.notify_all();
        }
    }

    /// Block until no snapshot is pinned, or until `timeout` elapses.
    ///
    /// Returns the number of pins still live, so `0` means the wait
    /// succeeded and anything else is what was still outstanding when
    /// the deadline passed. The caller decides whether that is an error.
    ///
    /// A condition variable rather than a counter the caller polls: a
    /// poll picks an interval, and every interval is wrong somewhere.
    /// Too short burns a core during a shutdown that is waiting on a
    /// long scan; too long adds its own latency to every clean
    /// shutdown. Waiting on the release itself has neither cost.
    pub(crate) fn wait_until_drained(&self, timeout: std::time::Duration) -> u64 {
        self.waiters.fetch_add(1, Ordering::AcqRel);
        let deadline = std::time::Instant::now() + timeout;
        let mut active = self.active.lock();
        while !active.is_empty() {
            let Some(remaining) = deadline.checked_duration_since(std::time::Instant::now()) else {
                break;
            };
            let (next, _) = self
                .drained
                .wait_timeout(active, remaining)
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            active = next;
        }
        self.waiters.fetch_sub(1, Ordering::AcqRel);
        active.values().map(|slot| slot.refcount as u64).sum()
    }

    /// Return the smallest currently registered seq, or `u64::MAX`
    /// if no snapshot is live. Compaction uses this as its GC
    /// horizon: entries older than the largest version visible to
    /// this seq are safe to drop.
    pub(crate) fn oldest_live_seq(&self) -> u64 {
        self.active
            .lock()
            .keys()
            .next()
            .copied()
            .unwrap_or(u64::MAX)
    }

    /// Number of distinct live snapshots. Counts pins, not
    /// distinct seqs - two snapshots taken at the same seq
    /// contribute two.
    pub(crate) fn live_count(&self) -> u64 {
        self.active
            .lock()
            .values()
            .map(|slot| slot.refcount as u64)
            .sum()
    }

    /// Unix-seconds timestamp when the oldest currently-live
    /// snapshot was registered.
    ///
    /// `None` when no snapshot is alive, and also `None` when the
    /// environment has no wall clock: regolith reports "not known"
    /// rather than inventing an epoch timestamp. Used to populate
    /// the `regolith.oldest-snapshot-time` property.
    pub(crate) fn oldest_snapshot_time_unix(&self) -> Option<u64> {
        self.active
            .lock()
            .values()
            .next()
            .and_then(|slot| slot.registered_at_unix)
    }

    /// Test-only: number of distinct seq values currently pinned.
    #[cfg(test)]
    pub(crate) fn pin_count(&self) -> usize {
        self.active.lock().len()
    }

    /// Test-only: threads currently inside `wait_until_drained`.
    #[cfg(test)]
    pub(crate) fn waiting(&self) -> usize {
        self.waiters.load(Ordering::Acquire)
    }

    /// Test-only: condvar wakes issued so far.
    #[cfg(test)]
    pub(crate) fn wakes_issued(&self) -> usize {
        self.wakes.load(Ordering::Relaxed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn register_release_refcounts_correctly() {
        let r = SnapshotRegistry::new();
        assert_eq!(r.oldest_live_seq(), u64::MAX);
        assert_eq!(r.pin_count(), 0);

        r.register(10);
        r.register(10);
        r.register(5);
        r.register(20);

        assert_eq!(r.oldest_live_seq(), 5);
        assert_eq!(r.pin_count(), 3);

        r.release(5);
        assert_eq!(r.oldest_live_seq(), 10);
        assert_eq!(r.pin_count(), 2);

        r.release(10);
        // Second pin at 10 still alive.
        assert_eq!(r.oldest_live_seq(), 10);
        assert_eq!(r.pin_count(), 2);

        r.release(10);
        assert_eq!(r.oldest_live_seq(), 20);
        assert_eq!(r.pin_count(), 1);

        r.release(20);
        assert_eq!(r.oldest_live_seq(), u64::MAX);
        assert_eq!(r.pin_count(), 0);
    }

    #[test]
    fn release_unknown_seq_is_noop() {
        let r = SnapshotRegistry::new();
        r.release(42);
        assert_eq!(r.oldest_live_seq(), u64::MAX);
    }

    #[test]
    fn live_count_tracks_refcount_total_not_distinct_seqs() {
        let r = SnapshotRegistry::new();
        r.register(5);
        r.register(5);
        r.register(9);
        assert_eq!(r.live_count(), 3);
        assert_eq!(r.pin_count(), 2);
        r.release(5);
        assert_eq!(r.live_count(), 2);
    }

    #[test]
    fn oldest_snapshot_time_is_none_when_empty_and_some_when_pinned() {
        let r = SnapshotRegistry::new();
        assert!(r.oldest_snapshot_time_unix().is_none());
        r.register(7);
        assert!(r.oldest_snapshot_time_unix().is_some());
        r.release(7);
        assert!(r.oldest_snapshot_time_unix().is_none());
    }

    #[test]
    fn concurrent_register_release_stays_consistent() {
        use std::sync::Arc;
        use std::thread;
        let r = Arc::new(SnapshotRegistry::new());
        let mut handles = Vec::new();
        for worker in 0..4u64 {
            let r = Arc::clone(&r);
            handles.push(thread::spawn(move || {
                for i in 0..200u64 {
                    let seq = worker * 200 + i + 1;
                    r.register(seq);
                    r.release(seq);
                }
            }));
        }
        for h in handles {
            h.join().unwrap();
        }
        assert_eq!(r.pin_count(), 0);
        assert_eq!(r.live_count(), 0);
        assert_eq!(r.oldest_live_seq(), u64::MAX);
    }

    #[test]
    fn release_wakes_a_registered_waiter() {
        use std::sync::Arc;
        use std::thread;

        let r = Arc::new(SnapshotRegistry::new());
        r.register(7);

        thread::scope(|scope| {
            let waiter = {
                let r = Arc::clone(&r);
                scope.spawn(move || {
                    let started = std::time::Instant::now();
                    let remaining = r.wait_until_drained(std::time::Duration::from_secs(60));
                    (remaining, started.elapsed())
                })
            };

            let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
            while r.waiting() == 0 {
                assert!(
                    std::time::Instant::now() < deadline,
                    "waiter never registered itself"
                );
                thread::yield_now();
            }
            r.release(7);

            let (remaining, elapsed) = waiter.join().expect("waiter thread");
            assert_eq!(remaining, 0, "the release must drain the last pin");
            assert_eq!(r.wakes_issued(), 1);
            assert!(
                elapsed < std::time::Duration::from_secs(20),
                "a missed wake would only return at the 60s timeout, took {elapsed:?}"
            );
        });
    }

    #[test]
    fn release_with_nobody_waiting_issues_no_wake() {
        let r = SnapshotRegistry::new();
        r.register(1);
        r.release(1);
        assert_eq!(r.wakes_issued(), 0);

        r.register(2);
        r.register(3);
        r.release(2);
        r.release(3);
        assert_eq!(r.wakes_issued(), 0);
    }

    #[test]
    fn a_waiter_leaves_no_count_behind() {
        let r = SnapshotRegistry::new();
        r.register(3);
        assert_eq!(
            r.wait_until_drained(std::time::Duration::from_millis(10)),
            1,
            "the pin is still live, so the wait must time out rather than drain"
        );
        assert_eq!(r.waiting(), 0);

        r.release(3);
        assert_eq!(r.wait_until_drained(std::time::Duration::from_secs(1)), 0);
        assert_eq!(r.waiting(), 0);
    }
}
