//! Token-bucket rate limiter for background I/O.
//!
//! A [`RateLimiter`] throttles byte-denominated background work (flush and
//! compaction writes) so bursts of it don't saturate the disk and push
//! foreground latency off a cliff. The engine calls [`RateLimiter::request`]
//! with a byte count before it installs what it wrote, and only on its
//! compaction worker threads: a caller's call is never throttled, whether it
//! flushes, compacts a step on its own thread, or runs a job at its queue's
//! poll (plan 4.10). Work regolith runs on a caller's thread is the caller's
//! I/O, paced by the caller.
//!
//! [`TokenBucketRateLimiter`] is the stock implementation: one token bucket
//! kept in a few atomics, with no lock and no condition variable. It is the
//! only implementation regolith ships; the trait is public so callers can
//! drop in their own (e.g. for test harnesses or a shared limiter across
//! multiple databases).

use std::cell::Cell;
use std::sync::Arc;
#[cfg(not(target_arch = "wasm32"))]
use std::time::Duration;

use crate::portability::{AtomicBool, AtomicU64, Ordering};

// The module's own tests measure real elapsed time to prove the
// limiter actually blocks.
#[cfg(test)]
use std::time::Instant;

/// Priority of a rate-limited I/O request.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Priority {
    /// Served at once: it takes its bytes from the bucket without waiting,
    /// so the requests behind it wait for them instead.
    High,
    /// Background work (flush, compaction): waits its turn.
    Low,
}

/// A byte-denominated rate limiter.
///
/// Implementations throttle callers of [`RateLimiter::request`] to at
/// most `get_bytes_per_second()` bytes over time. Requests block until
/// quota is available; shutdown (on drop or via an implementation-
/// specific `stop()` call) must release every blocked request.
///
/// regolith calls it only on its compaction worker threads, never on a
/// caller's thread, so a blocking `request` never blocks a caller.
///
/// A panic in this trait's code while a flush runs it fails that flush
/// with [`crate::Error::CallbackPanicked`]; the flush is retried as any
/// failing flush is.
pub trait RateLimiter: Send + Sync + 'static {
    /// Request `bytes` worth of I/O quota. Blocks until the request is
    /// served or the limiter is shut down.
    fn request(&self, bytes: u64, pri: Priority);

    /// Update the refill rate. Takes effect for the requests after it.
    fn set_bytes_per_second(&self, bytes_per_second: u64);

    /// Return the currently configured refill rate in bytes/sec.
    fn get_bytes_per_second(&self) -> u64;

    /// Total bytes successfully served at `pri` since construction.
    /// Excludes in-flight requests.
    fn get_total_bytes_through(&self, pri: Priority) -> u64;
}

thread_local! {
    /// The thread is a compaction worker: the only threads the engine
    /// throttles.
    static ON_WORKER: Cell<bool> = const { Cell::new(false) };
}

/// Mark the calling thread as a compaction worker for the rest of its life.
#[cfg(any(test, not(target_arch = "wasm32")))]
pub(crate) fn mark_worker_thread() {
    ON_WORKER.with(|on| on.set(true));
}

/// Throttle `bytes` of background I/O through `limiter`, on a compaction
/// worker only: the one function every engine call site uses, so no caller's
/// call is ever throttled.
///
/// The limiter is the caller's code: a panic in it fails the flush or the
/// compaction that asked, as [`crate::Error::CallbackPanicked`], instead of
/// unwinding through the worker.
pub(crate) fn throttle_background(
    limiter: Option<&Arc<dyn RateLimiter>>,
    bytes: u64,
) -> std::io::Result<()> {
    let Some(limiter) = limiter else {
        return Ok(());
    };
    if !ON_WORKER.with(Cell::get) {
        return Ok(());
    }
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        limiter.request(bytes, Priority::Low)
    }))
    .map_err(|_| {
        tracing::error!("the rate limiter panicked in background I/O");
        crate::Error::CallbackPanicked {
            callback: "RateLimiter",
            latched: false,
        }
        .into_io_error()
    })
}

/// The longest a blocked request sleeps before it checks for shutdown
/// again.
#[cfg(not(target_arch = "wasm32"))]
const SLEEP_SLICE: Duration = Duration::from_millis(50);

/// Nanoseconds `bytes` take at `rate` bytes per second, saturating.
fn nanos_for(bytes: u64, rate: u64) -> u64 {
    let nanos = u128::from(bytes).saturating_mul(1_000_000_000) / u128::from(rate.max(1));
    u64::try_from(nanos).unwrap_or(u64::MAX)
}

/// Bytes `nanos` buy at `rate` bytes per second, saturating.
fn bytes_for(nanos: u64, rate: u64) -> u64 {
    let bytes = u128::from(nanos).saturating_mul(u128::from(rate)) / 1_000_000_000;
    u64::try_from(bytes).unwrap_or(u64::MAX)
}

/// Default rate-limiter implementation: one token bucket refilled
/// continuously at `bytes_per_second`, holding at most `burst_bytes`.
///
/// The bucket is a single clock reading kept in an atomic: the time at which
/// every byte served so far will have been paid for at the rate (the
/// "theoretical arrival time" of the generic cell rate algorithm). A request
/// for `n` bytes moves it forward by `n / rate` with one compare-and-swap,
/// from now if the bucket had refilled meanwhile, and may proceed once the
/// new time is within `burst_bytes / rate` of now; until then it sleeps.
/// Reservations are taken in the order the compare-and-swaps land, so
/// requests are served first come, first served, and a request larger than
/// the burst simply waits for the bytes past it. Nobody takes a lock.
///
/// A fresh bucket is full: the first `burst_bytes` are served at once.
pub struct TokenBucketRateLimiter {
    rate: AtomicU64,
    burst_bytes: u64,
    /// Platform-clock nanoseconds at which every reserved byte is paid for.
    paid_until: AtomicU64,
    shutdown: AtomicBool,
    total_high: AtomicU64,
    total_low: AtomicU64,
}

impl TokenBucketRateLimiter {
    /// Construct a new limiter.
    ///
    /// * `bytes_per_second` - sustained refill rate. `0` disables the
    ///   limiter (every request is served instantly).
    /// * `burst_bytes` - maximum number of tokens the bucket can hold.
    ///   A fresh bucket starts full so the first `burst_bytes` worth of
    ///   work is served without blocking. Clamped to at least 1.
    ///
    /// Never panics: out-of-range arguments are clamped rather than
    /// asserted, because this is a public constructor.
    pub fn new(bytes_per_second: u64, burst_bytes: u64) -> Self {
        Self {
            rate: AtomicU64::new(bytes_per_second),
            burst_bytes: burst_bytes.max(1),
            paid_until: AtomicU64::new(0),
            shutdown: AtomicBool::new(false),
            total_high: AtomicU64::new(0),
            total_low: AtomicU64::new(0),
        }
    }

    /// Release every blocked request and return. Subsequent calls to
    /// [`RateLimiter::request`] also return immediately without
    /// consuming tokens. Called automatically when the limiter is
    /// dropped.
    pub fn stop(&self) {
        self.shutdown.store(true, Ordering::Release);
    }

    /// Reserve `bytes` at `rate`, at `now`, and return the time the request
    /// may proceed.
    fn reserve(&self, bytes: u64, rate: u64, now: u64) -> u64 {
        let cost = nanos_for(bytes, rate);
        let burst = nanos_for(self.burst_bytes, rate);
        let mut current = self.paid_until.load(Ordering::Acquire);
        loop {
            // A bucket idle long enough refilled: the debt starts now.
            let next = current.max(now).saturating_add(cost);
            match self.paid_until.compare_exchange_weak(
                current,
                next,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => return next.saturating_sub(burst),
                Err(actual) => current = actual,
            }
        }
    }

    /// Sleep until `ready_at` on the platform clock, or until stopped.
    /// `false` when stopped first.
    fn wait_until(&self, ready_at: u64) -> bool {
        loop {
            if self.shutdown.load(Ordering::Acquire) {
                return false;
            }
            let Some(now) = crate::env::platform_nanos() else {
                return true;
            };
            if now >= ready_at {
                return true;
            }
            #[cfg(not(target_arch = "wasm32"))]
            std::thread::sleep(SLEEP_SLICE.min(Duration::from_nanos(ready_at - now)));
            // A target with no thread to sleep serves at once rather than
            // spin: nothing on it calls a limiter that must block.
            #[cfg(target_arch = "wasm32")]
            return true;
        }
    }

    fn count(&self, bytes: u64, pri: Priority) {
        match pri {
            Priority::High => self.total_high.fetch_add(bytes, Ordering::Relaxed),
            Priority::Low => self.total_low.fetch_add(bytes, Ordering::Relaxed),
        };
    }
}

impl Drop for TokenBucketRateLimiter {
    fn drop(&mut self) {
        self.stop();
    }
}

impl RateLimiter for TokenBucketRateLimiter {
    fn request(&self, bytes: u64, pri: Priority) {
        if self.shutdown.load(Ordering::Acquire) {
            return;
        }
        let rate = self.rate.load(Ordering::Acquire);
        // Rate limiting is a function of elapsed time. A platform with no
        // monotonic clock cannot measure it, so the limiter serves every
        // request at once instead of blocking on a bucket that could never
        // refill; a rate of zero turns it off.
        let now = crate::env::platform_nanos();
        let (Some(now), true) = (now, rate > 0 && bytes > 0) else {
            self.count(bytes, pri);
            return;
        };
        let ready_at = self.reserve(bytes, rate, now);
        if pri == Priority::High || self.wait_until(ready_at) {
            self.count(bytes, pri);
        }
    }

    /// Change the rate. The bytes still owed are carried over at the new
    /// rate, so the change takes effect cleanly from now.
    fn set_bytes_per_second(&self, bytes_per_second: u64) {
        let old = self.rate.swap(bytes_per_second, Ordering::AcqRel);
        let (Some(now), true) = (
            crate::env::platform_nanos(),
            old > 0 && bytes_per_second > 0,
        ) else {
            return;
        };
        let mut current = self.paid_until.load(Ordering::Acquire);
        loop {
            let owed = bytes_for(current.saturating_sub(now), old);
            let next = now.saturating_add(nanos_for(owed, bytes_per_second));
            match self.paid_until.compare_exchange_weak(
                current,
                next,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => return,
                Err(actual) => current = actual,
            }
        }
    }

    fn get_bytes_per_second(&self) -> u64 {
        self.rate.load(Ordering::Acquire)
    }

    fn get_total_bytes_through(&self, pri: Priority) -> u64 {
        match pri {
            Priority::High => self.total_high.load(Ordering::Relaxed),
            Priority::Low => self.total_low.load(Ordering::Relaxed),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;
    use std::thread;

    #[test]
    fn single_request_within_burst_is_instant() {
        let lim = TokenBucketRateLimiter::new(1_000_000, 1_000_000);
        let start = Instant::now();
        lim.request(500_000, Priority::Low);
        assert!(start.elapsed() < Duration::from_millis(50));
        assert_eq!(lim.get_total_bytes_through(Priority::Low), 500_000);
    }

    #[test]
    fn ten_mb_through_one_mbps_takes_at_least_nine_seconds() {
        // The bucket starts full (1 MB burst) so a 10 MB request
        // sees 1 MB of free credit up front - expected wait is
        // ~9 seconds, not 10. Assert >= 9 to match.
        let lim = TokenBucketRateLimiter::new(1_000_000, 1_000_000);
        let start = Instant::now();
        lim.request(10_000_000, Priority::Low);
        let elapsed = start.elapsed();
        assert!(
            elapsed >= Duration::from_secs(9),
            "10 MB through 1 MB/s took {:?}, expected >= 9s",
            elapsed
        );
        assert_eq!(lim.get_total_bytes_through(Priority::Low), 10_000_000);
    }

    #[test]
    fn requests_are_served_in_the_order_they_reserved() {
        // 100 KB/s with a 10 KB burst: after the burst is drained, each
        // 10 KB waits 100 ms behind the one before it.
        let lim = Arc::new(TokenBucketRateLimiter::new(100_000, 10_000));
        lim.request(10_000, Priority::Low);
        let start = Instant::now();
        lim.request(10_000, Priority::Low);
        lim.request(10_000, Priority::Low);
        let elapsed = start.elapsed();
        assert!(
            elapsed >= Duration::from_millis(180),
            "two 10 KB requests at 100 KB/s took {elapsed:?}"
        );
    }

    #[test]
    fn high_priority_preempts_low() {
        let lim = Arc::new(TokenBucketRateLimiter::new(100_000, 10_000));
        // Drain the initial burst so every following waiter has to
        // wait for refills.
        lim.request(10_000, Priority::Low);

        let order: Arc<Mutex<Vec<&'static str>>> = Arc::new(Mutex::new(Vec::new()));

        let low_handles: Vec<_> = (0..2)
            .map(|i| {
                let lim = lim.clone();
                let order = order.clone();
                thread::spawn(move || {
                    lim.request(30_000, Priority::Low);
                    let label = if i == 0 { "lo1" } else { "lo2" };
                    order.lock().unwrap().push(label);
                })
            })
            .collect();

        // The low requests reserved first; the high one arrives after,
        // takes its bytes at once and is served first.
        thread::sleep(Duration::from_millis(30));
        let high = {
            let lim = lim.clone();
            let order = order.clone();
            thread::spawn(move || {
                lim.request(30_000, Priority::High);
                order.lock().unwrap().push("high");
            })
        };

        high.join().unwrap();
        for h in low_handles {
            h.join().unwrap();
        }

        let order = order.lock().unwrap();
        let high_idx = order.iter().position(|&s| s == "high").unwrap();
        assert!(
            high_idx < 2,
            "high did not preempt any low: order = {:?}",
            *order
        );
    }

    #[test]
    fn shutdown_releases_blocked_requests() {
        let lim = Arc::new(TokenBucketRateLimiter::new(1_000, 1_000));
        // Drain the burst so the next request has to wait ~1s per KB.
        lim.request(1_000, Priority::Low);

        let blocked = {
            let lim = lim.clone();
            thread::spawn(move || {
                let start = Instant::now();
                lim.request(60_000, Priority::Low);
                start.elapsed()
            })
        };

        thread::sleep(Duration::from_millis(100));
        lim.stop();
        let waited = blocked.join().unwrap();
        assert!(
            waited < Duration::from_secs(5),
            "blocked request was not released promptly after stop: {:?}",
            waited
        );
        assert_eq!(
            lim.get_total_bytes_through(Priority::Low),
            1_000,
            "a request released by shutdown was not served"
        );
    }

    #[test]
    fn set_bytes_per_second_live_update_is_respected() {
        let lim = Arc::new(TokenBucketRateLimiter::new(100_000, 100_000));
        lim.request(100_000, Priority::Low); // drain burst
        assert_eq!(lim.get_bytes_per_second(), 100_000);

        // Bump the rate and confirm a subsequent large request
        // completes faster than it would have at the old rate.
        lim.set_bytes_per_second(10_000_000);
        assert_eq!(lim.get_bytes_per_second(), 10_000_000);
        let start = Instant::now();
        lim.request(1_000_000, Priority::Low);
        // At the old rate 1 MB would need ~10 seconds; at 10 MB/s
        // it should need ~100 ms. Give it generous slack for CI.
        assert!(
            start.elapsed() < Duration::from_secs(2),
            "request took {:?} after rate bump",
            start.elapsed()
        );
    }

    #[test]
    fn zero_rate_disables_limiter() {
        let lim = TokenBucketRateLimiter::new(0, 1);
        let start = Instant::now();
        lim.request(100_000_000, Priority::Low);
        assert!(start.elapsed() < Duration::from_millis(50));
        assert_eq!(lim.get_total_bytes_through(Priority::Low), 100_000_000);
    }

    #[test]
    fn get_total_bytes_through_tracks_both_classes() {
        let lim = TokenBucketRateLimiter::new(10_000_000, 10_000_000);
        lim.request(1_000, Priority::High);
        lim.request(2_000, Priority::Low);
        lim.request(3_000, Priority::High);
        assert_eq!(lim.get_total_bytes_through(Priority::High), 4_000);
        assert_eq!(lim.get_total_bytes_through(Priority::Low), 2_000);
    }

    /// A limiter that serves every request at once and counts the bytes.
    #[derive(Default)]
    struct Counting(AtomicU64);

    impl RateLimiter for Counting {
        fn request(&self, bytes: u64, _: Priority) {
            self.0.fetch_add(bytes, Ordering::SeqCst);
        }
        fn set_bytes_per_second(&self, _: u64) {}
        fn get_bytes_per_second(&self) -> u64 {
            0
        }
        fn get_total_bytes_through(&self, _: Priority) -> u64 {
            self.0.load(Ordering::SeqCst)
        }
    }

    /// The engine throttles a worker thread only: a caller's thread never
    /// asks the limiter at all.
    #[test]
    fn only_a_worker_thread_is_throttled() {
        let counting = Arc::new(Counting::default());
        let limiter: Arc<dyn RateLimiter> = Arc::clone(&counting) as Arc<dyn RateLimiter>;
        throttle_background(Some(&limiter), 1_000_000).unwrap();
        assert_eq!(counting.0.load(Ordering::SeqCst), 0, "a caller asked");
        let throttled = Arc::clone(&limiter);
        thread::spawn(move || {
            mark_worker_thread();
            throttle_background(Some(&throttled), 1).unwrap();
        })
        .join()
        .unwrap();
        assert_eq!(counting.0.load(Ordering::SeqCst), 1, "the worker asked");
    }

    /// A limiter that panics fails the I/O that asked, as an error, and
    /// leaves the worker running.
    #[test]
    fn a_panicking_limiter_fails_the_request_instead_of_the_worker() {
        struct Panics;
        impl RateLimiter for Panics {
            fn request(&self, _: u64, _: Priority) {
                panic!("limiter panics");
            }
            fn set_bytes_per_second(&self, _: u64) {}
            fn get_bytes_per_second(&self) -> u64 {
                0
            }
            fn get_total_bytes_through(&self, _: Priority) -> u64 {
                0
            }
        }
        let limiter: Arc<dyn RateLimiter> = Arc::new(Panics);
        let failed = thread::spawn(move || {
            mark_worker_thread();
            throttle_background(Some(&limiter), 1)
        })
        .join()
        .expect("the panic did not unwind through the worker");
        let err = crate::Error::from(failed.unwrap_err());
        assert!(matches!(
            err,
            crate::Error::CallbackPanicked {
                callback: "RateLimiter",
                latched: false
            }
        ));
    }
}
