//! Engine-wide counters and histograms for observability.
//!
//! A caller configures [`crate::Options::statistics`] with an
//! [`Arc<Statistics>`] and the engine increments tickers and
//! records histograms on every hot path it has instrumented. The
//! caller then polls the `Statistics` object (via
//! [`Statistics::get_ticker`], [`Statistics::get_histogram_snapshot`],
//! or [`Statistics::to_string`]) to export the values to their
//! monitoring stack of choice.
//!
//! # Metric names
//!
//! Every ticker and histogram exports a stable string name of the
//! form `regolith.<surface>.<metric>`, grouping related metrics
//! under a shared surface prefix. The surfaces are `write`
//! (memtable/batch writes), `read` (point lookups), `iter`
//! (iterator seek/next), `block_cache`, `bloom`, `compaction`,
//! `flush`, `wal`, `snapshot`, `commit` (transaction commit
//! outcomes), and `policy` ([`IsolationLevel::DefraLevel`]
//! relaxations).
//!
//! # Cost when disabled
//!
//! `Options::statistics = None` short-circuits every instrumentation
//! site behind an `Option::is_some` check plus an `Arc` clone at
//! open time. The hot-path overhead is a single branch. Reaching
//! for a non-`None` statistics object adds one `fetch_add` per
//! ticker update and a short mutex for histogram updates.
//!
//! # Histograms
//!
//! The initial histogram implementation tracks `count`, `sum`,
//! `min`, and `max` only. `HistogramSnapshot::average` gives you
//! `sum / count`. Percentiles / buckets are intentionally out of
//! scope for v1 - adding an HDR-style bucket array is a follow-up
//! that drops in behind the existing API without breaking
//! callers.

use crate::portability::{AtomicU64, Ordering};

/// Enumerated counters incremented by the engine. Every variant
/// is backed by one `AtomicU64` slot in [`Statistics`]; looking
/// up a ticker is `O(1)` and thread-safe.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(usize)]
#[non_exhaustive]
pub enum Ticker {
    /// Total key + value bytes written to the memtable. Counts
    /// raw user bytes; does not include internal encoding
    /// overhead, the CF prefix, or WAL framing.
    BytesWritten = 0,
    /// Total value bytes returned from point lookups that found
    /// a live value.
    BytesRead = 1,
    /// Number of successful `put` operations routed through
    /// `apply_batch`.
    KeysWritten = 2,
    /// Number of `get` calls (including lookups that returned
    /// `None`).
    KeysRead = 3,
    /// Number of `delete` operations.
    KeysDeleted = 4,
    /// Number of range-delete operations.
    RangeDeletesWritten = 5,
    /// Number of merge operands written.
    MergesWritten = 6,
    /// Block cache hits (the block was already resident).
    BlockCacheHit = 7,
    /// Block cache misses (the block had to be fetched from disk).
    BlockCacheMiss = 8,
    /// Block cache insertions (one per miss that actually
    /// populated the cache).
    BlockCacheAdd = 9,
    /// Bloom-filter "useful" hits - the filter correctly
    /// answered "not present" and spared a block read.
    BloomFilterUseful = 10,
    /// Bloom-filter "full positive" hits - the filter said
    /// "maybe", and the key was actually present in the block.
    BloomFilterFullPositive = 11,
    /// Bytes read by compaction (sum of input file sizes).
    CompactionBytesRead = 12,
    /// Bytes written by compaction (sum of output file sizes).
    CompactionBytesWritten = 13,
    /// Number of compaction jobs that have run.
    CompactionCount = 14,
    /// Bytes written by the flush path (output SSTable size).
    FlushBytesWritten = 15,
    /// Number of memtable → L0 flushes.
    FlushCount = 16,
    /// Bytes appended to the WAL.
    WalBytesWritten = 17,
    /// Number of `Wal::sync` calls.
    WalSyncCount = 18,
    /// Number of `Iter::seek` / `Iter::seek_to_first` / etc.
    IterSeekCount = 19,
    /// Number of `Iter::next` calls that produced a key.
    IterNextCount = 20,
    /// Microseconds writers spent in write-stall waits that admitted the
    /// write: plain writes and transactional commits that carry writes
    /// alike. A wait that ends in a busy or closed error is not counted.
    WriteStallMicros = 21,
    /// Number of snapshots registered via `Db::snapshot`.
    SnapshotsRegistered = 22,
    /// Number of snapshots released (dropped or explicitly
    /// released).
    SnapshotsReleased = 23,
    /// Number of incomplete trailing WAL records discarded during
    /// recovery. A non-zero value means a crash left a partly written
    /// record behind and the bytes from it to end-of-file were dropped;
    /// the discard is also logged with the file and the offset.
    WalTailDiscarded = 24,
    /// Optimistic or pessimistic transaction commits that returned
    /// `Ok`.
    CommitCount = 25,
    /// Transaction commits that returned
    /// [`crate::TransactionError::Conflict`].
    CommitConflicts = 26,
    /// The subset of [`Ticker::CommitConflicts`] where the
    /// conflicting key was a key the transaction read.
    CommitConflictsOnRead = 27,
    /// The subset of [`Ticker::CommitConflicts`] where the
    /// conflicting key was a key the transaction wrote or merged
    /// into.
    CommitConflictsOnWrite = 28,
    /// Written keys whose newer committed version was accepted
    /// because the write stored exactly what the key already holds.
    /// Counted only for commits that returned `Ok`.
    CommitWritesElided = 29,
    /// Blind merge-only keys accepted at
    /// [`crate::IsolationLevel::DefraLevel`] despite a newer merge
    /// operand, because operands commute. Counted only for commits
    /// that returned `Ok`.
    PolicyBlindMergesCommuted = 30,
    /// Scan stretches dropped because they stayed inside a
    /// [`crate::KeyClass::CommutativePrefix`], so the caller's
    /// policy declared them safe to leave unvalidated. Counted only
    /// for commits that returned `Ok`.
    PolicyScanRunsDropped = 31,
}

const NUM_TICKERS: usize = 32;

/// Every defined ticker, in discriminant order. Used by
/// [`Statistics::dump`] to iterate all slots. Keep this in sync
/// with the [`Ticker`] enum - adding a variant without
/// appending here will silently drop it from the dump output.
const ALL_TICKERS: &[Ticker] = &[
    Ticker::BytesWritten,
    Ticker::BytesRead,
    Ticker::KeysWritten,
    Ticker::KeysRead,
    Ticker::KeysDeleted,
    Ticker::RangeDeletesWritten,
    Ticker::MergesWritten,
    Ticker::BlockCacheHit,
    Ticker::BlockCacheMiss,
    Ticker::BlockCacheAdd,
    Ticker::BloomFilterUseful,
    Ticker::BloomFilterFullPositive,
    Ticker::CompactionBytesRead,
    Ticker::CompactionBytesWritten,
    Ticker::CompactionCount,
    Ticker::FlushBytesWritten,
    Ticker::FlushCount,
    Ticker::WalBytesWritten,
    Ticker::WalSyncCount,
    Ticker::IterSeekCount,
    Ticker::IterNextCount,
    Ticker::WriteStallMicros,
    Ticker::SnapshotsRegistered,
    Ticker::SnapshotsReleased,
    Ticker::WalTailDiscarded,
    Ticker::CommitCount,
    Ticker::CommitConflicts,
    Ticker::CommitConflictsOnRead,
    Ticker::CommitConflictsOnWrite,
    Ticker::CommitWritesElided,
    Ticker::PolicyBlindMergesCommuted,
    Ticker::PolicyScanRunsDropped,
];

impl Ticker {
    /// Stable string name for exporting to monitoring systems.
    pub fn name(&self) -> &'static str {
        match self {
            Ticker::BytesWritten => "regolith.write.bytes",
            Ticker::BytesRead => "regolith.read.bytes",
            Ticker::KeysWritten => "regolith.write.keys",
            Ticker::KeysRead => "regolith.read.keys",
            Ticker::KeysDeleted => "regolith.write.deletes",
            Ticker::RangeDeletesWritten => "regolith.write.range_deletes",
            Ticker::MergesWritten => "regolith.write.merges",
            Ticker::BlockCacheHit => "regolith.block_cache.hit",
            Ticker::BlockCacheMiss => "regolith.block_cache.miss",
            Ticker::BlockCacheAdd => "regolith.block_cache.add",
            Ticker::BloomFilterUseful => "regolith.bloom.useful",
            Ticker::BloomFilterFullPositive => "regolith.bloom.full_positive",
            Ticker::CompactionBytesRead => "regolith.compaction.bytes_read",
            Ticker::CompactionBytesWritten => "regolith.compaction.bytes_written",
            Ticker::CompactionCount => "regolith.compaction.count",
            Ticker::FlushBytesWritten => "regolith.flush.bytes_written",
            Ticker::FlushCount => "regolith.flush.count",
            Ticker::WalBytesWritten => "regolith.wal.bytes_written",
            Ticker::WalSyncCount => "regolith.wal.sync_count",
            Ticker::IterSeekCount => "regolith.iter.seek_count",
            Ticker::IterNextCount => "regolith.iter.next_count",
            Ticker::WriteStallMicros => "regolith.write.stall_micros",
            Ticker::SnapshotsRegistered => "regolith.snapshot.registered",
            Ticker::SnapshotsReleased => "regolith.snapshot.released",
            Ticker::WalTailDiscarded => "regolith.wal.tail_discarded",
            Ticker::CommitCount => "regolith.commit.count",
            Ticker::CommitConflicts => "regolith.commit.conflicts",
            Ticker::CommitConflictsOnRead => "regolith.commit.conflicts_on_read",
            Ticker::CommitConflictsOnWrite => "regolith.commit.conflicts_on_write",
            Ticker::CommitWritesElided => "regolith.commit.writes_elided",
            Ticker::PolicyBlindMergesCommuted => "regolith.policy.blind_merges_commuted",
            Ticker::PolicyScanRunsDropped => "regolith.policy.scan_runs_dropped",
        }
    }
}

/// Enumerated histograms recorded by the engine. Every variant
/// is backed by one histogram slot in [`Statistics`], guarded
/// by its own short mutex so recording is non-contending
/// across histograms.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(usize)]
#[non_exhaustive]
pub enum Histogram {
    /// Wall-clock microseconds per `Db::get` call.
    DbGet = 0,
    /// Wall-clock microseconds per `Db::write` / `apply_batch`.
    DbWrite = 1,
    /// Wall-clock microseconds per `Iter::seek*` call.
    DbIterSeek = 2,
    /// Wall-clock microseconds per `Iter::next` call that
    /// produced a key.
    DbIterNext = 3,
    /// Wall-clock microseconds per compaction job.
    CompactionTime = 4,
    /// Wall-clock microseconds per flush.
    FlushTime = 5,
    /// Bytes returned per `Db::get` that found a live value.
    BytesPerRead = 6,
    /// Total bytes applied per `Db::write` (keys + values across
    /// every op in the batch).
    BytesPerWrite = 7,
    /// Wall-clock microseconds to append a batch to the WAL
    /// (including fsync when durability is Immediate).
    WalWriteTime = 8,
}

const NUM_HISTOGRAMS: usize = 9;

/// Every defined histogram, in discriminant order. Same pattern
/// as [`ALL_TICKERS`].
const ALL_HISTOGRAMS: &[Histogram] = &[
    Histogram::DbGet,
    Histogram::DbWrite,
    Histogram::DbIterSeek,
    Histogram::DbIterNext,
    Histogram::CompactionTime,
    Histogram::FlushTime,
    Histogram::BytesPerRead,
    Histogram::BytesPerWrite,
    Histogram::WalWriteTime,
];

impl Histogram {
    /// Stable string name for exporting to monitoring systems.
    pub fn name(&self) -> &'static str {
        match self {
            Histogram::DbGet => "regolith.read.get_micros",
            Histogram::DbWrite => "regolith.write.batch_micros",
            Histogram::DbIterSeek => "regolith.iter.seek_micros",
            Histogram::DbIterNext => "regolith.iter.next_micros",
            Histogram::CompactionTime => "regolith.compaction.micros",
            Histogram::FlushTime => "regolith.flush.micros",
            Histogram::BytesPerRead => "regolith.read.bytes_per_get",
            Histogram::BytesPerWrite => "regolith.write.bytes_per_batch",
            Histogram::WalWriteTime => "regolith.wal.write_micros",
        }
    }
}

/// Immutable snapshot of a single histogram's state. Callers
/// read this to export to their metrics pipeline or assert in
/// tests.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct HistogramSnapshot {
    /// Number of samples recorded.
    pub count: u64,
    /// Sum of all recorded values.
    pub sum: u64,
    /// Minimum recorded value (0 when `count == 0`).
    pub min: u64,
    /// Maximum recorded value (0 when `count == 0`).
    pub max: u64,
}

impl HistogramSnapshot {
    /// Arithmetic mean. Returns 0 when `count == 0`.
    pub fn average(&self) -> u64 {
        self.sum.checked_div(self.count).unwrap_or(0)
    }
}

/// One histogram's running count, sum, min and max.
///
/// Lock-free: `record` runs on hot read and write paths, and a mutex here
/// serialised every instrumented `get` across threads. Each field is
/// updated independently, so a snapshot taken while a sample is being
/// recorded may include part of that one sample (its count but not yet
/// its sum, say). That is the precision these observability counters
/// need; `reset` racing a recorder is equally approximate.
#[derive(Debug)]
struct HistogramData {
    count: AtomicU64,
    sum: AtomicU64,
    /// `u64::MAX` until the first sample, so `fetch_min` needs no branch.
    min: AtomicU64,
    max: AtomicU64,
}

impl Default for HistogramData {
    fn default() -> Self {
        Self {
            count: AtomicU64::new(0),
            sum: AtomicU64::new(0),
            min: AtomicU64::new(u64::MAX),
            max: AtomicU64::new(0),
        }
    }
}

impl HistogramData {
    fn record(&self, value: u64) {
        self.count.fetch_add(1, Ordering::Relaxed);
        let mut sum = self.sum.load(Ordering::Relaxed);
        while let Err(current) = self.sum.compare_exchange_weak(
            sum,
            sum.saturating_add(value),
            Ordering::Relaxed,
            Ordering::Relaxed,
        ) {
            sum = current;
        }
        self.min.fetch_min(value, Ordering::Relaxed);
        self.max.fetch_max(value, Ordering::Relaxed);
    }

    fn snapshot(&self) -> HistogramSnapshot {
        let count = self.count.load(Ordering::Relaxed);
        if count == 0 {
            return HistogramSnapshot {
                count: 0,
                sum: 0,
                min: 0,
                max: 0,
            };
        }
        let min = self.min.load(Ordering::Relaxed);
        HistogramSnapshot {
            count,
            sum: self.sum.load(Ordering::Relaxed),
            min: if min == u64::MAX { 0 } else { min },
            max: self.max.load(Ordering::Relaxed),
        }
    }

    fn clear(&self) {
        self.count.store(0, Ordering::Relaxed);
        self.sum.store(0, Ordering::Relaxed);
        self.min.store(u64::MAX, Ordering::Relaxed);
        self.max.store(0, Ordering::Relaxed);
    }
}

/// Engine-wide counters and histograms. Constructed by the
/// caller and passed to [`crate::Options::statistics`]. The
/// engine clones the `Arc` into the paths it wants to
/// instrument and updates it with lock-free atomics.
pub struct Statistics {
    tickers: [AtomicU64; NUM_TICKERS],
    histograms: [HistogramData; NUM_HISTOGRAMS],
}

impl std::fmt::Debug for Statistics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Statistics").finish_non_exhaustive()
    }
}

impl Default for Statistics {
    fn default() -> Self {
        Self::new()
    }
}

impl Statistics {
    /// Construct a fresh `Statistics` with every ticker and
    /// histogram at zero.
    pub fn new() -> Self {
        // `AtomicU64` is not `Copy`, so we can't use the
        // `[x; N]` syntax. `std::array::from_fn` is the
        // cleanest alternative.
        let tickers = std::array::from_fn(|_| AtomicU64::new(0));
        let histograms = std::array::from_fn(|_| HistogramData::default());
        Self {
            tickers,
            histograms,
        }
    }

    /// Read the current value of a ticker. Guaranteed to be
    /// consistent with the corresponding `fetch_add` via
    /// `Ordering::Relaxed` - callers that need stronger
    /// ordering should wrap their own fences.
    pub fn get_ticker(&self, ticker: Ticker) -> u64 {
        self.tickers[ticker as usize].load(Ordering::Relaxed)
    }

    /// Return an immutable snapshot of a histogram's state.
    pub fn get_histogram_snapshot(&self, hist: Histogram) -> HistogramSnapshot {
        self.histograms[hist as usize].snapshot()
    }

    /// Zero every ticker and clear every histogram.
    pub fn reset(&self) {
        for t in &self.tickers {
            t.store(0, Ordering::Relaxed);
        }
        for h in &self.histograms {
            h.clear();
        }
    }

    /// Human-readable dump of every ticker and histogram. Meant
    /// for debug output, not machine parsing.
    pub fn dump(&self) -> String {
        let mut out = String::new();
        out.push_str("-- tickers --\n");
        for ticker in ALL_TICKERS {
            out.push_str(&format!(
                "{:40} {}\n",
                ticker.name(),
                self.tickers[*ticker as usize].load(Ordering::Relaxed)
            ));
        }
        out.push_str("-- histograms --\n");
        for hist in ALL_HISTOGRAMS {
            let snap = self.histograms[*hist as usize].snapshot();
            out.push_str(&format!(
                "{:40} count={} sum={} min={} max={} avg={}\n",
                hist.name(),
                snap.count,
                snap.sum,
                snap.min,
                snap.max,
                snap.average(),
            ));
        }
        out
    }

    /// Add `amount` to `ticker`. `Ordering::Relaxed` - callers
    /// that need stronger ordering should provide their own.
    pub(crate) fn add(&self, ticker: Ticker, amount: u64) {
        self.tickers[ticker as usize].fetch_add(amount, Ordering::Relaxed);
    }

    /// Record a single sample into `hist`.
    pub(crate) fn record(&self, hist: Histogram, value: u64) {
        self.histograms[hist as usize].record(value);
    }
}

/// Convenience RAII helper: creates a timer on construction and
/// records the elapsed wall-clock microseconds into `hist` on
/// `Drop`. If the statistics handle is `None` the helper is
/// optimized out - both construction and drop are no-ops.
pub(crate) struct TimeScope<'a> {
    /// Start reading in microseconds. `None` when no statistics
    /// handle is installed, and also `None` on a platform with no
    /// monotonic clock: the histogram then takes no sample at all
    /// rather than a zero that reads like a measurement.
    start: Option<u64>,
    stats: Option<&'a Statistics>,
    hist: Histogram,
}

impl<'a> TimeScope<'a> {
    pub(crate) fn new(stats: Option<&'a Statistics>, hist: Histogram) -> Self {
        Self {
            start: stats.and_then(|_| crate::env::platform_micros()),
            stats,
            hist,
        }
    }
}

impl Drop for TimeScope<'_> {
    fn drop(&mut self) {
        if let (Some(start), Some(stats), Some(now)) =
            (self.start, self.stats, crate::env::platform_micros())
        {
            stats.record(self.hist, now.saturating_sub(start));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(not(target_arch = "wasm32"))]
    #[test]
    fn concurrent_records_are_all_counted() {
        let stats = std::sync::Arc::new(Statistics::new());
        let threads: Vec<_> = (0..8u64)
            .map(|t| {
                let stats = std::sync::Arc::clone(&stats);
                std::thread::spawn(move || {
                    for i in 0..10_000u64 {
                        stats.record(Histogram::DbGet, t * 10_000 + i + 1);
                    }
                })
            })
            .collect();
        for t in threads {
            t.join().unwrap();
        }
        let snap = stats.get_histogram_snapshot(Histogram::DbGet);
        assert_eq!(snap.count, 80_000);
        assert_eq!(snap.sum, (1..=80_000u64).sum::<u64>());
        assert_eq!(snap.min, 1);
        assert_eq!(snap.max, 80_000);
    }

    #[test]
    fn an_empty_histogram_snapshots_as_zero_and_reset_empties_it() {
        let stats = Statistics::new();
        let empty = stats.get_histogram_snapshot(Histogram::DbGet);
        assert_eq!((empty.count, empty.sum, empty.min, empty.max), (0, 0, 0, 0));
        stats.record(Histogram::DbGet, 7);
        stats.reset();
        let reset = stats.get_histogram_snapshot(Histogram::DbGet);
        assert_eq!((reset.count, reset.sum, reset.min, reset.max), (0, 0, 0, 0));
        stats.record(Histogram::DbGet, 9);
        let one = stats.get_histogram_snapshot(Histogram::DbGet);
        assert_eq!((one.count, one.sum, one.min, one.max), (1, 9, 9, 9));
    }

    #[test]
    fn ticker_add_and_read() {
        let s = Statistics::new();
        assert_eq!(s.get_ticker(Ticker::BytesWritten), 0);
        s.add(Ticker::BytesWritten, 100);
        s.add(Ticker::BytesWritten, 50);
        assert_eq!(s.get_ticker(Ticker::BytesWritten), 150);
    }

    #[test]
    fn histogram_records_min_max_sum_count() {
        let s = Statistics::new();
        s.record(Histogram::DbGet, 10);
        s.record(Histogram::DbGet, 20);
        s.record(Histogram::DbGet, 5);
        let snap = s.get_histogram_snapshot(Histogram::DbGet);
        assert_eq!(snap.count, 3);
        assert_eq!(snap.sum, 35);
        assert_eq!(snap.min, 5);
        assert_eq!(snap.max, 20);
        assert_eq!(snap.average(), 11);
    }

    #[test]
    fn reset_zeroes_everything() {
        let s = Statistics::new();
        s.add(Ticker::BytesRead, 42);
        s.record(Histogram::FlushTime, 99);
        s.reset();
        assert_eq!(s.get_ticker(Ticker::BytesRead), 0);
        let snap = s.get_histogram_snapshot(Histogram::FlushTime);
        assert_eq!(snap, HistogramSnapshot::default());
    }

    #[test]
    fn dump_contains_every_ticker_and_histogram_name() {
        let s = Statistics::new();
        let out = s.dump();
        assert!(out.contains("regolith.write.bytes"));
        assert!(out.contains("regolith.block_cache.hit"));
        assert!(out.contains("regolith.read.get_micros"));
        assert!(out.contains("regolith.flush.micros"));
    }

    #[test]
    fn every_metric_name_is_unique_and_surface_prefixed() {
        const SURFACES: [&str; 11] = [
            "write",
            "read",
            "iter",
            "block_cache",
            "bloom",
            "compaction",
            "flush",
            "wal",
            "snapshot",
            "commit",
            "policy",
        ];
        let mut names: Vec<&str> = ALL_TICKERS
            .iter()
            .map(|t| t.name())
            .chain(ALL_HISTOGRAMS.iter().map(|h| h.name()))
            .collect();
        let total = names.len();
        names.sort_unstable();
        names.dedup();
        assert_eq!(names.len(), total, "metric names must be unique");
        for name in names {
            let rest = name
                .strip_prefix("regolith.")
                .unwrap_or_else(|| panic!("{name} must start with `regolith.`"));
            let surface = rest.split('.').next().unwrap();
            assert!(
                SURFACES.contains(&surface),
                "{name} uses unknown surface `{surface}`"
            );
        }
    }

    #[test]
    fn histogram_empty_snapshot_is_default() {
        let s = Statistics::new();
        assert_eq!(
            s.get_histogram_snapshot(Histogram::DbGet),
            HistogramSnapshot::default()
        );
    }

    #[test]
    fn time_scope_records_on_drop() {
        let s = Statistics::new();
        {
            let _t = TimeScope::new(Some(&s), Histogram::DbGet);
            std::thread::sleep(std::time::Duration::from_millis(1));
        }
        let snap = s.get_histogram_snapshot(Histogram::DbGet);
        assert_eq!(snap.count, 1);
        assert!(snap.sum > 0, "scope should have recorded non-zero micros");
    }

    #[test]
    fn time_scope_disabled_is_noop() {
        let _t = TimeScope::new(None, Histogram::DbGet);
        // Nothing to assert - the test is that Drop runs without
        // panicking when the stats handle is absent.
    }
}
