pub(crate) mod arena;
pub(crate) mod background_health;
pub(crate) mod block;
pub(crate) mod block_cache;
pub(crate) mod bloom;
pub(crate) mod callback;
pub(crate) mod checksum;
pub(crate) mod commit;
pub(crate) mod compaction;
#[cfg(not(target_arch = "wasm32"))]
pub(crate) mod compaction_backoff;
pub(crate) mod disk_check;
pub(crate) mod filter_block;
pub(crate) mod index_block;
mod ingest;
#[cfg(test)]
mod ingest_range_tests;
#[cfg(test)]
mod ingest_window_tests;
pub(crate) mod internal_key;
pub(crate) mod io;
pub(crate) mod iterator;
pub(crate) mod lookup_key;
#[cfg(loom)]
pub mod loom_model;
pub(crate) mod manifest;
pub(crate) mod memtable;
pub(crate) mod open_transactions;
pub(crate) mod orphan_sweep;
pub(crate) mod pending_outputs;
pub(crate) mod range_tombstone;
pub(crate) mod read_horizon;
mod read_rule;
pub(crate) mod read_view;
mod reclaim;
mod recovery;
pub(crate) mod skiplist;
pub(crate) mod snapshot_registry;
pub(crate) mod source_walk;
pub(crate) mod sstable;
pub(crate) mod wal;
#[cfg(test)]
mod wal_close_tests;
pub(crate) mod wal_frame;
pub(crate) mod wal_replay;
#[cfg(test)]
mod wal_rotation_tests;
pub(crate) mod wal_v1;

use crate::portability::{AtomicBool, AtomicU8, AtomicU64, Ordering};
use std::collections::{BTreeMap, HashSet};
use std::ops::ControlFlow;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::sync::internal::{Gate, Mutex, MutexGuard, OwnedGateWriteGuard};
use kovan_queue::array_queue::ArrayQueue;

use background_health::{BackgroundHealth, Hazard, Job};
use block_cache::BlockCache;
pub(crate) use commit::PendingAppend;
use commit::{Pipeline, StallSignal, WriteSlot};
use compaction::{CompactionOptions, CompactionOutcome, CompactionScheduler};
use lookup_key::{LookupKey, with_key_scratch};
use manifest::{VersionEdit, VersionSet};
use memtable::{MemTable, MemTableConfig};

const STOP_TOO_MANY_MEMTABLES: &str = "stop: too many memtables";
use pending_outputs::PendingOutputs;
use read_horizon::ReadHorizon;
pub(crate) use read_rule::ReadRule;
use read_view::{ReadView, ReadViewCell, VersionStore, ViewGuard};
use recovery::{replay_logs, report_discarded_tail, rewrite_recovered_memtable_to_wal};
use skiplist::InsertHint;
use snapshot_registry::SnapshotRegistry;
use source_walk::Source;

use crate::env::{Capabilities, Env, FileLock};
use crate::{Access, Conflict, DbSlice, WriteBatchOp, WriteKind, event_listener};
use sstable::{
    LiveSst, LookupResult, Materialize, PointValue, SsTableMeta, SsTableReader, SsTableWriter,
    sst_filename,
};
use wal::{RecordLen, Wal, WalEntry, check_write_len, wal_filename};

/// Controls when data is flushed to disk after a commit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DurabilityMode {
    Immediate,
    Eventual,
}

/// Outcome of [`RegolithEngine::commit_with_conflict_check`].
/// `Conflict` indicates that another writer changed one of the
/// tracked keys after the sequence the transaction observed it at;
/// the caller typically surfaces this as a retry-able error.
#[derive(Debug)]
pub(crate) enum CommitOutcome {
    /// The commit validated. `seq` is the sequence its writes became visible
    /// at, and `None` for a commit that carried no write.
    Ok { seq: Option<u64> },
    /// The reason, with the key still carrying its column-family prefix.
    Conflict(Conflict),
}

/// Why the engine stopped taking writes, see `RegolithEngine::write_latch`.
enum WriteLatch {
    /// A failed commit group could not be rolled back out of the log.
    Wal(std::io::ErrorKind, String),
    /// A caller's code of this trait panicked inside the ordered step.
    CallbackPanicked(&'static str),
}

/// Lay a commit's writes out as one batch: point operations in ascending key
/// order, then range deletes, then merges in ascending key order, each key's
/// operands in the order they were buffered. The commit's conflict check
/// relies on both sorted runs, so this layout is a guarantee and not an
/// accident.
fn grouped_batch_ops(
    point_ops: BTreeMap<Vec<u8>, Option<Vec<u8>>>,
    range_deletes: Vec<(Vec<u8>, Vec<u8>)>,
    mut merges: Vec<(Vec<u8>, Vec<u8>)>,
) -> Vec<WriteBatchOp> {
    // Stable on purpose: a key's operands must keep the order they were
    // buffered in, which is the order a read folds them.
    merges.sort_by(|a, b| a.0.cmp(&b.0));
    let mut ops = Vec::with_capacity(point_ops.len() + range_deletes.len() + merges.len());
    for (key, value) in point_ops {
        match value {
            Some(value) => ops.push(WriteBatchOp::Put { key, value }),
            None => ops.push(WriteBatchOp::Delete { key }),
        }
    }
    for (start, end) in range_deletes {
        ops.push(WriteBatchOp::DeleteRange { start, end });
    }
    for (key, operand) in merges {
        ops.push(WriteBatchOp::Merge { key, operand });
    }
    ops
}

/// Fold `operands`, oldest first, onto `base` with `op`. A read of the
/// database and a transaction's read of its own merges both go through here,
/// so both fail the same way when the operator declines.
pub(crate) fn apply_merge(
    op: &dyn crate::options::MergeOperator,
    key: &[u8],
    base: Option<&[u8]>,
    operands: &[&[u8]],
) -> std::io::Result<Vec<u8>> {
    op.full_merge(key, base, operands).ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!("merge operator {} failed for key", op.name()),
        )
    })
}

/// A key a commit validates because the transaction read it: the key and
/// the earliest sequence the transaction observed it at. Never elided as an
/// idempotent write, since a value derived from a stale read is a lost
/// update even when the bytes match.
#[derive(Clone, Debug)]
pub(crate) struct ConflictKey {
    /// The prefixed key.
    pub key: Vec<u8>,
    /// The sequence the transaction observed it at.
    pub observed_seq: u64,
    /// A read of the key returned a value. Recorded only for a transaction
    /// with a key classifier, which narrows it to `presence_only`; the
    /// commit does not look at it.
    pub found: bool,
    /// What the transaction did with the key, which is what a conflict on it
    /// reports. [`Access::ReadPresence`] marks a read of a key whose bytes
    /// never differ that returned a value, so it is lost only when the key
    /// is gone: see [`ConflictKey::presence_only`].
    pub access: Access,
    /// What counts as a change to the key since the read.
    pub rule: ReadRule,
}

impl ConflictKey {
    /// The read returned a value of a key whose bytes never differ, so a newer
    /// version conflicts only if the newest is a deletion, a covering range
    /// delete included. It does not stand for a write of the same key, which
    /// takes its own check.
    pub fn presence_only(&self) -> bool {
        self.access == Access::ReadPresence
    }
}

/// A key range a validated scan covered, as prefixed keys `[lo, hi)`: no
/// write may have landed in it after `observed_seq`. Sorted and disjoint in a
/// [`ValidationSet`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RangeCheck {
    pub lo: Vec<u8>,
    pub hi: Vec<u8>,
    pub observed_seq: u64,
}

/// What a commit validates on top of the operations it carries.
///
/// The written keys are not listed here: the commit already owns them in
/// its operation list and validates them from there, so listing them again
/// would clone every key a second time. What needs its own entry is a key
/// the transaction read, since a read carries its own anchor (the read's
/// sequence) and its own rule (never elided).
#[derive(Debug)]
pub(crate) struct ValidationSet {
    /// Keys the transaction read that the isolation level validates.
    /// Sorted by key with no duplicates; the commit relies on both to
    /// find a written key here by binary search and to name the same key
    /// on every run of a multi-key conflict. A read is validated in full
    /// (any newer version conflicts) unless it is `presence_only`.
    pub reads: Vec<ConflictKey>,
    /// The sequence every written or merged key not in `reads` is validated
    /// against, or `None` when written keys are not validated at all
    /// (pessimistic mode: the key lock orders them and there is no read to
    /// lose).
    pub writes_at: Option<u64>,
    /// Whether a key this commit only merges into, and did not read, is
    /// validated against the newest write that replaced it rather than the
    /// newest write of any kind. Operands commute, so a newer operand never
    /// invalidates a blind merge; a newer put or delete still does.
    pub blind_merges_commute: bool,
    /// Keys the commit puts or merges that the caller exempts from
    /// validation: the commit skips them without looking them up. Sorted by
    /// key with no duplicates, for the binary search that finds a written
    /// key here, and empty unless the transaction layer's key classifier
    /// named some, so a commit without one pays nothing. Their reads are not
    /// in `reads`, and a key the commit deletes is never listed.
    pub exempt: Vec<Vec<u8>>,
    /// Ranges a validated scan covered, which conflict with any write newer
    /// than their `observed_seq` inside them (see `commit::range_rule`).
    /// Empty unless the transaction used a validated scan.
    pub ranges: Vec<RangeCheck>,
}

fn batch_op_wal_bytes(op: &WriteBatchOp) -> u64 {
    match op {
        WriteBatchOp::Put { key, value } => (key.len() + value.len() + 8) as u64,
        WriteBatchOp::Delete { key } => (key.len() + 8) as u64,
        WriteBatchOp::DeleteRange { start, end } => (start.len() + end.len() + 8) as u64,
        WriteBatchOp::Merge { key, operand } => (key.len() + operand.len() + 8) as u64,
    }
}

fn memtable_needs_flush(memtable: &MemTable) -> bool {
    !memtable.is_empty() || memtable.has_range_tombstones()
}

/// Apply one batch op to `memtable`, threading `hint` through the point
/// ops. `DeleteRange` touches only the tombstone set, not the skip list,
/// so the hint stays valid across it.
fn apply_batch_op_to_memtable<'a>(
    memtable: &'a MemTable,
    hint: &mut InsertHint<'a>,
    op: &WriteBatchOp,
    seq: u64,
) {
    match op {
        WriteBatchOp::Put { key, value } => memtable.put_hinted(hint, key, value, seq),
        WriteBatchOp::Delete { key } => memtable.delete_hinted(hint, key, seq),
        WriteBatchOp::DeleteRange { start, end } => memtable.delete_range(start, end, seq),
        WriteBatchOp::Merge { key, operand } => memtable.merge_hinted(hint, key, operand, seq),
    }
}

/// One version of a key: its sequence, value type and value.
pub(crate) type KeyVersion = (u64, u8, DbSlice);

/// A key's visible versions, newest first, through its first terminator.
pub(crate) type MergeChain = Vec<KeyVersion>;

struct MultiGetEntry {
    key: Vec<u8>,
    output_indexes: Vec<usize>,
    max_rt: u64,
    resolved: bool,
}

fn grouped_multi_get_entries(keys: &[&[u8]]) -> Vec<MultiGetEntry> {
    let mut grouped: BTreeMap<Vec<u8>, Vec<usize>> = BTreeMap::new();
    for (idx, key) in keys.iter().enumerate() {
        grouped.entry((*key).to_vec()).or_default().push(idx);
    }
    grouped
        .into_iter()
        .map(|(key, output_indexes)| MultiGetEntry {
            key,
            output_indexes,
            max_rt: 0,
            resolved: false,
        })
        .collect()
}

fn file_covers_key(file: &LiveSst, key: &[u8]) -> bool {
    file.meta.smallest_key.as_slice() <= key && key <= file.meta.largest_key.as_slice()
}

fn resolve_multi_get_value(pseq: u64, popt: Option<DbSlice>, rt_seq: u64) -> Option<Vec<u8>> {
    if pseq > rt_seq {
        popt.map(DbSlice::into_vec)
    } else {
        None
    }
}

fn set_multi_get_result(
    entry: &mut MultiGetEntry,
    results: &mut [Option<Vec<u8>>],
    value: Option<Vec<u8>>,
) {
    for &output_idx in &entry.output_indexes {
        results[output_idx] = value.clone();
    }
    entry.resolved = true;
}

/// Configuration for the Regolith engine.
#[derive(Clone)]
pub(crate) struct EngineOptions {
    pub(crate) write_buffer_size: usize,
    pub(crate) arena_profile: crate::options::ArenaProfile,
    pub(crate) block_size: usize,
    pub(crate) block_cache_size: usize,
    pub(crate) block_cache_num_shard_bits: u32,
    pub(crate) strict_capacity_limit: bool,
    pub(crate) bloom_bits_per_key: usize,
    pub(crate) compression: crate::options::CompressionType,
    pub(crate) compression_per_level: Option<Vec<crate::options::CompressionType>>,
    pub(crate) l0_compaction_trigger: usize,
    pub(crate) level_base_bytes: u64,
    pub(crate) level_size_multiplier: u64,
    pub(crate) target_file_size: u64,
    pub(crate) compaction_filter: Option<Arc<dyn crate::options::CompactionFilter>>,
    pub(crate) prefix_extractor: Option<Arc<dyn crate::options::PrefixExtractor>>,
    pub(crate) merge_operator: Option<Arc<dyn crate::options::MergeOperator>>,
    pub(crate) listeners: Vec<Arc<dyn crate::event_listener::EventListener>>,
    pub(crate) transaction_hooks: Option<Arc<dyn crate::TransactionHooks>>,
    pub(crate) statistics: Option<Arc<crate::statistics::Statistics>>,
    pub(crate) rate_limiter: Option<Arc<dyn crate::rate_limiter::RateLimiter>>,
    pub(crate) level0_slowdown_writes_trigger: usize,
    pub(crate) level0_stop_writes_trigger: usize,
    pub(crate) soft_pending_compaction_bytes_limit: u64,
    pub(crate) hard_pending_compaction_bytes_limit: u64,
    pub(crate) max_write_buffer_number: usize,
    pub(crate) compaction_style: crate::options::CompactionStyle,
    pub(crate) fifo_compaction_options: crate::options::FifoCompactionOptions,
    pub(crate) universal_compaction_options: crate::options::UniversalCompactionOptions,
    pub(crate) evict_compaction_data_from_page_cache: bool,
    pub(crate) max_background_compactions: usize,
    pub(crate) partitioned_index: bool,
    pub(crate) metadata_block_size: usize,
    pub(crate) cache_index_and_filter_blocks: bool,
    pub(crate) read_only: bool,
    pub(crate) max_key_size: usize,
    pub(crate) max_value_size: usize,
    /// The host platform this database runs on. Every filesystem,
    /// clock, and thread call the engine makes goes through it.
    pub(crate) env: Arc<dyn Env>,
}

impl EngineOptions {
    /// How readers this engine opens should hold their index and
    /// filter blocks.
    pub(crate) fn metadata_policy(&self) -> sstable::MetadataPolicy {
        if self.cache_index_and_filter_blocks {
            sstable::MetadataPolicy::Cached
        } else {
            sstable::MetadataPolicy::Pinned
        }
    }

    /// Resolve the codec to use when writing an SSTable destined for
    /// `level`. A per-level override (if any) wins; otherwise fall
    /// back to the default codec.
    pub(crate) fn compression_for_level(&self, level: usize) -> crate::options::CompressionType {
        match &self.compression_per_level {
            Some(per_level) if level < per_level.len() => per_level[level],
            _ => self.compression,
        }
    }

    /// Project these options onto the subset compaction consumes.
    ///
    /// The three places that need a [`CompactionOptions`] - starting
    /// the scheduler, `compact_range`, and the foreground inline pass -
    /// all call this, so a knob added to one cannot go missing from
    /// another.
    pub(crate) fn to_compaction_options(&self) -> CompactionOptions {
        CompactionOptions {
            l0_compaction_trigger: self.l0_compaction_trigger,
            level_base_bytes: self.level_base_bytes,
            level_size_multiplier: self.level_size_multiplier,
            target_file_size: self.target_file_size,
            block_size: self.block_size,
            bloom_bits_per_key: self.bloom_bits_per_key,
            cache_index_and_filter_blocks: self.cache_index_and_filter_blocks,
            compression: self.compression,
            compression_per_level: self.compression_per_level.clone(),
            compaction_filter: self.compaction_filter.clone(),
            prefix_extractor: self.prefix_extractor.clone(),
            merge_operator: self.merge_operator.clone(),
            listeners: self.listeners.clone(),
            statistics: self.statistics.clone(),
            rate_limiter: self.rate_limiter.clone(),
            compaction_style: self.compaction_style,
            fifo_compaction_options: self.fifo_compaction_options,
            universal_compaction_options: self.universal_compaction_options,
            evict_compaction_data_from_page_cache: self.evict_compaction_data_from_page_cache,
            max_background_compactions: self.max_background_compactions,
            partitioned_index: self.partitioned_index,
            metadata_block_size: self.metadata_block_size,
            env: Arc::clone(&self.env),
        }
    }

    /// The stall policy implied by this configuration: with no
    /// background worker there is nobody to signal a parked writer, so
    /// the writer compacts on its own thread instead.
    pub(crate) fn stall_policy(&self) -> StallPolicy {
        if self.max_background_compactions == 0 {
            StallPolicy::CompactInline
        } else {
            StallPolicy::WaitForWorker
        }
    }
}

impl Default for EngineOptions {
    fn default() -> Self {
        Self {
            write_buffer_size: 64 * 1024 * 1024,
            arena_profile: crate::options::ArenaProfile::SERVER,
            block_size: 16 * 1024,
            block_cache_size: 512 * 1024 * 1024,
            block_cache_num_shard_bits: 6,
            strict_capacity_limit: false,
            bloom_bits_per_key: 10,
            compression: crate::options::CompressionType::Lz4,
            compression_per_level: None,
            l0_compaction_trigger: compaction::L0_COMPACTION_TRIGGER,
            level_base_bytes: compaction::DEFAULT_LEVEL_BASE_BYTES,
            level_size_multiplier: compaction::LEVEL_SIZE_MULTIPLIER,
            target_file_size: compaction::DEFAULT_TARGET_FILE_SIZE,
            compaction_filter: None,
            prefix_extractor: None,
            merge_operator: None,
            listeners: Vec::new(),
            transaction_hooks: None,
            statistics: None,
            rate_limiter: None,
            level0_slowdown_writes_trigger: 20,
            level0_stop_writes_trigger: 36,
            soft_pending_compaction_bytes_limit: 64 * 1024 * 1024 * 1024,
            hard_pending_compaction_bytes_limit: 256 * 1024 * 1024 * 1024,
            max_write_buffer_number: 2,
            compaction_style: crate::options::CompactionStyle::Level,
            fifo_compaction_options: crate::options::FifoCompactionOptions::default(),
            universal_compaction_options: crate::options::UniversalCompactionOptions::default(),
            evict_compaction_data_from_page_cache: false,
            max_background_compactions: 1,
            partitioned_index: false,
            metadata_block_size: 4096,
            cache_index_and_filter_blocks: false,
            read_only: false,
            max_key_size: crate::options::DEFAULT_MAX_KEY_SIZE,
            max_value_size: crate::options::DEFAULT_MAX_VALUE_SIZE,
            env: crate::env::std_env(),
        }
    }
}

const CLOSE_STATE_OPEN: u8 = 0;
const CLOSE_STATE_CLOSING: u8 = 1;
const CLOSE_STATE_CLOSED: u8 = 2;

/// Blocks of the configured block size one I/O queue may owe before a
/// further miss waits for room. Enough for a seek through every level and a
/// deep L0 at once, with each level's index leaf and filter.
const IO_QUEUE_BLOCKS: usize = 256;

/// The core LSM-tree engine.
pub(crate) struct RegolithEngine {
    /// The published read view: the active memtable, the frozen
    /// memtables and the version every read resolves against. Loading
    /// it is the whole of a read's source acquisition - one shared lock
    /// acquisition and one `Arc` clone - and the three sources it hands
    /// back are consistent with each other by construction.
    view: Arc<ReadViewCell>,
    /// The engine's one memtable arena pool and its sizing policy. Every
    /// memtable this engine builds recycles the others' chunks through it.
    memtable_config: MemTableConfig,
    /// The version set, together with the publication of every version
    /// it installs into `view`.
    versions: Arc<VersionStore>,
    cache: Arc<BlockCache>,
    /// Sequence-number allocator. Advanced up front (before a write's
    /// data lands) so WAL and memtable entries can be stamped, and used
    /// as the durable "last sequence" marker for WAL replay.
    latest_seq: AtomicU64,
    /// Published read horizon: the highest sequence whose data is fully
    /// applied and durable. Snapshots read this, never `latest_seq`, so a
    /// snapshot taken mid-commit cannot observe a sequence whose WAL and
    /// memtable writes have not landed yet. The ordering that makes that
    /// true lives in [`ReadHorizon`], which is where it is model-checked.
    visible_seq: ReadHorizon,
    close_state: AtomicU8,
    close_lock: Mutex<()>,
    /// Transactions that `close` must abort. See `open_transactions`.
    open_transactions: open_transactions::OpenTransactions,
    active_wal: Mutex<Option<Wal>>,
    wal_id: AtomicU64,
    sst_dir: PathBuf,
    wal_dir: PathBuf,
    compaction: Mutex<CompactionScheduler>,
    /// Engine-wide RwLock that coordinates foreground and background
    /// compaction. Background workers each hold a read lock so they
    /// can run concurrently; foreground callers (`compact_range`,
    /// `ingest_external_files`, `checkpoint_capture`) hold the write
    /// lock to exclude all background activity for the duration of
    /// their pass.
    compaction_lock: Arc<Gate>,
    /// Tracks the sequence numbers of every live snapshot so compaction
    /// can cut each key's versions into stripes no snapshot straddles,
    /// and drop or fold what no reader can see. A snapshot registers
    /// itself on creation and releases on drop; a compaction pass reads
    /// the list with [`SnapshotRegistry::live_seqs`] once its inputs are
    /// fixed.
    snapshot_registry: Arc<SnapshotRegistry>,
    options: EngineOptions,
    /// Bounded ring of writers waiting for a commit group. Writers push a
    /// ticket here and park; they never block on `pipeline`, which is what
    /// takes the WAL fsync off every writer's critical path.
    commit_ring: ArrayQueue<Arc<WriteSlot>>,
    /// Exclusion for the whole write pipeline, and the leader-owned
    /// staging buffers. Acquiring it *is* becoming the commit leader.
    /// Administrative operations that rotate the memtable or the WAL
    /// (`compact_range`, `ingest_external_files`, `checkpoint_capture`,
    /// `drop_all`, `close`) take it blockingly; no follower ever does.
    pipeline: Mutex<Pipeline>,
    /// Serializes [`Self::flush_oldest_frozen`] against itself.
    ///
    /// Not the same exclusion as `pipeline`. A rotation holds the
    /// pipeline mutex while it flushes, but `drain_memtables`
    /// releases it before it flushes (a flush writes a whole SSTable
    /// and must not block writers for that long), so a checkpoint's
    /// drain and a writer's rotation could both be inside the flush at
    /// once. They would then both take `frozen.first()` as their victim
    /// and both retire index 0, and the second retirement would drop a
    /// memtable whose contents are in no published version: an
    /// acknowledged write disappears, and a reader that had already seen
    /// it reads an older version instead.
    ///
    /// An ingest takes it only through `flush_until_retired`, for the
    /// memtables holding a key of its file's range, and holds the pipeline
    /// mutex until the file is installed. A memtable holding none of its
    /// keys may be flushed after it and land in front of it in L0, which
    /// changes no read: the two share no key (LsmOrder.tla, Lean
    /// `ingest_ordered`).
    flushing: Mutex<()>,
    /// Latched write-path failure. Set only when a failed commit group
    /// could not be rolled back out of the WAL, which leaves the log with
    /// a tail no later write may extend, or when a caller's code panicked
    /// inside the commit's ordered step. Once set, every write fails loud
    /// with the original reason instead of appending after unknown bytes or
    /// state.
    write_latch: Mutex<Option<WriteLatch>>,
    /// Cheap gate on `write_latch`, checked on every write.
    write_latched: AtomicBool,
    /// Signal used by foreground writers to wait out a "stop writes"
    /// condition (too many L0 files, too many unflushed memtables).
    /// The background compaction thread holds a clone of this `Arc`
    /// and calls [`StallSignal::notify_all`] after each compaction
    /// pass so blocked writers can re-check their thresholds.
    stall_signal: Arc<StallSignal>,
    /// Cached stall level: 0 = none, 1 = slowdown, 2 = stop.
    /// Updated by `rotate_memtable` (after changing L0/memtable
    /// counts) and by the compaction thread (after reducing them).
    /// Writers check this atomic first - the full `stall_state()`
    /// with its lock acquisitions is only called when the cached
    /// level is nonzero, saving 2 lock round-trips per write in
    /// the common no-stall case.
    cached_stall_level: AtomicU8,
    /// How a stalled writer makes room. See [`StallPolicy`].
    stall_policy: StallPolicy,
    /// File ids currently being compacted, shared with every background
    /// worker and with [`RegolithEngine::run_one_compaction_pass`]. One set
    /// for the whole engine is what stops a foreground pass and a
    /// worker from picking overlapping inputs.
    compaction_in_progress: Arc<Mutex<HashSet<u64>>>,
    /// Whether background flushes and compactions are currently failing.
    background_health: Arc<BackgroundHealth>,
    /// The host platform. Cloned out of [`EngineOptions`] so the read
    /// and write paths reach it without going through `options`.
    env: Arc<dyn Env>,
    _db_lock: Box<dyn FileLock>,
}

/// How a writer that has hit a "stop writes" threshold makes room.
///
/// Decided once at open from
/// [`crate::Options::max_background_compactions`] and never
/// re-evaluated, so write-stall behavior is a property of the
/// configuration rather than of a runtime accident.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StallPolicy {
    /// Background workers exist. Park on the stall condvar until a
    /// worker reports progress, re-checking on a bounded timeout.
    WaitForWorker,
    /// No background worker exists. The stalling writer is the
    /// compactor: it performs the compaction itself, on its own
    /// thread, and never parks.
    CompactInline,
}

impl RegolithEngine {
    /// Open or create the database at the given path.
    pub(crate) fn open(db_dir: &Path, mut options: EngineOptions) -> std::io::Result<Arc<Self>> {
        options.read_only = false;
        let env = Arc::clone(&options.env);
        let db_lock = env.lock_file(db_dir, true)?;
        disk_check::spawn(&env, db_dir.to_path_buf());
        let sst_dir = db_dir.join("sst");
        let wal_dir = db_dir.join("wal");

        env.create_dir_all(&sst_dir)?;
        env.create_dir_all(&wal_dir)?;

        let version_set =
            VersionSet::open_with_policy(&env, db_dir, &sst_dir, options.metadata_policy())?;
        let version = version_set.current();
        let latest_seq = version.last_seq;

        // Replay WAL files to recover memtable state
        let memtable_config = MemTableConfig::new(
            options.arena_profile,
            options.write_buffer_size,
            options.max_write_buffer_number,
        );
        let memtable = Arc::new(MemTable::new(&memtable_config)?);
        let mut wal_files = list_wal_files(&*env, &wal_dir)?;
        wal_files.sort();
        wal_files.retain(|path| should_replay_wal(path, version.min_wal_id));

        let (latest_seq, discarded) = replay_logs(&env, &wal_files, &memtable, latest_seq)?;
        if let Some((path, tail)) = discarded {
            // Before the next log exists, so the newest log is complete
            // when it becomes an earlier one (WalRecovery.tla, RED
            // `NoTruncate`): a crash before the old logs are removed below
            // leaves it beside the new one, and an earlier log with a
            // damaged tail refuses the open.
            wal::truncate_durably(&*env, &path, tail.offset)?;
            report_discarded_tail(&options, &path, tail, latest_seq);
        }

        let wal_id = next_wal_id(version.next_file_id, &wal_files);
        let wal_path = wal_dir.join(wal_filename(wal_id));
        let mut wal = Wal::create_in(&env, &wal_path)?;

        rewrite_recovered_memtable_to_wal(&memtable, &mut wal)?;

        for replayed_wal_path in &wal_files {
            if replayed_wal_path != &wal_path {
                match Wal::remove_in(&*env, replayed_wal_path) {
                    Ok(()) => {}
                    Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
                    Err(e) => return Err(e),
                }
            }
        }

        let versions = Arc::new(VersionStore::new(version_set));
        let view = Arc::new(ReadViewCell::new(ReadView {
            active: Arc::clone(&memtable),
            frozen: Vec::new(),
            version: versions.lock().current(),
        }));
        versions.attach_view(Arc::clone(&view));

        versions
            .lock()
            .apply(&[VersionEdit::SetNextFileId(wal_id + 1)])?;

        let cache = Arc::new(
            BlockCache::with_config(
                options.block_cache_size,
                options.block_cache_num_shard_bits,
                options.strict_capacity_limit,
            )
            .with_stats(options.statistics.clone()),
        );
        let compaction_opts = options.to_compaction_options();

        let compaction_lock = Arc::new(Gate::new());
        let snapshot_registry = Arc::new(SnapshotRegistry::with_env(Arc::clone(&env)));
        let stall_signal = Arc::new(StallSignal::new());
        let compaction_in_progress = Arc::new(Mutex::new(HashSet::new()));
        let background_health = Arc::new(BackgroundHealth::default());
        // `max_background_compactions == 0` starts no worker, which is
        // how a single-threaded target opens at all. A platform that
        // cannot spawn a worker it was asked for fails the open here
        // instead of aborting; the directory lock and the fresh WAL
        // drop with this return.
        let compaction = CompactionScheduler::start(
            Arc::clone(&compaction_lock),
            Arc::clone(&snapshot_registry),
            Arc::clone(&versions),
            Arc::from(sst_dir.as_path()),
            Arc::clone(&cache),
            compaction_opts,
            Arc::clone(&stall_signal),
            Arc::clone(&compaction_in_progress),
            Arc::clone(&background_health),
        )?;

        let engine = Arc::new(Self {
            view,
            memtable_config,
            versions,
            cache,
            latest_seq: AtomicU64::new(latest_seq),
            visible_seq: ReadHorizon::new(latest_seq),
            close_state: AtomicU8::new(CLOSE_STATE_OPEN),
            close_lock: Mutex::new(()),
            open_transactions: open_transactions::OpenTransactions::new(),
            active_wal: Mutex::new(Some(wal)),
            wal_id: AtomicU64::new(wal_id),
            sst_dir,
            wal_dir,
            compaction: Mutex::new(compaction),
            compaction_lock,
            snapshot_registry,
            stall_policy: options.stall_policy(),
            options,
            commit_ring: Self::new_commit_ring(),
            pipeline: Mutex::new(Pipeline::new()),
            flushing: Mutex::new(()),
            write_latch: Mutex::new(None),
            write_latched: AtomicBool::new(false),
            stall_signal,
            cached_stall_level: AtomicU8::new(0),
            compaction_in_progress,
            background_health,
            env,
            _db_lock: db_lock,
        });

        // Arm write back-pressure before the first write. A database
        // reopened with L0 already past its stop trigger would
        // otherwise take the `cached_stall_level == 0` fast path and
        // accept writes with no back-pressure until the first memtable
        // rotation refreshed the cache.
        engine.refresh_stall_level();

        Ok(engine)
    }

    /// Open an existing database without mutating files or starting
    /// background writers.
    pub(crate) fn open_read_only(
        db_dir: &Path,
        mut options: EngineOptions,
    ) -> std::io::Result<Arc<Self>> {
        let env = Arc::clone(&options.env);
        let db_lock = env.lock_file(db_dir, false)?;
        let sst_dir = db_dir.join("sst");
        let wal_dir = db_dir.join("wal");

        if !env.is_dir(&sst_dir) {
            return Err(std::io::Error::new(
                std::io::ErrorKind::NotFound,
                format!(
                    "missing SST directory for read-only open: {}",
                    sst_dir.display()
                ),
            ));
        }
        if !env.is_dir(&wal_dir) {
            return Err(std::io::Error::new(
                std::io::ErrorKind::NotFound,
                format!(
                    "missing WAL directory for read-only open: {}",
                    wal_dir.display()
                ),
            ));
        }

        options.read_only = true;

        let memtable_config = MemTableConfig::new(
            options.arena_profile,
            options.write_buffer_size,
            options.max_write_buffer_number,
        );
        let version_set =
            VersionSet::open_read_only(&env, db_dir, &sst_dir, options.metadata_policy())?;
        let version = version_set.current();
        let latest_seq = version.last_seq;

        let memtable = Arc::new(MemTable::new(&memtable_config)?);
        let mut wal_files = list_wal_files(&*env, &wal_dir)?;
        wal_files.sort();
        wal_files.retain(|path| should_replay_wal(path, version.min_wal_id));

        // A read-only open writes nothing, so the tail stays in the file;
        // the next read-write open drops it again and truncates it.
        let (latest_seq, discarded) = replay_logs(&env, &wal_files, &memtable, latest_seq)?;
        if let Some((path, tail)) = discarded {
            report_discarded_tail(&options, &path, tail, latest_seq);
        }

        let cache = Arc::new(
            BlockCache::with_config(
                options.block_cache_size,
                options.block_cache_num_shard_bits,
                options.strict_capacity_limit,
            )
            .with_stats(options.statistics.clone()),
        );
        let versions = Arc::new(VersionStore::new(version_set));
        let view = Arc::new(ReadViewCell::new(ReadView {
            active: Arc::clone(&memtable),
            frozen: Vec::new(),
            version: versions.lock().current(),
        }));
        versions.attach_view(Arc::clone(&view));
        let compaction_lock = Arc::new(Gate::new());
        let snapshot_registry = Arc::new(SnapshotRegistry::with_env(Arc::clone(&env)));
        let stall_signal = Arc::new(StallSignal::new());
        let wal_id = next_wal_id(version.next_file_id, &wal_files);

        Ok(Arc::new(Self {
            view,
            memtable_config,
            versions,
            cache,
            latest_seq: AtomicU64::new(latest_seq),
            visible_seq: ReadHorizon::new(latest_seq),
            close_state: AtomicU8::new(CLOSE_STATE_OPEN),
            close_lock: Mutex::new(()),
            open_transactions: open_transactions::OpenTransactions::new(),
            active_wal: Mutex::new(None),
            wal_id: AtomicU64::new(wal_id),
            sst_dir,
            wal_dir,
            compaction: Mutex::new(CompactionScheduler::disabled()),
            compaction_lock,
            snapshot_registry,
            // A read-only engine has no worker, so a writer could never
            // be woken. Writes are rejected before they reach the stall
            // path, and inline compaction refuses a read-only engine,
            // so this policy can only ever produce an error, never a
            // wait that nobody will end.
            stall_policy: StallPolicy::CompactInline,
            options,
            commit_ring: Self::new_commit_ring(),
            pipeline: Mutex::new(Pipeline::new()),
            flushing: Mutex::new(()),
            write_latch: Mutex::new(None),
            write_latched: AtomicBool::new(false),
            stall_signal,
            cached_stall_level: AtomicU8::new(0),
            compaction_in_progress: Arc::new(Mutex::new(HashSet::new())),
            background_health: Arc::new(BackgroundHealth::default()),
            env,
            _db_lock: db_lock,
        }))
    }

    /// What the installed environment can actually do.
    pub(crate) fn capabilities(&self) -> Capabilities {
        self.env.capabilities()
    }

    /// The environment this database runs on, for the wrappers
    /// (checkpoints, TTL) that do filesystem or clock work of their
    /// own and must do it on the same host.
    pub(crate) fn env(&self) -> &Arc<dyn Env> {
        &self.env
    }

    /// Microseconds elapsed since `start`, or `None` when this
    /// platform has no monotonic clock.
    ///
    /// A `None` means "not measured". Callers skip the recording
    /// rather than publishing a zero that reads like a measurement.
    fn elapsed_micros(&self, start: Option<u64>) -> Option<u64> {
        crate::env::elapsed_micros(&*self.env, start)
    }

    pub(crate) fn snapshot_seq(&self) -> u64 {
        self.visible_seq.visible()
    }

    pub(crate) fn is_read_only(&self) -> bool {
        self.options.read_only
    }

    /// The operator that folds merge operands into a value, if one is
    /// configured.
    pub(crate) fn merge_operator(&self) -> Option<&dyn crate::options::MergeOperator> {
        self.options.merge_operator.as_deref()
    }

    /// Refuses a merge write on a database with no operator to fold it, which
    /// reads would otherwise disagree about.
    pub(crate) fn require_merge_operator(&self) -> Result<(), crate::Error> {
        self.merge_operator()
            .map(|_| ())
            .ok_or(crate::Error::NoMergeOperator)
    }

    /// The transactions `close` aborts.
    pub(crate) fn open_transactions(&self) -> &open_transactions::OpenTransactions {
        &self.open_transactions
    }

    /// The database-wide transaction callbacks, if any are installed.
    pub(crate) fn transaction_hooks(&self) -> Option<&Arc<dyn crate::TransactionHooks>> {
        self.options.transaction_hooks.as_ref()
    }

    pub(crate) fn is_closed(&self) -> bool {
        self.close_state.load(Ordering::Acquire) != CLOSE_STATE_OPEN
    }

    fn closed_error() -> std::io::Error {
        crate::Error::Closed.into_io_error()
    }

    fn ensure_open(&self) -> std::io::Result<()> {
        if self.is_closed() {
            Err(Self::closed_error())
        } else {
            Ok(())
        }
    }

    fn read_only_error() -> std::io::Error {
        crate::Error::ReadOnly.into_io_error()
    }

    pub(crate) fn ensure_writable(&self) -> std::io::Result<()> {
        self.ensure_open()?;
        if self.write_latched.load(Ordering::Acquire) {
            return Err(self.latched_error());
        }
        if self.is_read_only() {
            Err(Self::read_only_error())
        } else {
            Ok(())
        }
    }

    /// Latch a write-ahead-log failure the engine cannot recover from
    /// on its own, so every later write fails loud with the reason
    /// rather than appending after a tail nobody can account for.
    pub(crate) fn latch_wal_failure(&self, err: &std::io::Error) {
        self.latch(WriteLatch::Wal(err.kind(), err.to_string()));
    }

    /// Latch the engine read-only because a caller's `callback` panicked
    /// inside the commit's ordered step, which left that step's shared state
    /// unaccounted for. Every later write fails with
    /// [`crate::Error::CallbackPanicked`] until the database is reopened.
    pub(crate) fn latch_callback_panic(&self, callback: &'static str) {
        self.latch(WriteLatch::CallbackPanicked(callback));
    }

    /// Keep the first reason: it is the one that explains the rest.
    fn latch(&self, latch: WriteLatch) {
        self.write_latch.lock().get_or_insert(latch);
        self.write_latched.store(true, Ordering::Release);
    }

    fn latched_error(&self) -> std::io::Error {
        match self.write_latch.lock().as_ref() {
            Some(WriteLatch::Wal(kind, message)) => std::io::Error::new(
                *kind,
                format!("write-ahead log left in an unknown state: {message}"),
            ),
            Some(WriteLatch::CallbackPanicked(callback)) => crate::Error::CallbackPanicked {
                callback,
                latched: true,
            }
            .into_io_error(),
            None => std::io::Error::other("write-ahead log left in an unknown state"),
        }
    }

    /// Install a new log, named `new_wal_id`, as the active one and hand back
    /// the log it seals.
    ///
    /// Recovery takes the newest log by file name and tolerates a torn tail
    /// only there, so a log has to be complete on disk before any newer file
    /// exists, an empty one included, and `Eventual` durability never syncs a
    /// log on its own. Hence the order, all under the `active_wal` lock so no
    /// commit appends to the old log in between: sync it, create the new
    /// file, swap. A failed sync latches the log as unknown, since its tail
    /// can no longer be vouched for and a retried sync may report success for
    /// pages the kernel already dropped.
    fn swap_wal(&self, new_wal_id: u64) -> std::io::Result<Wal> {
        let mut guard = self.active_wal.lock();
        let current = guard.as_mut().ok_or_else(Self::read_only_error)?;
        if let Err(err) = current.sync_data() {
            drop(guard);
            tracing::error!(error = %err, "syncing the write-ahead log before sealing it failed");
            self.latch_wal_failure(&err);
            self.notify_wal_error(&err)?;
            return Err(err);
        }
        let new_wal = Wal::create_in(&self.env, &self.wal_dir.join(wal_filename(new_wal_id)))?;
        guard.replace(new_wal).ok_or_else(Self::read_only_error)
    }

    fn validate_prefixed_key_size(&self, key: &[u8]) -> std::io::Result<()> {
        self.validate_user_key_len(key.len().saturating_sub(4))
    }

    /// [`Self::validate_prefixed_key_size`] for a key known by its length,
    /// without the column-family prefix.
    fn validate_user_key_len(&self, user_key_len: usize) -> std::io::Result<()> {
        if user_key_len <= self.options.max_key_size {
            return Ok(());
        }

        Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!(
                "key length {} exceeds configured max_key_size {}",
                user_key_len, self.options.max_key_size
            ),
        ))
    }

    fn validate_value_size(&self, value: &[u8]) -> std::io::Result<()> {
        if value.len() <= self.options.max_value_size {
            return Ok(());
        }

        Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!(
                "value length {} exceeds configured max_value_size {}",
                value.len(),
                self.options.max_value_size
            ),
        ))
    }

    /// `disable_wal` skips the record-length check, since the write
    /// produces no WAL record; key and value limits still apply.
    fn validate_ops_sizes(&self, ops: &[WriteBatchOp], disable_wal: bool) -> std::io::Result<()> {
        let mut record = RecordLen::default();
        for op in ops {
            match op {
                WriteBatchOp::Put { key, value } => {
                    self.validate_prefixed_key_size(key)?;
                    self.validate_value_size(value)?;
                    record.put(key, value);
                }
                WriteBatchOp::Delete { key } => {
                    self.validate_prefixed_key_size(key)?;
                    record.delete(key);
                }
                WriteBatchOp::DeleteRange { start, end } => {
                    self.validate_prefixed_key_size(start)?;
                    self.validate_prefixed_key_size(end)?;
                    record.delete_range(start, end);
                }
                WriteBatchOp::Merge { key, operand } => {
                    self.validate_prefixed_key_size(key)?;
                    self.validate_value_size(operand)?;
                    record.merge(key, operand);
                }
            }
        }
        if !disable_wal {
            check_write_len(record.framed())?;
        }
        Ok(())
    }

    /// Borrow the engine's `Statistics` sink if one is configured.
    /// Returning `Option<&Statistics>` lets instrumented call
    /// sites branch on a single `is_some()` check rather than
    /// cloning an `Arc` per operation.
    pub(crate) fn statistics(&self) -> Option<&crate::statistics::Statistics> {
        self.options.statistics.as_deref()
    }

    /// Clone the statistics `Arc` for consumers (like the public
    /// `Iter`) that need to carry the handle across a lifetime
    /// boundary where a borrowed reference wouldn't reach.
    pub(crate) fn statistics_arc(&self) -> Option<Arc<crate::statistics::Statistics>> {
        self.options.statistics.clone()
    }

    /// A new I/O queue for one thread, on this database's block cache.
    ///
    /// What the queue may owe is bounded by bytes: [`IO_QUEUE_BLOCKS`]
    /// blocks of the configured block size, so the bound follows the block
    /// size the reads are made of.
    pub(crate) fn io_queue(&self) -> crate::IoQueue {
        crate::IoQueue::open(
            Arc::clone(&self.cache),
            self.options.block_size.saturating_mul(IO_QUEUE_BLOCKS),
        )
    }

    /// Register a new live snapshot at `seq` so compaction keeps
    /// every version it might need to see. Balanced by
    /// [`Self::release_snapshot`] when the snapshot drops.
    pub(crate) fn register_snapshot(&self, seq: u64) {
        if self.is_closed() {
            return;
        }
        self.snapshot_registry.register(seq);
        if let Some(s) = self.statistics() {
            s.add(crate::statistics::Ticker::SnapshotsRegistered, 1);
        }
    }

    /// Pin a snapshot at the current read horizon, sampling the
    /// horizon and registering the pin as one step so a concurrent
    /// compaction cannot cut its stripes from a registry that does
    /// not yet contain this pin. Returns the pinned sequence.
    pub(crate) fn register_snapshot_at_horizon(&self) -> u64 {
        if self.is_closed() {
            return self.visible_seq.visible();
        }
        let seq = self
            .snapshot_registry
            .register_at(|| self.visible_seq.visible());
        if let Some(s) = self.statistics() {
            s.add(crate::statistics::Ticker::SnapshotsRegistered, 1);
        }
        seq
    }

    /// Release a snapshot pin previously taken via
    /// [`Self::register_snapshot`].
    pub(crate) fn release_snapshot(&self, seq: u64) {
        self.snapshot_registry.release(seq);
        if let Some(s) = self.statistics() {
            s.add(crate::statistics::Ticker::SnapshotsReleased, 1);
        }
    }

    /// The smallest live snapshot seq, or `u64::MAX` if no snapshot is
    /// currently pinned.
    pub(crate) fn oldest_live_seq(&self) -> u64 {
        self.snapshot_registry.oldest_live_seq()
    }

    /// Wait for every snapshot pin to be released, returning how many
    /// were still outstanding when `timeout` elapsed.
    pub(crate) fn wait_for_snapshots(&self, timeout: std::time::Duration) -> u64 {
        self.snapshot_registry.wait_until_drained(timeout)
    }

    /// Construct a streaming iterator over the latest published read
    /// horizon. The view is loaded before the horizon is sampled, for
    /// the reason spelled out on [`Self::get_latest`].
    pub(crate) fn new_iter_latest(&self) -> iterator::RegolithIterator {
        let closed = self.is_closed();
        let view = self.view.load();
        let snapshot_seq = self.visible_seq.visible();
        self.iter_in_view(&view, snapshot_seq, closed)
    }

    /// Construct a streaming iterator rooted at a caller-pinned
    /// `snapshot_seq`. Captures one published view of the memtables and
    /// the version; no filesystem access happens here - file handles
    /// are already open in the pinned `Arc<LiveSst>`s carried by the
    /// version.
    pub(crate) fn new_iter_at(&self, snapshot_seq: u64) -> iterator::RegolithIterator {
        let closed = self.is_closed();
        let view = self.view.load();
        self.iter_in_view(&view, snapshot_seq, closed)
    }

    fn iter_in_view(
        &self,
        view: &ReadView,
        snapshot_seq: u64,
        closed: bool,
    ) -> iterator::RegolithIterator {
        let mut iter = iterator::RegolithIterator::new(
            Arc::clone(&view.active),
            view.frozen.clone(),
            Arc::clone(&view.version),
            Arc::clone(&self.cache),
            snapshot_seq,
            self.options.prefix_extractor.clone(),
            self.options.merge_operator.clone(),
        );
        if closed {
            iter.set_error(Self::closed_error());
        }
        iter
    }

    /// Point lookup at the latest published read horizon.
    ///
    /// The order of the first two statements is load-bearing: the view
    /// is loaded FIRST and the horizon sampled SECOND. Sampling the
    /// horizon first lets a compaction garbage-collect the newest
    /// version at or below it - compaction cuts its stripes at the
    /// registered snapshots, and a read without a `Snapshot` registers
    /// nothing there - after which the key reads back as absent. A
    /// version that compaction dropped was shadowed by a newer one
    /// that had already been flushed into the version being published,
    /// so a horizon sampled after the view is always at least that
    /// newer version's sequence and the read finds it.
    ///
    /// The read linearizes at the moment it loads the view: a write
    /// that lands between the load and the horizon sample is simply
    /// not part of this read. Read-your-writes still holds, because a
    /// write applies into the active memtable of the view current at
    /// that moment and every later view still exposes that memtable's
    /// data, as `active`, as `frozen`, or folded into the version.
    pub(crate) fn get_latest(&self, key: &[u8]) -> std::io::Result<Option<Vec<u8>>> {
        self.ensure_open()?;
        let view = self.view.load();
        let lk = LookupKey::from_prefixed(key, self.visible_seq.visible());
        if self.options.merge_operator.is_some() {
            return Ok(self.get_with_merge(&lk, &view)?.map(DbSlice::into_vec));
        }
        Ok(self
            .lookup_in_view(
                lk.prefixed_user_key(),
                lk.snapshot_seq(),
                &lk,
                Materialize::Value,
                &view,
            )?
            .and_then(|v| match v {
                PointValue::Value(value) => Some(value.into_vec()),
                PointValue::Length(_) => None,
            }))
    }

    /// Point lookup at a caller-pinned snapshot sequence, without copying
    /// the value out of the block or heap buffer it already lives in. The
    /// snapshot's registration in [`SnapshotRegistry`] is what keeps
    /// compaction from dropping the versions it needs, so the load order
    /// does not matter here; the view is still loaded once so every
    /// source the read walks agrees with every other.
    pub(crate) fn get_slice_at(
        &self,
        prefixed_key: &[u8],
        snapshot_seq: u64,
    ) -> std::io::Result<Option<DbSlice>> {
        let lk = LookupKey::from_prefixed(prefixed_key, snapshot_seq);
        self.get_slice(&lk)
    }

    /// Point lookup resolved against one already-loaded view.
    ///
    /// Walks sources newest→oldest (active memtable, frozen memtables
    /// newest first, L0 newest first, L1..Ln). At each source we check
    /// both the newest visible point entry and the newest visible
    /// covering range tombstone, carrying the largest RT seq forward so
    /// a range delete in a newer source can override a point entry in
    /// an older source. The first source yielding a decisive answer
    /// wins - a point entry with `seq > max_rt_so_far` gives its value;
    /// otherwise the range tombstone hides it.
    ///
    /// When a [`crate::MergeOperator`] is configured, the walk also
    /// collects any merge operands that sit on top of the terminator
    /// and calls the operator to collapse the chain into a final
    /// value at visibility time.
    #[cfg(test)]
    pub(crate) fn get(
        &self,
        prefixed_key: &[u8],
        snapshot_seq: u64,
    ) -> std::io::Result<Option<Vec<u8>>> {
        let lk = LookupKey::from_prefixed(prefixed_key, snapshot_seq);
        Ok(self.get_slice(&lk)?.map(DbSlice::into_vec))
    }

    /// Newest visible value for `key`, without copying it. The returned
    /// [`DbSlice`] borrows the block or heap buffer the value already
    /// lives in and keeps that owner alive.
    ///
    /// The read samples its sequence with the view it reads through
    /// already loaded. The order is load-bearing and it is the whole reason this is not
    /// `visible_seq.visible()` at the call site. Sampling the horizon
    /// first and loading the view afterwards leaves a window in
    /// between: `snapshot_seq()` registers nothing in the
    /// [`SnapshotRegistry`], so a compaction is free to drop the newest
    /// version at or below the sampled sequence, and the read then
    /// walks a view that no longer holds it and reports the key absent
    /// or an older value. That is a read travelling backwards.
    ///
    /// Loading the view first pins the sources, so every version the
    /// sampled horizon admits is still reachable through it.
    ///
    /// A caller reading at a *pinned* snapshot does not need this: the
    /// registration is what holds the versions, so the order does not
    /// matter there. See [`RegolithEngine::get_slice_at`].
    pub(crate) fn get_slice_latest(
        &self,
        cf_id: u32,
        key: &[u8],
    ) -> std::io::Result<Option<DbSlice>> {
        match self.lookup_latest_cf(cf_id, key, Materialize::Value)? {
            Some(PointValue::Value(value)) => Ok(Some(value)),
            Some(PointValue::Length(_)) => Err(std::io::Error::other(
                "point lookup produced a length where a value was requested",
            )),
            None => Ok(None),
        }
    }

    /// Length of the newest visible value for `key`, or `None`.
    pub(crate) fn get_size_latest(
        &self,
        cf_id: u32,
        key: &[u8],
        limit: Option<usize>,
    ) -> std::io::Result<Option<usize>> {
        Ok(self
            .lookup_latest_cf(cf_id, key, Materialize::LengthOnly(limit))?
            .map(|v| v.len()))
    }

    pub(crate) fn get_slice(&self, lk: &LookupKey) -> std::io::Result<Option<DbSlice>> {
        match self.lookup(lk, Materialize::Value)? {
            Some(PointValue::Value(value)) => Ok(Some(value)),
            Some(PointValue::Length(_)) => Err(std::io::Error::other(
                "point lookup produced a length where a value was requested",
            )),
            None => Ok(None),
        }
    }

    /// Length of the live value for `lk`, or `None` when there is none.
    ///
    /// Reads the same sources [`RegolithEngine::get_slice`] does and pays
    /// the same block reads, but never takes a reference on the block
    /// or buffer the value lives in.
    pub(crate) fn get_size(
        &self,
        lk: &LookupKey,
        limit: Option<usize>,
    ) -> std::io::Result<Option<usize>> {
        Ok(self
            .lookup(lk, Materialize::LengthOnly(limit))?
            .map(|v| v.len()))
    }

    /// Look one SSTable up, projecting the hit into whichever form the
    /// caller asked for. The two arms run the same bloom check, index
    /// search, block read and block scan; they differ only in whether
    /// the winning value is handed back as bytes or as a length.
    fn probe_file(
        &self,
        reader: &SsTableReader,
        lk: &LookupKey,
        materialize: Materialize,
    ) -> std::io::Result<LookupResult<PointValue>> {
        with_key_scratch(|buf| match materialize {
            Materialize::Value => Ok(reader
                .get(lk, buf, &self.cache)?
                .map_value(PointValue::Value)),
            Materialize::LengthOnly(limit) => Ok(reader
                .get_size(lk, buf, &self.cache, limit)?
                .map_value(PointValue::Length)),
        })
    }

    /// The single point-read source walk. `materialize` decides only
    /// what the winning entry is projected into, never which sources
    /// are consulted or how MVCC and range-tombstone precedence are
    /// resolved, so every `get`-shaped entry point agrees by
    /// construction.
    fn lookup(
        &self,
        lk: &LookupKey,
        materialize: Materialize,
    ) -> std::io::Result<Option<PointValue>> {
        self.ensure_open()?;
        let view = self.view.load();
        self.lookup_loaded(lk, materialize, &view)
    }

    /// [`Self::lookup`] against a view the caller already loaded, so a commit
    /// check reads a value the way a `get` does: a configured merge operator
    /// collapses the key's operands first.
    fn lookup_loaded(
        &self,
        lk: &LookupKey,
        materialize: Materialize,
        view: &ReadView,
    ) -> std::io::Result<Option<PointValue>> {
        if self.options.merge_operator.is_some() {
            Self::reject_guarded_merge(materialize)?;
            // A merge operator decides inside `full_merge` whether a
            // value exists at all, so a length-only request has to
            // collapse the chain exactly like a full read does.
            return Ok(self.get_with_merge(lk, view)?.map(PointValue::Value));
        }
        self.lookup_in_view(
            lk.prefixed_user_key(),
            lk.snapshot_seq(),
            lk,
            materialize,
            view,
        )
    }

    /// Read the newest visible value for `key`, sampling the horizon
    /// against the very view the read then walks.
    ///
    /// One view load, one sample, in that order. Sampling first and
    /// loading afterwards leaves a window where a compaction can drop
    /// the newest version at or below the sampled sequence, and the
    /// read reports the key absent or an older value: a read that
    /// travels backwards. Sampling under a *different* view load than
    /// the one the read walks has the same hole, only narrower, which
    /// is why the two happen here together rather than in a helper the
    /// caller composes.
    fn lookup_latest_cf(
        &self,
        cf_id: u32,
        key: &[u8],
        materialize: Materialize,
    ) -> std::io::Result<Option<PointValue>> {
        self.ensure_open()?;
        let view = self.view.load();
        // `LookupKey::new` writes the prefix into its own inline buffer,
        // so the read path stays allocation-free: prefixing into a
        // `Vec` here would put a malloc on every point read.
        let lk = LookupKey::new(cf_id, key, self.visible_seq.visible());
        let snapshot_seq = lk.snapshot_seq();
        if self.options.merge_operator.is_some() {
            Self::reject_guarded_merge(materialize)?;
            return Ok(self.get_with_merge(&lk, &view)?.map(PointValue::Value));
        }
        self.lookup_in_view(
            lk.prefixed_user_key(),
            snapshot_seq,
            &lk,
            materialize,
            &view,
        )
    }

    fn reject_guarded_merge(materialize: Materialize) -> std::io::Result<()> {
        if matches!(materialize, Materialize::LengthOnly(Some(_))) {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "guarded size reads do not support a configured merge operator",
            ));
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lookup_in_view(
        &self,
        key: &[u8],
        snapshot_seq: u64,
        lk: &LookupKey,
        materialize: Materialize,
        view: &ReadView,
    ) -> std::io::Result<Option<PointValue>> {
        use crate::perf_context::{PerfTimer, PerfTimerField};

        // Memtable phase - timed via `PerfContext` at
        // `PerfLevel::EnableTime` so per-op breakdowns can
        // attribute time to "memtable vs SSTable". The first table the
        // walk reaches starts the SSTable phase: everything from there is
        // the "get_from_output_files" time.
        let mut timer = PerfTimer::new(PerfTimerField::GetFromMemtable);
        let mut in_tables = false;
        let walked = view.walk_newest_first(key, snapshot_seq, |source, max_rt_seq| {
            Ok(match source {
                Source::Memtable(mt) => match mt.get(lk) {
                    Some((seq, value)) => ControlFlow::Break(if seq > max_rt_seq {
                        value.map(|v| PointValue::of(v, materialize))
                    } else {
                        None
                    }),
                    None => ControlFlow::Continue(()),
                },
                // Readers are already open in the pinned `Version`, so no
                // filesystem access happens here - concurrent compaction
                // unlinking paths cannot break us.
                Source::Table(reader) => {
                    if !in_tables {
                        in_tables = true;
                        drop(std::mem::replace(
                            &mut timer,
                            PerfTimer::new(PerfTimerField::GetFromOutputFiles),
                        ));
                    }
                    match self.probe_file(reader, lk, materialize)? {
                        LookupResult::Found { seq, value } => {
                            ControlFlow::Break((seq > max_rt_seq).then_some(value))
                        }
                        LookupResult::FoundTombstone { .. } => ControlFlow::Break(None),
                        LookupResult::NotInTable => ControlFlow::Continue(()),
                    }
                }
            })
        })?;
        Ok(match walked {
            ControlFlow::Break(found) => found,
            ControlFlow::Continue(_) => None,
        })
    }

    /// Every visible entry for `lk`'s key in `view`, newest first, through
    /// the first terminator: a value, a deletion, or a covering range
    /// tombstone standing in as one.
    fn merge_chain_in_view(&self, lk: &LookupKey, view: &ReadView) -> std::io::Result<MergeChain> {
        use internal_key::VALUE_TYPE_DELETION;

        // `chain` records visible entries for `key` in newest-seq-
        // first order, stopping at (and including) the first
        // terminator (`VALUE` or `DELETION`). Range tombstones that
        // cover the key are treated as virtual deletion terminators.
        let mut chain: MergeChain = Vec::new();
        // The chain is the result; where the walk ended adds nothing to it.
        let _ = view.walk_newest_first(
            lk.prefixed_user_key(),
            lk.snapshot_seq(),
            |source, max_rt_seq| {
                let start = chain.len();
                let terminated = match source {
                    Source::Memtable(mt) => mt.collect_merge_chain(lk, &mut chain),
                    Source::Table(reader) => with_key_scratch(|buf| {
                        reader.collect_merge_chain(lk, buf, &self.cache, &mut chain)
                    })?,
                };
                // Entries are newest first, so a range tombstone hides the
                // first entry at or below it and every older one: it stands
                // in as the terminator.
                if let Some(hidden) = chain[start..]
                    .iter()
                    .position(|entry| entry.0 <= max_rt_seq)
                {
                    chain.truncate(start + hidden);
                    chain.push((max_rt_seq, VALUE_TYPE_DELETION, DbSlice::empty()));
                    return Ok(ControlFlow::Break(()));
                }
                Ok(if terminated {
                    ControlFlow::Break(())
                } else {
                    ControlFlow::Continue(())
                })
            },
        )?;
        Ok(chain)
    }

    /// Merge-aware point lookup. Walks every source newest→oldest
    /// collecting merge operands and any base value / deletion into
    /// a single chain, honors range-tombstone coverage, and calls
    /// [`crate::MergeOperator::full_merge`] at the end to materialize
    /// the final value.
    ///
    /// Resolved against the caller's `view`, never one loaded here: the
    /// caller chose `lk`'s sequence against that view, and a later one
    /// may have had the version that sequence admits compacted away.
    ///
    /// Callers are responsible for having checked that
    /// `self.options.merge_operator.is_some()`; this helper asserts
    /// internally.
    fn get_with_merge(&self, lk: &LookupKey, view: &ReadView) -> std::io::Result<Option<DbSlice>> {
        use internal_key::{VALUE_TYPE_DELETION, VALUE_TYPE_MERGE, VALUE_TYPE_VALUE};

        let merge_op = self
            .options
            .merge_operator
            .as_ref()
            .expect("get_with_merge called without a merge operator");

        let key = lk.prefixed_user_key();
        let mut chain = self.merge_chain_in_view(lk, view)?;
        // Materialize the chain. `chain` is newest-first; the last
        // entry (if any) is either a real VALUE / DELETION terminator
        // or (if !terminated) the oldest visible merge operand.
        let (base_slice, has_terminator) = match chain.last() {
            Some((_, VALUE_TYPE_VALUE, value)) => (Some(value.as_slice()), true),
            Some((_, VALUE_TYPE_DELETION, _)) => (None, true),
            _ => (None, false),
        };

        // Build operands in oldest-first order: walk the merge part
        // of the chain (everything except the terminator slot, if
        // one is present) in reverse.
        let merge_end = if has_terminator {
            chain.len() - 1
        } else {
            chain.len()
        };
        let mut operands_owned: Vec<&[u8]> = Vec::with_capacity(merge_end);
        for entry in chain[..merge_end].iter().rev() {
            debug_assert_eq!(entry.1, VALUE_TYPE_MERGE);
            operands_owned.push(entry.2.as_slice());
        }

        if operands_owned.is_empty() {
            // No merges at all - the chain is just a plain
            // Value / Deletion / nothing. Return the base directly.
            drop(operands_owned);
            return Ok(match chain.pop() {
                Some((_, vt, value)) if vt == VALUE_TYPE_VALUE => Some(value),
                _ => None,
            });
        }

        apply_merge(merge_op.as_ref(), key, base_slice, &operands_owned)
            .map(|merged| Some(DbSlice::from_vec(merged)))
    }

    /// Batched point lookup at a given snapshot. Returns one `Option<Vec<u8>>`
    /// per input key in the same order as `keys`. Duplicate keys in the
    /// input produce duplicate results.
    ///
    /// The batch amortizes per-call overhead - one loaded view, one
    /// sequence, one logical walk of the source hierarchy - and
    /// short-circuits once every key has been resolved. All keys are read
    /// at that one sequence from that one view, with or without a merge
    /// operator, so a concurrent writer cannot make two keys disagree.
    pub(crate) fn multi_get_latest(&self, keys: &[&[u8]]) -> std::io::Result<Vec<Option<Vec<u8>>>> {
        self.ensure_open()?;
        let view = self.view.load();
        let snapshot_seq = self.visible_seq.visible();
        self.multi_get_in_view(keys, snapshot_seq, &view)
    }

    /// Batched point lookup at a caller-pinned snapshot sequence. See
    /// [`Self::get_slice_at`] for why the load order is free here.
    pub(crate) fn multi_get_at(
        &self,
        keys: &[&[u8]],
        snapshot_seq: u64,
    ) -> std::io::Result<Vec<Option<Vec<u8>>>> {
        self.ensure_open()?;
        let view = self.view.load();
        self.multi_get_in_view(keys, snapshot_seq, &view)
    }

    /// Batched point lookup resolved against one already-loaded view.
    fn multi_get_in_view(
        &self,
        keys: &[&[u8]],
        snapshot_seq: u64,
        view: &ReadView,
    ) -> std::io::Result<Vec<Option<Vec<u8>>>> {
        // When a merge operator is configured, fall back to per-key
        // resolution - the batched walk's short-circuiting logic
        // doesn't compose cleanly with merge-chain collection, and
        // merges are rare enough that the cost difference isn't
        // worth a specialized batched path.
        if self.options.merge_operator.is_some() {
            let mut out = Vec::with_capacity(keys.len());
            let mut lk = LookupKey::from_prefixed(&[], snapshot_seq);
            for key in keys {
                lk.reset_prefixed(key, snapshot_seq);
                out.push(self.get_with_merge(&lk, view)?.map(DbSlice::into_vec));
            }
            return Ok(out);
        }

        let mut results: Vec<Option<Vec<u8>>> = vec![None; keys.len()];
        if keys.is_empty() {
            return Ok(results);
        }
        let mut entries = grouped_multi_get_entries(keys);
        let mut unresolved = entries.len();
        // One encoder, re-pointed per key, instead of one per key per
        // source.
        let mut lk = LookupKey::from_prefixed(&[], snapshot_seq);

        // 1. Active memtable.
        {
            let mt = &view.active;
            for entry in &mut entries {
                if entry.resolved {
                    continue;
                }
                let rt = mt.covering_range_tombstone_seq(&entry.key, snapshot_seq);
                if rt > entry.max_rt {
                    entry.max_rt = rt;
                }
                lk.reset_prefixed(&entry.key, snapshot_seq);
                if let Some((pseq, popt)) = mt.get(&lk) {
                    let value = resolve_multi_get_value(pseq, popt, entry.max_rt);
                    set_multi_get_result(entry, &mut results, value);
                    unresolved -= 1;
                }
            }
        }
        if unresolved == 0 {
            return Ok(results);
        }

        // 2. Frozen memtables, newest first.
        {
            let frozen = &view.frozen;
            for mt in frozen.iter().rev() {
                for entry in &mut entries {
                    if entry.resolved {
                        continue;
                    }
                    let rt = mt.covering_range_tombstone_seq(&entry.key, snapshot_seq);
                    if rt > entry.max_rt {
                        entry.max_rt = rt;
                    }
                    lk.reset_prefixed(&entry.key, snapshot_seq);
                    if let Some((pseq, popt)) = mt.get(&lk) {
                        let value = resolve_multi_get_value(pseq, popt, entry.max_rt);
                        set_multi_get_result(entry, &mut results, value);
                        unresolved -= 1;
                    }
                }
                if unresolved == 0 {
                    return Ok(results);
                }
            }
        }

        let version = &view.version;

        // 3. L0 SSTables, newest first.
        for file in version.levels[0].iter().rev() {
            for entry in &mut entries {
                if entry.resolved || !file_covers_key(file, &entry.key) {
                    continue;
                }
                let rt = file
                    .reader
                    .covering_range_tombstone_seq(&entry.key, snapshot_seq);
                if rt > entry.max_rt {
                    entry.max_rt = rt;
                }
                lk.reset_prefixed(&entry.key, snapshot_seq);
                match with_key_scratch(|buf| file.reader.get(&lk, buf, &self.cache))? {
                    LookupResult::Found { seq, value } => {
                        let value = resolve_multi_get_value(seq, Some(value), entry.max_rt);
                        set_multi_get_result(entry, &mut results, value);
                        unresolved -= 1;
                    }
                    LookupResult::FoundTombstone { .. } => {
                        set_multi_get_result(entry, &mut results, None);
                        unresolved -= 1;
                    }
                    LookupResult::NotInTable => {}
                }
            }
            if unresolved == 0 {
                return Ok(results);
            }
        }

        // 4. L1..Ln: a level is one sorted run, so each key finds the few
        //    tables covering it by binary search rather than being matched
        //    against every table, and a table whose range covers the key
        //    but holds no point entry for it, as a tombstone-only table
        //    does, costs no more than any other. As a single-key read
        //    does, a key sees the tombstones of all its covering tables in
        //    a level before any of them is probed.
        for files in version.levels.iter().skip(1) {
            if files.is_empty() {
                continue;
            }
            for entry in &mut entries {
                if entry.resolved {
                    continue;
                }
                let run = manifest::covering(files, &entry.key);
                for file in run {
                    let rt = file
                        .reader
                        .covering_range_tombstone_seq(&entry.key, snapshot_seq);
                    if rt > entry.max_rt {
                        entry.max_rt = rt;
                    }
                }
                for file in run.iter().filter(|file| file.meta.num_entries > 0) {
                    lk.reset_prefixed(&entry.key, snapshot_seq);
                    match with_key_scratch(|buf| file.reader.get(&lk, buf, &self.cache))? {
                        LookupResult::Found { seq, value } => {
                            let value = resolve_multi_get_value(seq, Some(value), entry.max_rt);
                            set_multi_get_result(entry, &mut results, value);
                            unresolved -= 1;
                            break;
                        }
                        LookupResult::FoundTombstone { .. } => {
                            set_multi_get_result(entry, &mut results, None);
                            unresolved -= 1;
                            break;
                        }
                        LookupResult::NotInTable => {}
                    }
                }
                if unresolved == 0 {
                    return Ok(results);
                }
            }
        }

        Ok(results)
    }

    /// The version the last applied edit published.
    ///
    /// Cheaper than `versions.lock().current()` - one shared lock
    /// acquisition instead of the version set's exclusive one - and it
    /// is the same version, because every [`VersionStore`] guard
    /// publishes what its critical section installed before it
    /// releases the mutex.
    fn published_version(&self) -> Arc<manifest::Version> {
        Arc::clone(&self.view.load().version)
    }

    /// Retire one frozen memtable in one publication. Called only once
    /// its contents are durable in an SSTable the published version
    /// already references, or once they proved to be empty.
    ///
    /// By identity, not by position. The memtable named here is the one
    /// this flush read, and between reading it and getting here the
    /// list can have changed: a rotation appends, and another flush
    /// could have retired ahead of this one. Dropping "index 0" would
    /// then drop somebody else's memtable, whose contents are in no
    /// published version. Retiring a memtable that is already gone is a
    /// no-op, which is what makes this safe to call on every exit path.
    fn retire_frozen(&self, flushed: &Arc<MemTable>) {
        self.view.retire_memtable(flushed);
    }

    /// Unlink the log that backed `flushed`, now that its records are in
    /// an SSTable the published version references.
    ///
    /// Keyed off the memtable rather than off whatever log the caller
    /// happened to seal. A flush and the seal that fed it are not
    /// necessarily about the same memtable: the seal appends to the
    /// frozen list while the flush takes the front of it, and the two
    /// are separated by a whole SSTable write. Unlinking the caller's
    /// log would delete the only durable copy of a memtable that has not
    /// been flushed, and a crash would then lose every write in it.
    fn remove_sealed_wal(&self, flushed: &MemTable) {
        if let Some(path) = flushed.sealed_wal() {
            let _ = Wal::remove_in(&*self.env, path);
        }
    }

    /// Snapshot the current write-stall inputs: L0 file count,
    /// in-memory memtable count (active + frozen), and total bytes
    /// across all L0 files (regolith's approximation of pending
    /// compaction bytes).
    fn stall_snapshot(&self) -> (usize, usize, u64) {
        let view = self.view.load();
        let l0 = view.version.levels[0].len();
        let pending_bytes: u64 = view.version.levels[0]
            .iter()
            .map(|f| f.meta.file_size)
            .sum();
        // The active memtable always counts as 1; frozen memtables
        // are whatever is still waiting for the flush path.
        let memtable_count = 1 + view.frozen.len();
        (l0, memtable_count, pending_bytes)
    }

    /// Classify the current state against the configured stall
    /// thresholds. Returns:
    ///
    /// * `None` - writes may proceed freely.
    /// * `Some(("...", true))` - hard stop: block writers until
    ///   compaction relieves the condition.
    /// * `Some(("...", false))` - slowdown: add a small delay per
    ///   write so the foreground write rate tracks compaction.
    fn stall_state(&self) -> Option<(&'static str, bool)> {
        let (l0, memtables, pending_bytes) = self.stall_snapshot();
        let opts = &self.options;
        // Stop conditions dominate over slowdown. An unconfigured
        // threshold (`0`) disables that particular trigger.
        if opts.level0_stop_writes_trigger > 0 && l0 >= opts.level0_stop_writes_trigger {
            // The L0 *count* triggers are level-style back-pressure:
            // only level compaction reduces the L0 file count in
            // response to them. Under the other two styles the count
            // can sit above the trigger with the picker correctly
            // declining to merge, so name the real cause and the knob
            // rather than pointing the caller at a compaction that
            // provably cannot help.
            return Some((
                match opts.compaction_style {
                    crate::options::CompactionStyle::Level => "stop: too many L0 files",
                    crate::options::CompactionStyle::Fifo => {
                        "stop: too many L0 files, and FIFO compaction never merges them - \
                         set level0_stop_writes_trigger to 0 to disable this level-style \
                         trigger, or lower fifo_compaction_options.max_table_files_size"
                    }
                    crate::options::CompactionStyle::Universal => {
                        "stop: too many L0 files, and the universal picker's size-ratio and \
                         size-amplification rules decline to merge them - set \
                         level0_stop_writes_trigger to 0 to disable this level-style \
                         trigger, or lower \
                         universal_compaction_options.max_size_amplification_percent"
                    }
                },
                true,
            ));
        }
        if opts.max_write_buffer_number > 0
            && memtables >= opts.max_write_buffer_number.saturating_mul(2)
        {
            return Some((STOP_TOO_MANY_MEMTABLES, true));
        }
        if opts.hard_pending_compaction_bytes_limit > 0
            && pending_bytes >= opts.hard_pending_compaction_bytes_limit
        {
            return Some(("stop: pending compaction bytes over hard limit", true));
        }
        if opts.level0_slowdown_writes_trigger > 0 && l0 >= opts.level0_slowdown_writes_trigger {
            return Some(("slowdown: L0 files over trigger", false));
        }
        if opts.max_write_buffer_number > 0 && memtables > opts.max_write_buffer_number {
            return Some(("slowdown: memtables over trigger", false));
        }
        if opts.soft_pending_compaction_bytes_limit > 0
            && pending_bytes >= opts.soft_pending_compaction_bytes_limit
        {
            return Some(("slowdown: pending compaction bytes over soft limit", false));
        }
        None
    }

    /// Fixed per-write slowdown delay. Keeping this small (1 ms)
    /// gives foreground writers a steady back-pressure signal
    /// without freezing progress entirely; compaction gets cycles
    /// to catch up and the writer learns that the engine is under
    /// pressure.
    const SLOWDOWN_DELAY: std::time::Duration = std::time::Duration::from_millis(1);

    /// Block the current writer until the engine is ready to
    /// accept another write, or (when `no_slowdown` is set) return
    /// [`crate::Error::Busy`] immediately if any stall condition is
    /// active. Returns the number of microseconds the caller spent
    /// stalled, which is also published to the
    /// [`crate::statistics::Ticker::WriteStallMicros`] counter.
    /// Refresh the cached stall level from the current L0 /
    /// memtable / pending-bytes state. Called after any event that
    /// changes those counters (memtable rotation, compaction pass).
    pub(crate) fn refresh_stall_level(&self) {
        let level = match self.stall_state() {
            None => 0,
            Some((_, false)) => 1,
            Some((_, true)) => 2,
        };
        self.cached_stall_level.store(level, Ordering::Release);
    }

    /// How long a stalled writer parks before re-checking its
    /// thresholds. The wait is bounded so a missed notification costs
    /// one re-check rather than wedging the writer forever.
    const STALL_WAIT: std::time::Duration = std::time::Duration::from_millis(100);

    /// Park until a compaction pass reports progress, or
    /// [`Self::STALL_WAIT`] elapses.
    ///
    /// Shared by both stall policies: `WaitForWorker` waits on the
    /// background worker, and `CompactInline` waits on whichever other
    /// foreground thread currently holds the input files it needs.
    /// One wait step for a writer stopped behind background work, or the
    /// error that says waiting would not end.
    ///
    /// Too many memtables means flushes are failing: memtables are written
    /// out by the writer that seals them, and no worker retries one that
    /// failed, so a stopped writer that only waited would wait forever,
    /// even after the fault cleared. It retries the oldest flush itself,
    /// unless another thread holds the flush exclusion, and returns that
    /// flush's error if it fails. Any other stop is relieved by
    /// compaction; while the last compaction pass failed, the writer
    /// returns that failure instead of waiting on a retry that is
    /// likely to fail the same way.
    fn wait_out_stop(&self, reason: &'static str) -> Result<(), crate::Error> {
        if reason == STOP_TOO_MANY_MEMTABLES {
            if let Some(flushing) = self.flushing.try_lock() {
                let flushed = self.flush_oldest_frozen(&flushing);
                drop(flushing);
                return match flushed {
                    Ok(_) => {
                        self.refresh_stall_level();
                        self.stall_signal.notify_all();
                        Ok(())
                    }
                    Err(source) => Err(crate::Error::BackgroundFailed {
                        job: Job::Flush.name(),
                        hazard: Hazard::of(&source).label(),
                        source,
                    }),
                };
            }
        } else if let Some(failure) = self.background_health.failing(Job::Compaction) {
            return Err(failure.to_error());
        }
        self.wait_for_stall_signal();
        Ok(())
    }

    fn wait_for_stall_signal(&self) {
        self.stall_signal.wait(Self::STALL_WAIT);
    }

    /// Upper bound on compaction jobs one stalled write will perform on
    /// its own thread before giving up with [`crate::Error::Busy`].
    ///
    /// The bound exists to cap write latency, not to cap iterations for
    /// their own sake: one L0 -> L1 pass normally drains the entire L0
    /// pool, so a caller that needs more than this many passes is not
    /// going to be rescued by another one on this thread.
    const MAX_INLINE_PASSES: usize = 32;

    /// How many times in a row an inline compaction pass may report
    /// nothing to do while a stop-writes threshold is still active,
    /// before the write is failed with [`crate::Error::Busy`].
    ///
    /// Not zero, because another thread can relieve the stall between
    /// this thread's threshold check and its pick, and that races to
    /// an `Idle` that means the opposite of stuck. Small, because a
    /// picker that declines twice running while the threshold holds is
    /// declining for a structural reason (see
    /// [`crate::Options::level0_stop_writes_trigger`]) that another
    /// pass will not change.
    const MAX_IDLE_PASSES: usize = 2;

    /// Run at most one pending compaction job on the calling thread and
    /// report whether any work was done.
    ///
    /// Takes the read side of the engine-wide compaction lock, exactly
    /// as a background worker does, and shares the engine's in-progress
    /// file-id set, so a foreground pass and a worker can never pick
    /// overlapping inputs.
    ///
    /// Lock-order invariant: the caller must not hold `write_lock`.
    /// `ingest_external_files` holds the write side of the compaction
    /// lock while it takes `write_lock`, so acquiring them in the
    /// opposite order here would invert the hierarchy. The stall path
    /// satisfies this because it runs before the write path takes
    /// `write_lock`, never inside it.
    pub(crate) fn run_one_compaction_pass(&self) -> std::io::Result<CompactionOutcome> {
        self.ensure_writable()?;
        let outcome = {
            let _guard = self.compaction_lock.read();
            self.ensure_writable()?;
            compaction::pick_and_run_compaction(
                &self.versions,
                &self.sst_dir,
                &self.cache,
                &self.options.to_compaction_options(),
                &self.snapshot_registry,
                &self.compaction_in_progress,
            )?
        };
        // Mirror the worker loop's post-pass work so a writer parked on
        // the condvar in `WaitForWorker` mode re-checks its thresholds.
        self.stall_signal.notify_all();
        self.refresh_stall_level();
        Ok(outcome)
    }

    /// Write every memtable currently held in memory out to level-0
    /// SSTables on the calling thread. A no-op when nothing is held.
    ///
    /// Shares [`Self::flush_all_memtables`] with the close path, so an
    /// explicit flush and a close write memtables out the same way.
    pub(crate) fn flush_active_memtable(&self) -> std::io::Result<()> {
        self.ensure_writable()?;
        self.drain_memtables(ActiveFlush::Always)?;
        self.refresh_stall_level();
        Ok(())
    }

    // Not closed and no cached stall is the overwhelming common case, so
    // this fast check stays inlined at every call site rather than a call
    // instruction: two byte loads and two branches over state the engine
    // already keeps resident (`close_state`, `cached_stall_level`), which
    // also skips the `stall_state()` call that loads the read view and
    // walks L0. Anything past that is parking or an inline compaction
    // pass, so it is cold and kept out of line instead of bloating every
    // caller that never stalls.
    #[inline]
    pub(crate) fn wait_for_write_capacity(&self, no_slowdown: bool) -> Result<u64, crate::Error> {
        if !self.is_closed() && self.cached_stall_level.load(Ordering::Acquire) == 0 {
            return Ok(0);
        }
        self.wait_for_write_capacity_slow(no_slowdown)
    }

    #[cold]
    #[inline(never)]
    fn wait_for_write_capacity_slow(&self, no_slowdown: bool) -> Result<u64, crate::Error> {
        if self.is_closed() {
            return Err(crate::Error::Closed);
        }

        let start = self.env.now_micros();
        let mut any_stall = false;
        let mut inline_passes = 0usize;
        let mut idle_passes = 0usize;

        loop {
            if self.is_closed() {
                return Err(crate::Error::Closed);
            }
            match self.stall_state() {
                None => {
                    // Stall cleared - update the cache so
                    // subsequent writers take the fast path.
                    self.cached_stall_level.store(0, Ordering::Release);
                    break;
                }
                Some((reason, true)) => {
                    if no_slowdown {
                        return Err(crate::Error::Busy(reason));
                    }
                    any_stall = true;
                    match self.stall_policy {
                        StallPolicy::WaitForWorker => self.wait_out_stop(reason)?,
                        StallPolicy::CompactInline => {
                            match self.run_one_compaction_pass()? {
                                // Files came out of L0; the next
                                // `stall_state()` sees it. Only real
                                // work counts against the budget,
                                // because only real work is latency
                                // this thread is paying for.
                                CompactionOutcome::DidWork => {
                                    idle_passes = 0;
                                    inline_passes += 1;
                                    if inline_passes > Self::MAX_INLINE_PASSES {
                                        return Err(crate::Error::Busy(reason));
                                    }
                                }
                                // Another thread already holds the
                                // inputs this writer needs. That thread
                                // *is* the worker here, and it notifies
                                // this signal when its job ends, so
                                // wait for it exactly as
                                // `WaitForWorker` does. Waiting is not
                                // charged to the inline budget: a
                                // contended wait is bounded by the
                                // holder's job, which always terminates
                                // and always deregisters, after which
                                // this thread sees `DidWork` from its
                                // own pass or `Idle` and gives up.
                                CompactionOutcome::Contended => {
                                    idle_passes = 0;
                                    self.wait_for_stall_signal();
                                }
                                // Idle is ambiguous under
                                // concurrency: it means "nothing to
                                // compact right now", which is what a
                                // wedged engine looks like *and* what
                                // an engine another thread just
                                // relieved looks like. Re-check the
                                // thresholds from the top instead of
                                // failing a write that no longer needs
                                // to fail. Bounded so the genuinely
                                // unrelievable case still returns
                                // rather than spinning: a picker that
                                // declines this many times in a row
                                // while the stall persists is not
                                // going to change its mind.
                                CompactionOutcome::Idle => {
                                    idle_passes += 1;
                                    if idle_passes > Self::MAX_IDLE_PASSES {
                                        return Err(crate::Error::Busy(reason));
                                    }
                                }
                            }
                        }
                    }
                }
                Some((reason, false)) => {
                    if no_slowdown {
                        return Err(crate::Error::Busy(reason));
                    }
                    any_stall = true;
                    match self.stall_policy {
                        StallPolicy::WaitForWorker => self.env.sleep(Self::SLOWDOWN_DELAY),
                        // Sleeping accomplishes nothing with no worker.
                        // The writer pays one compaction job instead,
                        // which is what makes the write rate track
                        // compaction on a single-threaded host.
                        StallPolicy::CompactInline => {
                            self.run_one_compaction_pass()?;
                        }
                    }
                    // One slowdown delay per call - don't loop, or
                    // a writer that just crossed the trigger would
                    // stall indefinitely at low rates.
                    break;
                }
            }
        }

        // No monotonic clock means nothing was measured. The ticker
        // stays untouched rather than gaining a fabricated zero, and
        // the caller is told the same thing.
        let micros = self.elapsed_micros(start);
        if any_stall && let (Some(micros), Some(s)) = (micros, self.statistics()) {
            s.add(crate::statistics::Ticker::WriteStallMicros, micros);
        }
        Ok(micros.unwrap_or(0))
    }

    pub(crate) fn commit_with_conflict_check(
        &self,
        checks: &ValidationSet,
        point_ops: BTreeMap<Vec<u8>, Option<Vec<u8>>>,
        range_deletes: Vec<(Vec<u8>, Vec<u8>)>,
        merges: Vec<(Vec<u8>, Vec<u8>)>,
        appends: Vec<PendingAppend>,
        durability: DurabilityMode,
    ) -> std::io::Result<CommitOutcome> {
        self.commit_optimistic(
            checks,
            point_ops,
            range_deletes,
            merges,
            appends,
            durability,
        )
    }

    /// Whether this commit's write for `key` would store exactly what `key`
    /// already holds.
    ///
    /// Such a write is not a conflict. Take two transactions that both write
    /// `K = v`, with the first committing: under the serial order "first, then
    /// second" the second writes `K = v` and the final state is `K = v`, which
    /// is what letting both commit produces. The schedule has a serial
    /// equivalent, so refusing it rejects a correct history.
    ///
    /// The comparison is against the *committed* value, not against what the
    /// transaction observed, and byte equality is the whole test: "the key
    /// exists" is not enough. A delete is equal only to an absent key.
    ///
    /// Only ever called on a key that was about to abort the commit, so the
    /// read it costs is paid on the failure path and never on a clean commit.
    fn write_matches_committed(
        &self,
        key: &[u8],
        ops: &[WriteBatchOp],
        view: &ReadView,
        newest: WriteKind,
    ) -> std::io::Result<bool> {
        // Unresolved merge operands on top mean a point read replays them, so
        // what it returns is not what this key stores. Beneath a newest value
        // or deletion, any operands are already folded and the read is exact.
        if newest == WriteKind::Merge {
            return Ok(false);
        }

        let mut intended: Option<Option<&[u8]>> = None;
        for op in ops {
            match op {
                WriteBatchOp::Put { key: op_key, value } if op_key == key => {
                    intended = Some(Some(value.as_slice()));
                }
                WriteBatchOp::Delete { key: op_key } if op_key == key => {
                    intended = Some(None);
                }
                // A merge is not idempotent: two `+1` operands are not one
                // `+1`, so a merge on this key always conflicts.
                WriteBatchOp::Merge { key: op_key, .. } if op_key == key => return Ok(false),
                // A range delete makes the key's final value a function of the
                // range as well as the point op, which this comparison does
                // not model.
                WriteBatchOp::DeleteRange { start, end }
                    if start.as_slice() <= key && key < end.as_slice() =>
                {
                    return Ok(false);
                }
                _ => {}
            }
        }

        // No write for this key means it is here because the transaction read
        // it, and a read that no longer holds has to abort.
        let Some(intended) = intended else {
            return Ok(false);
        };

        self.committed_equals(key, intended, view)
    }

    /// [`Self::committed_equals`] for a key whose newest version is `newest`:
    /// an operand on top means a read replays it, so what the key stores is
    /// not what a lookup of its value returns, and the write never matches.
    fn committed_equals_after(
        &self,
        key: &[u8],
        intended: Option<&[u8]>,
        view: &ReadView,
        newest: WriteKind,
    ) -> std::io::Result<bool> {
        if newest == WriteKind::Merge {
            return Ok(false);
        }
        self.committed_equals(key, intended, view)
    }

    /// Whether `key` holds exactly `intended` (`None`: nothing) in `view`,
    /// whose newest version is a value or a deletion, never an operand.
    fn committed_equals(
        &self,
        key: &[u8],
        intended: Option<&[u8]>,
        view: &ReadView,
    ) -> std::io::Result<bool> {
        let snap = u64::MAX;
        let lk = LookupKey::from_prefixed(key, snap);
        let committed = self.lookup_in_view(key, snap, &lk, Materialize::Value, view)?;
        let committed = match committed {
            Some(PointValue::Value(slice)) => Some(slice),
            Some(PointValue::Length(_)) => return Ok(false),
            None => None,
        };

        Ok(match (intended, committed.as_deref()) {
            (Some(intended), Some(committed)) => intended == committed,
            // A delete of a key that is already absent stores the same thing.
            (None, None) => true,
            _ => false,
        })
    }

    /// Return the sequence number and kind of the newest write that
    /// touched `key` across every source, or `None` if nothing ever wrote
    /// it. A covering range tombstone that outranks every point entry
    /// reports as a range delete.
    /// Used by transaction commit to detect conflicts, so it counts
    /// every kind of write: point entries, point tombstones, merge
    /// operands, and range tombstones that cover the key. The caller
    /// only needs to know "was this key written to again?".
    ///
    /// Sources are visited newest-first and range-tombstone coverage
    /// is accumulated on the way down, mirroring the read path: a
    /// tombstone in a newer source outranks a point entry found in an
    /// older one.
    #[inline]
    fn latest_version_in_view(
        &self,
        key: &[u8],
        view: &ReadView,
    ) -> std::io::Result<Option<(u64, WriteKind)>> {
        self.latest_version_upto(key, u64::MAX, view)
    }

    /// [`Self::latest_version_in_view`] among the writes at or below `snap`,
    /// for a check that runs without the pipeline mutex and so must not see
    /// a group that is still being published.
    fn latest_version_upto(
        &self,
        key: &[u8],
        snap: u64,
        view: &ReadView,
    ) -> std::io::Result<Option<(u64, WriteKind)>> {
        let lk = LookupKey::from_prefixed(key, snap);
        let walked = view.walk_newest_first(key, snap, |source, max_rt_seq| {
            let version = match source {
                Source::Memtable(mt) => mt.latest_version(&lk),
                Source::Table(reader) => {
                    with_key_scratch(|buf| reader.latest_version(&lk, buf, &self.cache))?
                }
            };
            // A covering range tombstone that outranks the point entry
            // stands in for it.
            Ok(match version {
                Some((point_seq, _)) if max_rt_seq > point_seq => {
                    ControlFlow::Break((max_rt_seq, WriteKind::RangeDelete))
                }
                Some((seq, value_type)) => {
                    ControlFlow::Break((seq, internal_key::write_kind(value_type)))
                }
                None => ControlFlow::Continue(()),
            })
        })?;
        Ok(match walked {
            ControlFlow::Break(version) => Some(version),
            ControlFlow::Continue(max_rt_seq) => {
                (max_rt_seq > 0).then_some((max_rt_seq, WriteKind::RangeDelete))
            }
        })
    }

    /// Rotate the active memtable when it has reached the write-buffer
    /// size. Called at the *start* of a write path so that a rotation
    /// failure is surfaced before the write is assigned a sequence or
    /// applied - keeping write errors determinate: a returned error means
    /// the write did not land, never that it landed but a later step
    /// failed. Caller must hold the pipeline mutex.
    ///
    /// Takes the view the leader already loaded and hands back the view the
    /// group applies into: the same one when nothing rotated, a fresh load
    /// otherwise. The active memtable changes only under the pipeline mutex,
    /// so between the two nothing else can have replaced it.
    fn rotate_if_full<'v>(&'v self, view: ViewGuard<'v>) -> std::io::Result<ViewGuard<'v>> {
        if view.active.approximate_size() < self.options.write_buffer_size {
            return Ok(view);
        }
        // Released before the rotation publishes, so the views it retires
        // are handed to the reclaimer at once rather than when this group
        // is done (see `read_view::quiesce`).
        drop(view);
        self.rotate_memtable()?;
        Ok(self.view.load())
    }

    fn rotate_memtable(&self) -> std::io::Result<()> {
        let sealed = self.seal_active()?;
        let flushed = self.flush_until_retired(&sealed);
        // Even when the flush failed: the memtable it left frozen counts
        // toward the stall thresholds, and skipping the refresh would let
        // writers keep sealing memtables, without back-pressure, for as
        // long as flushes keep failing.
        self.refresh_stall_level();
        flushed
    }

    /// Move the active memtable to the frozen list behind a fresh one and
    /// a fresh WAL, and return it. Caller must hold the pipeline mutex.
    fn seal_active(&self) -> std::io::Result<Arc<MemTable>> {
        self.ensure_writable()?;
        // Everything fallible happens before the publication, so a rotation
        // that fails leaves the view as it was.
        let fresh = Arc::new(MemTable::new(&self.memtable_config)?);
        let new_wal_id = {
            let mut versions = self.versions.lock();
            let version = versions.current();
            let id = version.next_file_id;
            versions.apply(&[VersionEdit::SetNextFileId(id + 1)])?;
            id
        };
        let old_wal = self.swap_wal(new_wal_id)?;

        // One publication: the sealed memtable joins `frozen` in the
        // same view that hands writers the fresh active one, so no
        // reader can catch it in neither.
        let sealed = self.view.update_memtables(|active, frozen| {
            let sealed = Arc::clone(active);
            let mut next_frozen = frozen.to_vec();
            next_frozen.push(Arc::clone(&sealed));
            (Arc::clone(&fresh), next_frozen, sealed)
        });
        sealed.seal_seq(self.latest_seq.load(Ordering::Acquire));

        self.wal_id.store(new_wal_id, Ordering::Release);
        // The log that was active while `sealed` took writes is the one
        // `sealed`'s records are in, and the only durable copy of them
        // until a flush publishes an SSTable. Stamping it on the
        // memtable is what lets that flush unlink the right one.
        sealed.seal_wal(old_wal.path().to_path_buf());
        Ok(sealed)
    }

    /// Flush frozen memtables, oldest first, until `target` is no
    /// longer in the frozen list.
    ///
    /// The caller names the memtable it needs durable rather than a
    /// count of passes, so a concurrent rotation cannot extend the work
    /// and a concurrent flush that already retired the target ends it
    /// early. Each pass takes the oldest frozen memtable, whoever asked:
    /// L0 files carry no sequence of their own and readers take the
    /// most recently added as the newest, so flushing out of order would
    /// publish an older file over a newer one and make a read travel
    /// backwards.
    ///
    /// Each pass takes the `flushing` exclusion and releases it before the
    /// next.
    fn flush_until_retired(&self, target: &Arc<MemTable>) -> std::io::Result<()> {
        while self
            .view
            .load()
            .frozen
            .iter()
            .any(|mt| Arc::ptr_eq(mt, target))
        {
            if !self.flush_oldest_frozen(&self.flushing.lock())? {
                break;
            }
        }
        Ok(())
    }

    /// Write the oldest frozen memtable out to an L0 SSTable and retire
    /// it. Returns `false` when there was nothing frozen to flush.
    ///
    /// The caller holds `flushing` and passes its guard, which is the
    /// only way to call this. Serialized against itself. The exclusion
    /// is not protecting shared state, which the read view already
    /// publishes atomically: it is what keeps L0 installs in the order
    /// the memtables were sealed, because the format gives an L0 file no
    /// sequence of its own and recency is install order. Two flushes
    /// racing would install a newer file under an older one, and a read
    /// that had seen the newer version would then see the older one.
    fn flush_oldest_frozen(&self, flushing: &MutexGuard<'_, ()>) -> std::io::Result<bool> {
        match self.flush_oldest_frozen_inner(flushing) {
            Ok(flushed) => {
                self.background_health.record_success(Job::Flush);
                Ok(flushed)
            }
            Err(e) => {
                let hazard = self.background_health.record_failure(Job::Flush, &e);
                tracing::error!(error = %e, hazard = hazard.label(), "Flush failed");
                if !self.options.listeners.is_empty() {
                    let err = crate::Error::from(crate::Error::clone_io(&e));
                    crate::event_listener::dispatch_contained(&self.options.listeners, |l| {
                        l.on_background_error(
                            crate::event_listener::BackgroundErrorReason::Flush,
                            &err,
                        )
                    })
                    .map_err(crate::Error::into_io_error)?;
                }
                Err(e)
            }
        }
    }

    fn flush_oldest_frozen_inner(&self, _flushing: &MutexGuard<'_, ()>) -> std::io::Result<bool> {
        // Through the env: a target with no monotonic clock reports
        // nothing measured rather than a fabricated duration.
        let flush_start = self.env.now_micros();
        let memtable = match self.view.load().frozen.first() {
            Some(mt) => Arc::clone(mt),
            None => return Ok(false),
        };

        let range_tombstones = memtable.clone_range_tombstones();

        if memtable.is_empty() && range_tombstones.is_empty() {
            self.retire_frozen(&memtable);
            self.remove_sealed_wal(&memtable);
            return Ok(true);
        }

        let file_id = {
            let mut versions = self.versions.lock();
            let version = versions.current();
            let id = version.next_file_id;
            versions.apply(&[VersionEdit::SetNextFileId(id + 1)])?;
            id
        };

        let sst_path = self.sst_dir.join(sst_filename(file_id));
        // Until the edit below is offered to the manifest, nothing else
        // knows this file exists: every early return must unlink it, or a
        // flush that keeps failing leaks a memtable-sized file per retry.
        let mut pending = PendingOutputs::new(Arc::clone(&self.env));
        pending.track(sst_path.clone());

        // Memtable flushes always land at L0 - pick L0's codec.
        let mut writer = SsTableWriter::new_in(
            &self.env,
            &sst_path,
            self.options.block_size,
            self.options.bloom_bits_per_key,
            self.options.compression_for_level(0),
            self.options.prefix_extractor.clone(),
            self.options.partitioned_index,
            self.options.metadata_block_size,
        )?;

        // Walk the memtable in internal-key order and copy every version
        // and tombstone into the SSTable unchanged, preserving MVCC.
        // The walk streams straight out of the arena: a flush holds one
        // entry plus the block builder, never a second copy of the
        // whole memtable.
        let mut walk =
            || memtable.try_for_each_entry(|internal_key, value| writer.add(internal_key, value));
        // Only a prefix extractor runs caller code in the walk, so only then
        // is there a panic to catch.
        if self.options.prefix_extractor.is_some() {
            callback::contain("PrefixExtractor", walk).map_err(crate::Error::into_io_error)??;
        } else {
            walk()?;
        }

        // Persist range tombstones alongside the point entries.
        for rt in &range_tombstones {
            writer.add_range_tombstone(&rt.start, &rt.end, rt.seq);
        }

        let summary = match writer.finish()? {
            Some(s) => s,
            None => {
                self.retire_frozen(&memtable);
                self.remove_sealed_wal(&memtable);
                let _ = self.env.remove_file(&sst_path);
                return Ok(true);
            }
        };

        let file_size = self.env.metadata(&sst_path)?.len;
        let num_entries = summary.num_entries;

        // Throttle background I/O so bursts of flush writes don't
        // starve foreground traffic. Rate-limiting is opt-in via
        // `Options::rate_limiter`; a `None` limiter is a no-op.
        if let Some(limiter) = &self.options.rate_limiter {
            callback::contain("RateLimiter", || {
                limiter.request(file_size, crate::rate_limiter::Priority::Low)
            })
            .map_err(crate::Error::into_io_error)?;
        }

        let reader = Arc::new(SsTableReader::open_with(
            &self.env,
            &sst_path,
            file_id,
            self.options.metadata_policy(),
        )?);
        let file = LiveSst::new(
            SsTableMeta {
                file_id,
                smallest_key: summary.smallest_user_key,
                largest_key: summary.largest_user_key,
                file_size,
                num_entries,
                global_seq: None,
            },
            reader,
        );

        // The sequence this memtable was sealed at, not the engine's
        // current one. `last_seq` is read back as "every write at or
        // below this is in an SSTable", and a checkpoint copies tables
        // and no WAL, so stamping the global counter here would make a
        // checkpoint claim writes that are still only in a memtable it
        // did not flush.
        let seq = memtable
            .sealed_seq()
            .unwrap_or_else(|| self.latest_seq.load(Ordering::Acquire));
        let edits = vec![
            VersionEdit::AddFile { level: 0, file },
            VersionEdit::SetLastSeq(seq),
        ];
        pending.offered_to_manifest();
        self.versions.lock().apply(&edits)?;

        // Retired only now: until the `AddFile` above is published, the
        // flushed data lives in this memtable alone.
        self.retire_frozen(&memtable);
        self.remove_sealed_wal(&memtable);
        self.compaction.lock().notify();

        // Publish flush statistics before the listener dispatch
        // so callers that react to `on_flush_completed` can
        // already see the updated tickers.
        if let Some(s) = self.statistics() {
            s.add(crate::statistics::Ticker::FlushCount, 1);
            s.add(crate::statistics::Ticker::FlushBytesWritten, file_size);
            if let Some(micros) = self.elapsed_micros(flush_start) {
                s.record(crate::statistics::Histogram::FlushTime, micros);
            }
        }

        // Dispatch lifecycle events to any registered listeners.
        // Two callbacks fire per flush: `on_table_file_created`
        // for the new SSTable and `on_flush_completed` with
        // memtable-level aggregates.
        if !self.options.listeners.is_empty() {
            let (smallest, largest) = {
                // Version was just applied; pull the newly-added
                // file's metadata back out so listeners see the
                // exact bounds the engine committed.
                let ver = self.versions.lock().current();
                if let Some(added) = ver.levels[0].iter().find(|f| f.meta.file_id == file_id) {
                    (
                        added.meta.smallest_key.clone(),
                        added.meta.largest_key.clone(),
                    )
                } else {
                    (Vec::new(), Vec::new())
                }
            };
            // Zero where the platform has no monotonic clock; the
            // `FlushJobInfo::duration` doc says so.
            let duration =
                std::time::Duration::from_micros(self.elapsed_micros(flush_start).unwrap_or(0));
            let create_info = event_listener::TableFileCreationInfo {
                file_id,
                file_path: sst_path.clone(),
                level: 0,
                reason: event_listener::TableFileCreationReason::Flush,
                file_size,
                num_entries,
            };
            let flush_info = event_listener::FlushJobInfo {
                file_id,
                file_path: sst_path.clone(),
                file_size,
                num_entries,
                smallest_key: smallest,
                largest_key: largest,
                duration,
            };
            event_listener::dispatch_contained(&self.options.listeners, |l| {
                l.on_table_file_created(&create_info)
            })
            .map_err(crate::Error::into_io_error)?;
            event_listener::dispatch_contained(&self.options.listeners, |l| {
                l.on_flush_completed(&flush_info)
            })
            .map_err(crate::Error::into_io_error)?;
        }

        tracing::info!(
            file_id,
            entries = num_entries,
            size = file_size,
            "Flushed memtable to L0 SSTable"
        );

        Ok(true)
    }

    /// Synchronously compact SSTables overlapping the user-key range
    /// `[start, end)` down to the bottommost non-empty level.
    ///
    /// - Acquires the engine-wide compaction lock so the background
    ///   scheduler can't pick an overlapping input set concurrently.
    /// - Flushes the active memtable first so any matching in-memory
    ///   data reaches L0 before compaction picks inputs.
    /// - Walks levels 0..MAX_LEVELS-1, picking range-overlapping files
    ///   and merging them into the next level.
    pub(crate) fn compact_range(
        &self,
        start: Option<&[u8]>,
        end: Option<&[u8]>,
    ) -> std::io::Result<()> {
        self.ensure_writable()?;
        // 1. Exclude all background workers for the duration of the
        //    range walk. Write lock blocks until every in-flight
        //    background pass releases its read lock. Taken before the
        //    flush below, in the `compaction_lock -> pipeline` order an
        //    ingest and `drop_all` take too.
        let _compact_guard = self.compaction_lock.write();
        self.ensure_writable()?;

        // 2. Flush the active memtable so any in-memory data that
        //    overlaps the range is materialized in L0. We only touch
        //    the write lock if there's actually data to flush. "Data"
        //    here includes range tombstones, not just point entries.
        let needs_flush = |mt: &MemTable| !mt.is_empty() || mt.has_range_tombstones();
        if needs_flush(&self.view.load().active) {
            let _write_guard = self.pipeline.lock();
            if needs_flush(&self.view.load().active) {
                self.rotate_memtable()?;
            }
        }

        // 3. Run the level-by-level push-down.
        let compaction_opts = self.options.to_compaction_options();
        // Under FIFO compaction there is no level push-down; a
        // synchronous compact_range just flushes the memtable and
        // runs the FIFO picker so any pending files over the cap
        // get dropped deterministically.
        if matches!(
            self.options.compaction_style,
            crate::options::CompactionStyle::Fifo
        ) {
            let _ = compaction::run_fifo_pass(&self.versions, &self.sst_dir, &compaction_opts)?;
            return Ok(());
        }

        // Under Universal compaction a manual compact_range folds
        // every L0 file into one run, matching the "force full
        // compaction" semantics a caller expects.
        if matches!(
            self.options.compaction_style,
            crate::options::CompactionStyle::Universal
        ) {
            compaction::run_universal_full_compaction(
                &self.versions,
                &self.sst_dir,
                &self.cache,
                &compaction_opts,
                &self.snapshot_registry,
            )?;
            return Ok(());
        }

        compaction::run_compact_range(
            &self.versions,
            &self.sst_dir,
            &self.cache,
            &compaction_opts,
            start,
            end,
            &self.snapshot_registry,
        )
    }

    /// Atomically capture a consistent snapshot of the on-disk state
    /// for checkpoint / backup purposes.
    ///
    /// Flushes the active memtable (if non-empty) under the write
    /// lock so every live byte is in an SSTable, compacts the
    /// manifest so the on-disk form is a single rewrite of the
    /// current version, and returns the captured `Arc<Version>` plus
    /// the paths of the files a caller needs to copy or hard-link.
    ///
    /// The returned [`CheckpointSnapshot`] holds the engine's
    /// compaction lock, pinning every referenced file against
    /// concurrent unlink. Callers MUST drop the snapshot as soon as
    /// their filesystem work is done - a snapshot whose lifetime
    /// outlives the enclosing function scope can deadlock a
    /// concurrent `db.close()` / `drop(db)` that joins the background
    /// compaction thread (the thread will block on the same lock the
    /// snapshot holds).
    pub(crate) fn checkpoint_capture(&self) -> std::io::Result<CheckpointSnapshot> {
        self.ensure_writable()?;
        // Drain, do not merely seal. A checkpoint captures the SSTables
        // the current version names and copies no WAL, so a memtable that
        // is still waiting on a background flush would be missing from
        // the result entirely. Done before the compaction lock is taken,
        // because flushing needs it.
        self.drain_memtables(ActiveFlush::Always)?;

        let compaction_guard = Gate::write_owned(&self.compaction_lock);
        self.ensure_writable()?;

        let version;
        let manifest_bytes;
        {
            let mut versions = self.versions.lock();
            // Rewritten first, so what is captured is the canonical form
            // of exactly this version rather than a log of every edit
            // that ever reached it.
            versions.compact_manifest()?;
            version = versions.current();
            // Read here, under the same lock that produced `version`, so
            // the two cannot disagree. A concurrent flush takes this lock
            // but not the compaction lock held above, so it is free to
            // append `AddFile` records naming files this checkpoint will
            // not copy, and a rewrite can replace the file entirely.
            let path = versions.manifest_path().to_path_buf();
            manifest_bytes = self.env.read(&path)?;
        }

        Ok(CheckpointSnapshot {
            version,
            manifest_bytes,
            sst_dir: self.sst_dir.clone(),
            _compaction_guard: compaction_guard,
        })
    }

    /// Approximate on-disk bytes whose user key falls in
    /// `[start, end)`. Fans out over every SSTable whose own
    /// user-key range overlaps the query range and sums their
    /// per-range estimates. Index-only - no data-block decompression
    /// happens, so the cost scales with `num_files * log(num_blocks)`.
    pub(crate) fn approximate_size_in_range(&self, start: &[u8], end: &[u8]) -> u64 {
        if start >= end {
            return 0;
        }
        let version = self.published_version();
        let mut total: u64 = 0;
        for level in &version.levels {
            for file in level {
                if file.meta.largest_key.as_slice() < start {
                    continue;
                }
                if file.meta.smallest_key.as_slice() >= end {
                    continue;
                }
                total += file
                    .reader
                    .approximate_size_in_range(start, end, &self.cache);
            }
        }
        total
    }

    /// Exact `(count, size)` for every entry in the active memtable
    /// whose user key falls in `[start, end)`. Frozen memtables are
    /// *not* included - a caller that wants "everything in memory"
    /// should call this and also walk the frozen memtables
    /// separately.
    pub(crate) fn approximate_memtable_stats(&self, start: &[u8], end: &[u8]) -> (u64, u64) {
        self.view
            .load()
            .active
            .approximate_stats_for_range(start, end)
    }

    // ── property helpers ───────────────────────────────────────────────
    //
    // These return raw values consumed by `Db::get_property` /
    // `Db::get_int_property`. Every method is cheap - no block
    // reads, no locks held beyond a short `versions.lock()` or
    // memtable read.

    /// Number of SSTable files at a specific level. Returns 0 for
    /// out-of-range levels rather than panicking, so
    /// `regolith.num-files-at-level<N>` for unknown levels reads
    /// cleanly as `Some(0)`.
    pub(crate) fn num_files_at_level(&self, level: usize) -> u64 {
        let version = self.published_version();
        version
            .levels
            .get(level)
            .map(|files| files.len() as u64)
            .unwrap_or(0)
    }

    /// Total size in bytes across every level of the current
    /// version - sum of every `LiveSst::meta.file_size`.
    pub(crate) fn total_sst_size(&self) -> u64 {
        let version = self.published_version();
        version
            .levels
            .iter()
            .flat_map(|level| level.iter())
            .map(|f| f.meta.file_size)
            .sum()
    }

    /// Total `num_entries` across every current SSTable. The
    /// manifest tracks this per file at ingest / flush /
    /// compaction time, so the sum is free to compute.
    pub(crate) fn total_sst_num_entries(&self) -> u64 {
        let version = self.published_version();
        version
            .levels
            .iter()
            .flat_map(|level| level.iter())
            .map(|f| f.meta.num_entries)
            .sum()
    }

    /// Approximate size of the active memtable (sum of every
    /// inserted internal key + value length seen so far; tracked
    /// by the memtable itself).
    pub(crate) fn active_memtable_size(&self) -> u64 {
        self.view.load().active.approximate_size() as u64
    }

    /// Bytes every in-memory memtable actually reserved from the global
    /// allocator: the sum of their arena chunk sizes plus the heap their
    /// range tombstones own.
    ///
    /// [`RegolithEngine::active_memtable_size`] is the payload figure that
    /// `write_buffer_size` bounds; this is what the process is really
    /// holding, so the gap between them is the arena's rounding waste.
    pub(crate) fn memtables_reserved_size(&self) -> u64 {
        let active = self.view.load().active.reserved_size() as u64;
        let frozen: u64 = self
            .view
            .load()
            .frozen
            .iter()
            .map(|mt| mt.reserved_size() as u64)
            .sum();
        active + frozen
    }

    /// Bytes parked in the memtable arena's recycling pool, waiting to
    /// back the next memtable instead of being returned to the global
    /// allocator. Bounded by
    /// `write_buffer_size * max_write_buffer_number`.
    pub(crate) fn arena_pool_size(&self) -> u64 {
        self.memtable_config.pool_bytes().0 as u64
    }

    /// Total approximate size of every frozen memtable.
    pub(crate) fn frozen_memtables_size(&self) -> u64 {
        self.view
            .load()
            .frozen
            .iter()
            .map(|mt| mt.approximate_size() as u64)
            .sum()
    }

    /// Number of live snapshots. Counts pins, not distinct seqs -
    /// two snapshots taken at the same seq contribute two.
    pub(crate) fn live_snapshot_count(&self) -> u64 {
        self.snapshot_registry.live_count()
    }

    /// Total bytes currently held by the block cache across all
    /// shards. Used by the `regolith.block-cache-usage` property.
    pub(crate) fn block_cache_usage(&self) -> usize {
        self.cache.usage()
    }

    /// Block cache capacity in bytes (the sum of every shard's
    /// budget). Used by the `regolith.block-cache-capacity`
    /// property.
    pub(crate) fn block_cache_capacity(&self) -> usize {
        self.cache.capacity()
    }

    pub(crate) fn background_error_count(&self) -> u64 {
        self.background_health.error_count()
    }

    /// Free and total space on the filesystem holding the database, read
    /// now. `None` where the environment cannot say.
    pub(crate) fn disk_space(&self) -> Option<crate::env::DiskSpace> {
        self.env.disk_space(&self.sst_dir).ok().flatten()
    }

    /// Bytes the currently-live SSTable readers hold *outside* the
    /// block cache budget: pinned indexes, pinned filter regions, any
    /// metadata block the cache refused, and range tombstones.
    ///
    /// This is the honest counterpart to `regolith.block-cache-usage`:
    /// together they account for every byte of SSTable metadata the
    /// engine is holding. With
    /// [`Options::cache_index_and_filter_blocks`] off this number grows
    /// with the number of open files; with it on, only the pinned
    /// top-level index of each partitioned file and its range
    /// tombstones remain here.
    ///
    /// [`Options::cache_index_and_filter_blocks`]: crate::Options::cache_index_and_filter_blocks
    pub(crate) fn pinned_metadata_bytes(&self) -> usize {
        let version = self.versions.lock().current();
        version
            .levels
            .iter()
            .flat_map(|level| level.iter())
            .map(|file| file.reader.pinned_metadata_bytes())
            .sum()
    }

    /// Unix-seconds timestamp of the oldest live snapshot, or
    /// `None` when no snapshot is alive.
    pub(crate) fn oldest_snapshot_time_unix(&self) -> Option<u64> {
        self.snapshot_registry.oldest_snapshot_time_unix()
    }

    /// Borrow the current version so a caller can walk every
    /// SSTable's metadata - used by `regolith.sstables` formatter.
    pub(crate) fn current_version(&self) -> Arc<manifest::Version> {
        self.published_version()
    }

    /// Drop all data in the engine.
    pub(crate) fn drop_all(&self) -> std::io::Result<()> {
        self.ensure_writable()?;
        // Exclude background compaction for the whole drop, as
        // `compact_range`, `ingest_external_files` and `checkpoint_capture`
        // do. Without it a worker holding the read side runs straight
        // through the `Reset` below and then applies its `AddFile`, which
        // `VersionSet::apply` lays over whatever version is current: a file
        // full of pre-drop rows lands in the freshly emptied version, and
        // `remove_obsolete_sst_files` cannot unlink it because the pre-drop
        // version never named it. The drop reports success and the data is
        // still there, across a reopen.
        //
        // Taken before `pipeline`, matching the `compaction_lock ->
        // write_lock` order documented on `run_one_compaction_pass`.
        let _compact_guard = self.compaction_lock.write();
        let _write_guard = self.pipeline.lock();
        self.ensure_writable()?;

        // Published before the version `Reset` below, so no reader can
        // see the pre-drop memtables against the post-drop version.
        // `drop_all` holds `write_lock`, which excludes writers but not
        // readers: a concurrent reader may still briefly observe
        // pre-drop SSTable data, exactly as before this view existed.
        let fresh = Arc::new(MemTable::new(&self.memtable_config)?);
        self.view
            .update_memtables(|_, _| (Arc::clone(&fresh), Vec::new(), ()));

        let (old_version, wal_id, wal_path, new_wal) = {
            let mut versions = self.versions.lock();
            let old_version = versions.current();
            let id = old_version.next_file_id;
            let wal_path = self.wal_dir.join(wal_filename(id));
            let new_wal = Wal::create_in(&self.env, &wal_path)?;
            versions.apply(&[VersionEdit::Reset {
                next_file_id: id + 1,
                min_wal_id: id,
            }])?;
            (old_version, id, wal_path, new_wal)
        };

        self.cache.clear();
        let _old_wal = self.active_wal.lock().replace(new_wal);
        self.wal_id.store(wal_id, Ordering::Release);
        self.latest_seq.store(0, Ordering::Release);
        self.visible_seq.reset();

        self.versions.lock().compact_manifest().map_err(|e| {
            std::io::Error::new(e.kind(), format!("drop_all rewriting manifest: {e}"))
        })?;

        remove_obsolete_sst_files(&*self.env, &self.sst_dir, &old_version).map_err(|e| {
            std::io::Error::new(e.kind(), format!("drop_all removing sstables: {e}"))
        })?;
        remove_obsolete_wal_files(&*self.env, &self.wal_dir, &wal_path)
            .map_err(|e| std::io::Error::new(e.kind(), format!("drop_all removing wals: {e}")))?;

        Ok(())
    }

    /// Test-only: whether the active memtable currently holds any
    /// entries. Used by `compact_range` tests to verify that the
    /// memtable was flushed to L0 as part of the range walk.
    #[cfg(test)]
    pub(crate) fn active_memtable_is_empty(&self) -> bool {
        let view = self.view.load();
        view.active.is_empty() && !view.active.has_range_tombstones()
    }

    /// Test-only: number of SSTable files at `level` in the current
    /// version.
    #[cfg(test)]
    pub(crate) fn level_file_count(&self, level: usize) -> usize {
        self.published_version().levels[level].len()
    }

    /// Test-only: total number of SSTable files across every level.
    #[cfg(test)]
    pub(crate) fn total_file_count(&self) -> usize {
        let v = self.published_version();
        v.levels.iter().map(|level| level.len()).sum()
    }

    /// Test-only: collect every raw `(seq, value_type)` version of
    /// `user_key` currently persisted across all SSTables. Used by the
    /// snapshot-pinning GC tests to check the post-compaction on-disk
    /// state - not just what reads see.
    #[cfg(test)]
    pub(crate) fn all_persisted_versions_of(
        &self,
        user_key: &[u8],
    ) -> std::io::Result<Vec<(u64, u8)>> {
        use internal_key::decode_internal_key;

        let version = self.published_version();
        let mut out = Vec::new();
        for level in &version.levels {
            for file in level {
                let mut entries = file.reader.iter_internal_stream(&self.cache)?;
                while let Some((ik, _v)) = entries.next_entry()? {
                    let (uk, seq, vt) = decode_internal_key(&ik);
                    if uk == user_key {
                        out.push((seq, vt));
                    }
                }
            }
        }
        out.sort();
        Ok(out)
    }

    /// Flush all data to disk and shut down background threads.
    pub(crate) fn close(&self) -> std::io::Result<()> {
        let _close_guard = self.close_lock.lock();
        match self.close_state.load(Ordering::Acquire) {
            CLOSE_STATE_CLOSED => return Ok(()),
            CLOSE_STATE_CLOSING => return Err(Self::closed_error()),
            _ => {}
        }

        self.close_state
            .store(CLOSE_STATE_CLOSING, Ordering::Release);
        self.stall_signal.notify_all();
        // Every queue waiting on a read gets its completion now, and the read
        // run again sees the database closing.
        self.cache.close_io();
        // A transaction still open ends here, on this thread, before the final
        // sync; one already committing is left to finish through it.
        self.open_transactions.abort_all(self);

        match self.close_inner() {
            Ok(()) => {
                self.close_state
                    .store(CLOSE_STATE_CLOSED, Ordering::Release);
                Ok(())
            }
            Err(err) => {
                self.close_state.store(CLOSE_STATE_OPEN, Ordering::Release);
                self.stall_signal.notify_all();
                Err(err)
            }
        }
    }

    fn close_inner(&self) -> std::io::Result<()> {
        if self.is_read_only() {
            self.compaction.lock().shutdown();
            return Ok(());
        }

        self.flush_memtables_for_close()?;

        {
            let mut guard = self.active_wal.lock();
            let wal = guard.as_mut().ok_or_else(Self::read_only_error)?;
            // A latched log may end in bytes nobody can account for, and
            // CLOSE would vouch for them: replay would then refuse the
            // crash it should survive. Such a log is left for recovery to
            // judge. Checked under the lock a failing commit latches under.
            if self.write_latched.load(Ordering::Acquire) {
                wal.sync_data()?;
            } else if let Err(err) = wal.close() {
                drop(guard);
                tracing::error!(error = %err, "closing the write-ahead log failed");
                self.latch_wal_failure(&err);
                return Err(err);
            }
        }
        // Signal under the mutex, join without it.
        //
        // A worker parked in `compaction_lock.read()` cannot exit until
        // whoever holds that gate is done, and `ingest_external_files` holds
        // it across a call that wants this same mutex. Joining while holding
        // the mutex therefore closes a cycle: close waits on the worker, the
        // worker waits on the ingest gate, and ingest waits on this mutex.
        // Dropping the guard before the join is what breaks it.
        let handles = {
            let mut scheduler = self.compaction.lock();
            scheduler.signal_shutdown();
            scheduler.take_handles()
        };
        for handle in handles {
            handle.join();
        }

        Ok(())
    }

    fn flush_memtables_for_close(&self) -> std::io::Result<()> {
        self.drain_memtables(ActiveFlush::WhenFull)
    }

    /// Flush frozen memtables until none remain, and the active one
    /// according to `active`.
    ///
    /// [`ActiveFlush::Always`] is what a checkpoint needs: it captures
    /// the SSTables the current version names and copies no WAL, so any
    /// write still sitting in a memtable would be absent from the
    /// result. Sealing without waiting is not enough either, because a
    /// sealed memtable is flushed by a background worker and the capture
    /// would race it.
    /// Whether no memtable holds anything a flush would write out.
    ///
    /// The postcondition of [`Self::drain_memtables`] with
    /// [`ActiveFlush::Always`], and what a checkpoint depends on: the
    /// capture names SSTables, so anything left in a memtable would be
    /// absent from it.
    /// Rewrite the manifest now, the way growth does on its own.
    #[cfg(test)]
    pub(crate) fn force_manifest_rewrite(&self) -> std::io::Result<()> {
        self.versions.lock().compact_manifest()
    }

    #[cfg(test)]
    pub(crate) fn memtables_hold_no_data(&self) -> bool {
        let view = self.view.load();
        view.frozen.is_empty() && view.active.is_empty() && !view.active.has_range_tombstones()
    }

    fn drain_memtables(&self, active: ActiveFlush) -> std::io::Result<()> {
        let active_pending = |view: &ReadView| match active {
            ActiveFlush::WhenFull => memtable_needs_flush(&view.active),
            ActiveFlush::Always => !view.active.is_empty() || view.active.has_range_tombstones(),
        };

        // The set to drain is fixed here and never extended. A drain that
        // re-read the view each pass would chase memtables that writers
        // created after it started, and under a steady write load it
        // would never finish: `Db::checkpoint` calls this with
        // `ActiveFlush::Always`, so a checkpoint taken while anything is
        // writing would hang rather than capture.
        let targets: Vec<Arc<MemTable>> = {
            let _write_guard = self.pipeline.lock();
            let view = self.view.load();
            let seal_active = active_pending(&view);
            if !seal_active && view.frozen.is_empty() {
                return Ok(());
            }
            let mut targets = view.frozen.clone();
            drop(view);

            if seal_active {
                let new_wal_id = {
                    let mut versions = self.versions.lock();
                    let version = versions.current();
                    let id = version.next_file_id;
                    versions.apply(&[VersionEdit::SetNextFileId(id + 1)])?;
                    id
                };
                let fresh = Arc::new(MemTable::new(&self.memtable_config)?);
                let old_wal = self.swap_wal(new_wal_id)?;

                // One publication for the seal and the enqueue: two
                // would leave a window where the sealed memtable is in
                // neither the active slot nor the frozen list.
                let sealed = self.view.update_memtables(|active, frozen| {
                    let sealed = Arc::clone(active);
                    let mut next_frozen = frozen.to_vec();
                    next_frozen.push(Arc::clone(&sealed));
                    (Arc::clone(&fresh), next_frozen, sealed)
                });
                sealed.seal_seq(self.latest_seq.load(Ordering::Acquire));

                self.wal_id.store(new_wal_id, Ordering::Release);
                sealed.seal_wal(old_wal.path().to_path_buf());
                targets.push(sealed);
            }
            targets
        };

        // Oldest first, which is also the order `flush_until_retired`
        // writes them in, so a target that an earlier pass already
        // flushed costs one list scan and no work.
        for target in &targets {
            self.flush_until_retired(target)?;
        }
        Ok(())
    }
}

/// Whether a drain must flush the active memtable unconditionally, or
/// only once it has grown past the write buffer.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ActiveFlush {
    WhenFull,
    Always,
}

/// A consistent snapshot of on-disk state captured by
/// [`RegolithEngine::checkpoint_capture`]. Holds the engine's compaction
/// lock for its entire lifetime, so no background or foreground
/// compaction can unlink files referenced by `version` while the
/// snapshot is alive. Callers MUST drop this snapshot as soon as
/// they are done with the filesystem work - a snapshot whose
/// lifetime outlives the enclosing function scope can deadlock a
/// concurrent `db.close()` / `drop(db)` that joins the background
/// compaction thread (the thread will block waiting for the same
/// lock the snapshot holds).
pub(crate) struct CheckpointSnapshot {
    pub(crate) version: Arc<manifest::Version>,
    /// The manifest exactly as it described `version`, captured under
    /// the same lock.
    ///
    /// The bytes are held rather than a path and a length. A concurrent
    /// flush takes `versions.lock()` but not the compaction lock this
    /// snapshot holds, so it can append `AddFile` records naming files
    /// this checkpoint will not copy, and a manifest rewrite can replace
    /// the file wholesale. Re-reading the path later would then pick up
    /// a different manifest, and truncating it at a length measured
    /// against the old one can land mid-record. Copying what was read
    /// under the lock removes both.
    ///
    /// The manifest is rewritten once it grows past a multiple of its
    /// canonical size, so this is bounded by the live SSTable count.
    pub(crate) manifest_bytes: Vec<u8>,
    pub(crate) sst_dir: PathBuf,
    /// Compaction lock guard, scoped to the snapshot's lifetime.
    _compaction_guard: OwnedGateWriteGuard,
}

impl CheckpointSnapshot {
    /// Format an SSTable filename for the given file id - exposes
    /// the engine's naming scheme to callers outside the `engine`
    /// module so they can stage files into checkpoint / backup
    /// directories.
    pub(crate) fn sst_filename(id: u64) -> String {
        sst_filename(id)
    }
}

fn list_wal_files(env: &dyn Env, dir: &Path) -> std::io::Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    if env.exists(dir) {
        for entry in env.read_dir(dir)? {
            if entry
                .path
                .extension()
                .is_some_and(|ext| ext == "log" || ext == "wal")
            {
                files.push(entry.path);
            }
        }
    }
    Ok(files)
}

fn remove_obsolete_sst_files(
    env: &dyn Env,
    sst_dir: &Path,
    version: &manifest::Version,
) -> std::io::Result<()> {
    let mut removed_any = false;
    for level in &version.levels {
        for file in level {
            let path = sst_dir.join(sst_filename(file.meta.file_id));
            removed_any |= remove_file_if_exists(env, &path);
        }
    }
    if removed_any {
        env.sync_dir(sst_dir)?;
    }
    Ok(())
}

fn remove_obsolete_wal_files(
    env: &dyn Env,
    wal_dir: &Path,
    keep_path: &Path,
) -> std::io::Result<()> {
    let mut removed_any = false;
    for path in list_wal_files(env, wal_dir)? {
        if path == keep_path {
            continue;
        }
        removed_any |= remove_file_if_exists(env, &path);
    }
    if removed_any {
        env.sync_dir(wal_dir)?;
    }
    Ok(())
}

/// Unlink an obsolete file, reporting whether anything was removed.
///
/// Best effort by design, and the two callers are the only ones: an
/// obsolete SSTable or WAL is already unreachable through the manifest,
/// so failing to unlink it costs disk until the next sweep and costs
/// correctness nothing. Propagating the failure instead would fail the
/// operation that happened to trigger the sweep, which is how a
/// `drop_all` or a compaction came to return "Access is denied".
///
/// Windows is why this is not merely defensive. A file unlinked while
/// something still holds it open stays delete-pending: the name is still
/// there, and both a second unlink and an open of it are refused with
/// `ACCESS_DENIED` rather than the `NotFound` unix answers with. A sweep
/// that races a reader therefore sees an error for a file that is
/// already on its way out.
fn remove_file_if_exists(env: &dyn Env, path: &Path) -> bool {
    match env.remove_file(path) {
        Ok(()) => true,
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => false,
        Err(err) => {
            tracing::debug!(
                path = %path.display(),
                error = %err,
                "could not unlink an obsolete file; leaving it for the next sweep"
            );
            false
        }
    }
}

fn wal_file_id(path: &Path) -> Option<u64> {
    let stem = path.file_stem()?.to_str()?;
    stem.strip_prefix("wal_")?.parse().ok()
}

fn should_replay_wal(path: &Path, min_wal_id: u64) -> bool {
    match wal_file_id(path) {
        Some(id) => id >= min_wal_id,
        // A temporary WAL name carries no id to compare against the
        // reset marker. Once a reset has committed, such a file must not
        // be allowed to resurrect data.
        None => min_wal_id == 0,
    }
}

fn next_wal_id(manifest_next_file_id: u64, wal_files: &[PathBuf]) -> u64 {
    wal_files
        .iter()
        .filter_map(|path| wal_file_id(path))
        .map(|id| id.saturating_add(1))
        .fold(manifest_next_file_id, u64::max)
}

fn apply_replayed_wal_entry(memtable: &MemTable, entry: WalEntry) -> u64 {
    match entry {
        WalEntry::Put { key, value, seq } => {
            memtable.put(&key, &value, seq);
            seq
        }
        WalEntry::Delete { key, seq } => {
            memtable.delete(&key, seq);
            seq
        }
        WalEntry::DeleteRange { start, end, seq } => {
            memtable.delete_range(&start, &end, seq);
            seq
        }
        WalEntry::Merge { key, operand, seq } => {
            memtable.merge(&key, &operand, seq);
            seq
        }
    }
}

#[cfg(test)]
mod recovery_tests;
