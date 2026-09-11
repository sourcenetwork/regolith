//! ACID transactions on top of [`crate::Db`].
//!
//! Two flavors:
//!
//! - [`OptimisticTransactionDb`]: transactions take no locks,
//!   buffer writes in memory, and detect write-write conflicts at
//!   commit time by re-checking the visible seq of each touched key
//!   against the snapshot seq the transaction was anchored at.
//!   Best for low-contention workloads where most transactions
//!   commit on the first try.
//!
//! - [`TransactionDb`]: transactions acquire exclusive key locks
//!   as they write (or as [`Transaction::get_for_update`] is called)
//!   and hold them until commit / rollback. Contention is resolved
//!   when the lock is taken rather than at commit, and a
//!   timeout-based deadlock defense returns [`TransactionError::Busy`]
//!   when a lock cannot be acquired in time. Best for workloads
//!   where contention is high and retry cost dominates.
//!
//! Both flavors share a single [`Transaction`] type. The type
//! carries the mode internally so user code can write helpers that
//! work against either db.
//!
//! # Isolation level
//!
//! Both flavors provide **snapshot isolation** and both prevent
//! lost updates, but they anchor their reads at different points.
//!
//! An optimistic transaction reads everything as of the engine seq
//! captured at begin. A pessimistic transaction reads a key it has
//! not locked at that same begin seq, and reads a key it locks
//! through [`Transaction::get_for_update`] as of the moment the
//! lock was acquired. The lock handoff orders it after every
//! transaction that committed while it waited, so a
//! read-modify-write through `get_for_update` sees the value the
//! previous lock holder committed instead of a stale one. Reads
//! that hit the transaction's own buffered writes always see the
//! written value. A read anchor only ever moves forward, so two
//! reads of the same key inside one transaction never travel
//! backwards in time.
//!
//! At commit each flavor validates a set of keys, every key against
//! the *earliest* sequence this transaction observed it at:
//!
//! - Optimistic: every key the transaction wrote or read through
//!   `get_for_update`, against the begin snapshot.
//! - Pessimistic: every key the transaction read and then wrote
//!   (the read-modify-write set) plus every key it read through
//!   `get_for_update`. A key written blind, without ever being
//!   read, is not validated: there is no read to invalidate, and the
//!   key lock already orders it against every other transaction.
//!
//! For a pessimistic transaction the check cannot fire while every
//! writer goes through the lock manager. It fires when a key the
//! transaction read was written around the lock manager (for example
//! through [`TransactionDb::db`]) or before the lock was taken,
//! which surfaces as [`TransactionError::Conflict`] rather than as
//! a lost update.
//!
//! Rolling back to a savepoint discards buffered writes; it does not
//! discard what the transaction has already read, so a read anchor
//! survives the rollback and still guards the commit.
//!
//! Below [`IsolationLevel::Serializable`] a plain read ([`Transaction::get`],
//! [`Transaction::get_slice`] or a transactional scan) of a key the
//! transaction never writes is not validated; at
//! [`IsolationLevel::SnapshotIsolation`] a [`Transaction::get_for_update`]
//! key is validated even when it is not written. At `Serializable` every key
//! read by any of them is validated. At every level, a key a transactional
//! scan walked that the transaction then writes is validated as a read from
//! the begin snapshot, so a scan-then-write is never taken for a blind write.
//!
//! # Out of scope (follow-ups)
//!
//! - Phantom detection. A transactional scan records the stretches of keys
//!   it walked, but only to anchor keys the commit validates anyway: a key
//!   another transaction inserts into a scanned range after the snapshot (a
//!   phantom) is detected only when this transaction also writes it or
//!   validates it as a point read at its level.
//! - Transactional range deletes. [`Transaction::delete_range`] rejects
//!   non-empty ranges until range conflict tracking or range locks land.
//! - Wait-for graph deadlock detection (the pessimistic flavor ships
//!   with timeout-based detection only).
//! - Column-family-aware transactions (depends on CFs landing).

use crate::portability::{AtomicBool, AtomicU64, Ordering};
use kovan_queue::seg_queue::SegQueue;

use crate::txn_buffer::TxnBuffer;
use std::collections::{BTreeMap, HashMap};
use std::ops::ControlFlow;
use std::path::Path;
use std::sync::{Arc, OnceLock};
use std::time::Duration;

use crate::sync::{Condvar, Mutex};

use crate::column_family::{DEFAULT_CF_ID, prefix_key};
use crate::engine::{CommitOutcome, ConflictKey, RegolithEngine, ValidationSet};
use crate::{Db, DbSlice, Error, Options, Result};

mod scan_range;
use scan_range::{OpenRun, ScanRun};

/// Default lock-acquisition timeout for [`TransactionDb`] when the
/// caller doesn't specify one on [`TransactionDb::with_lock_timeout`].
/// Tuned to "long enough that a fast transaction finishes, short
/// enough that a deadlock surfaces quickly".
const DEFAULT_LOCK_TIMEOUT: Duration = Duration::from_secs(1);

/// Reasons a transaction can fail to commit. Not a variant of
/// [`crate::Error`]: a conflict is a retry-able business outcome,
/// distinct from an I/O failure.
#[derive(Debug, thiserror::Error)]
pub enum TransactionError {
    /// Propagated I/O error from the underlying engine.
    #[error(transparent)]
    Io(#[from] std::io::Error),
    /// A key in the transaction's validation set was written by
    /// someone else after this transaction first observed it: after
    /// the begin snapshot for an optimistic transaction, or after
    /// the read that the pessimistic transaction is about to
    /// overwrite. The caller should roll back and retry.
    #[error(
        "transaction conflict on key {key:?}: observed seq {observed_seq}, latest seq {latest_seq}"
    )]
    Conflict {
        /// The offending user key.
        key: Vec<u8>,
        /// The seq the transaction observed the key at.
        observed_seq: u64,
        /// The newest seq found for the key during the commit check.
        latest_seq: u64,
    },
    /// A pessimistic transaction could not acquire a key lock in
    /// time. Indicates either high contention or a deadlock; the
    /// caller should roll back and retry (possibly with a
    /// different operation order).
    #[error("transaction busy acquiring lock on key {0:?}")]
    Busy(Vec<u8>),
    /// The caller tried to use a savepoint that was never set.
    #[error("no savepoint to roll back to")]
    NoSavepoint,
    /// Transactional range deletes are disabled until they can
    /// participate in conflict detection or range locking.
    #[error("transactional range deletes are not supported")]
    UnsupportedRangeDelete,
}

/// Convenience alias for results returned by transaction methods.
pub type TxResult<T> = std::result::Result<T, TransactionError>;

impl From<Error> for TransactionError {
    fn from(e: Error) -> Self {
        TransactionError::Io(e.into_io_error())
    }
}

/// Optimistic-concurrency-control wrapper over a [`Db`].
///
/// `begin_transaction` returns a fresh [`Transaction`] whose
/// `commit` performs write-write conflict detection against the
/// seq captured at begin time. No locks are taken; other writers
/// proceed in parallel. Conflicts surface as
/// [`TransactionError::Conflict`].
pub struct OptimisticTransactionDb {
    isolation: IsolationLevel,
    inner: Db,
}

impl std::fmt::Debug for OptimisticTransactionDb {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OptimisticTransactionDb")
            .finish_non_exhaustive()
    }
}

impl OptimisticTransactionDb {
    /// Open or create an optimistic-transaction database at `path`.
    pub fn open<P: AsRef<Path>>(path: P, opts: Options) -> Result<Self> {
        Ok(Self {
            inner: Db::open(path, opts)?,
            isolation: IsolationLevel::default(),
        })
    }

    /// Borrow the underlying [`Db`] for APIs that
    /// [`OptimisticTransactionDb`] doesn't wrap: snapshots, the
    /// streaming iterator, `compact_range`, `close`, etc.
    pub fn db(&self) -> &Db {
        &self.inner
    }

    /// Start a new optimistic transaction anchored at the engine's
    /// current sequence number. Reads see a consistent view as of
    /// that seq; writes buffer in memory until [`Transaction::commit`].
    pub fn begin_transaction(&self) -> Transaction<'_> {
        self.begin_transaction_with(self.isolation)
    }

    /// Begin a transaction at an explicit [`IsolationLevel`], whatever
    /// the database default is.
    ///
    /// Per transaction rather than per database because the level is a
    /// property of what a unit of work needs: a read-mostly query and a
    /// read-modify-write against the same database want different
    /// answers, and paying serializable validation for the former is
    /// waste.
    pub fn begin_transaction_with(&self, isolation: IsolationLevel) -> Transaction<'_> {
        self.begin_inner(isolation)
    }

    /// Begin a transaction that keeps this database alive for as long as
    /// it lives, for callers that must store it in a `'static` container
    /// such as a boxed trait object.
    pub fn begin_transaction_owned(
        self: &Arc<Self>,
        isolation: IsolationLevel,
    ) -> OwnedTransaction {
        OwnedTransaction::new(self.begin_inner(isolation), Arc::clone(self) as Arc<_>)
    }

    /// The lifetime is free because a `Transaction` borrows nothing from
    /// the database: every field it holds is owned. The two public entry
    /// points differ only in what they tie that freedom to.
    fn begin_inner<'any>(&self, isolation: IsolationLevel) -> Transaction<'any> {
        let engine = self.inner.engine_arc();
        let snapshot_seq = engine.register_snapshot_at_horizon();
        Transaction::new(
            engine,
            snapshot_seq,
            self.inner.durability(),
            TxMode::Optimistic,
            None,
            DEFAULT_LOCK_TIMEOUT,
            isolation,
            self.inner.transaction_keys_inline(),
        )
    }

    /// Set the default [`IsolationLevel`] for transactions this database
    /// begins. Defaults to [`IsolationLevel::SnapshotIsolation`].
    pub fn with_isolation(mut self, isolation: IsolationLevel) -> Self {
        self.isolation = isolation;
        self
    }

    /// The default level [`Self::begin_transaction`] uses.
    pub fn isolation(&self) -> IsolationLevel {
        self.isolation
    }
}

/// Pessimistic-concurrency-control wrapper over a [`Db`].
///
/// Transactions acquire exclusive locks on every key they touch
/// for update (via `put`, `delete`, or `get_for_update`) and hold
/// the locks until commit or rollback. Lock contention is resolved
/// immediately, not at commit. A timeout-based deadlock defense
/// surfaces as [`TransactionError::Busy`] when a lock cannot be
/// acquired in time.
pub struct TransactionDb {
    isolation: IsolationLevel,
    inner: Db,
    lock_manager: Arc<LockManager>,
    tx_id: AtomicU64,
    lock_timeout: Duration,
}

impl std::fmt::Debug for TransactionDb {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TransactionDb")
            .field("lock_timeout", &self.lock_timeout)
            .finish_non_exhaustive()
    }
}

impl TransactionDb {
    /// Open or create a pessimistic-transaction database at `path`.
    /// The lock-acquisition timeout defaults to `DEFAULT_LOCK_TIMEOUT`;
    /// customize it via [`TransactionDb::with_lock_timeout`].
    pub fn open<P: AsRef<Path>>(path: P, opts: Options) -> Result<Self> {
        Ok(Self {
            inner: Db::open(path, opts)?,
            isolation: IsolationLevel::default(),
            lock_manager: Arc::new(LockManager::new()),
            tx_id: AtomicU64::new(1),
            lock_timeout: DEFAULT_LOCK_TIMEOUT,
        })
    }

    /// Borrow the underlying [`Db`].
    pub fn db(&self) -> &Db {
        &self.inner
    }

    /// Override the default lock-acquisition timeout for every
    /// future transaction created by this db.
    pub fn with_lock_timeout(mut self, timeout: Duration) -> Self {
        self.lock_timeout = timeout;
        self
    }

    /// Start a new pessimistic transaction. Reads see the engine
    /// state as of the current seq; writes acquire key locks that
    /// the caller retains until commit or rollback.
    pub fn begin_transaction(&self) -> Transaction<'_> {
        self.begin_transaction_with(self.isolation)
    }

    /// Begin a transaction at an explicit [`IsolationLevel`].
    pub fn begin_transaction_with(&self, isolation: IsolationLevel) -> Transaction<'_> {
        self.begin_inner(isolation)
    }

    /// Begin a transaction that keeps this database alive for as long as
    /// it lives. See [`OptimisticTransactionDb::begin_transaction_owned`].
    pub fn begin_transaction_owned(
        self: &Arc<Self>,
        isolation: IsolationLevel,
    ) -> OwnedTransaction {
        OwnedTransaction::new(self.begin_inner(isolation), Arc::clone(self) as Arc<_>)
    }

    fn begin_inner<'any>(&self, isolation: IsolationLevel) -> Transaction<'any> {
        let engine = self.inner.engine_arc();
        let snapshot_seq = engine.register_snapshot_at_horizon();
        let id = self.tx_id.fetch_add(1, Ordering::Relaxed);
        Transaction::new(
            engine,
            snapshot_seq,
            self.inner.durability(),
            TxMode::Pessimistic { tx_id: id },
            Some(Arc::clone(&self.lock_manager)),
            self.lock_timeout,
            isolation,
            self.inner.transaction_keys_inline(),
        )
    }

    /// Set the default [`IsolationLevel`] for transactions this database
    /// begins. Defaults to [`IsolationLevel::SnapshotIsolation`].
    pub fn with_isolation(mut self, isolation: IsolationLevel) -> Self {
        self.isolation = isolation;
        self
    }

    /// The default level [`Self::begin_transaction`] uses.
    pub fn isolation(&self) -> IsolationLevel {
        self.isolation
    }
}

/// Which way a scan walks its range.
///
/// The range is the same either way: `[start, end)`, with `start` inclusive
/// and `end` exclusive. Only the order entries arrive in changes.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ScanDirection {
    /// Ascending, from `start` towards `end`.
    #[default]
    Forward,
    /// Descending, from the highest key below `end` down to `start`.
    Reverse,
}

/// How much a transaction is protected against concurrent commits.
///
/// The level decides what the commit-time validation covers, so it
/// decides which anomalies are reachable.
///
/// # What each level admits
///
/// | Level | Dirty read | Non-repeatable read | Lost update | Write skew |
/// |---|---|---|---|---|
/// | [`IsolationLevel::ReadCommitted`] | no | possible | possible | possible |
/// | [`IsolationLevel::SnapshotIsolation`] | no | no | no | **possible** |
/// | [`IsolationLevel::Serializable`] | no | no | no | no |
///
/// Every level reads from a snapshot captured when the transaction
/// began, so none of them can observe a dirty read. What changes is the
/// size of the read set validated at commit.
///
/// # Why write skew survives snapshot isolation
///
/// Under [`IsolationLevel::SnapshotIsolation`] a key is validated only
/// if the transaction wrote it, or read it through
/// [`Transaction::get_for_update`]. Two transactions can therefore each
/// read what the other is about to overwrite, write disjoint keys, and
/// both commit - a schedule no serial order produces. Elle reports it as
/// a G2 anti-dependency cycle.
///
/// [`IsolationLevel::Serializable`] validates *every* key the
/// transaction read. A concurrent commit to any of them aborts it, so
/// the anti-dependency edge that would close the cycle cannot form.
/// This is backward validation: the cost is paid by the transaction
/// committing second, and it is proportional to its read set.
///
/// # The one thing to know before relying on it
///
/// Serializability here is validation of a set of keys, not of a
/// predicate. Point reads and every key a transactional scan yields are
/// in that set. The stretches a scan walked are recorded too, but only to
/// anchor keys the transaction validates anyway: a phantom - a key that
/// did not exist to be yielded, inserted into the range by a concurrent
/// transaction - aborts the transaction only if it also writes that key or
/// point-reads it. A transaction whose correctness depends on the absence
/// of keys in a range must not rely on this level for it.
/// [`Transaction::delete_range`] stays rejected.
///
/// # What a scan costs at Serializable
///
/// A transactional scan at [`IsolationLevel::Serializable`] adds one
/// read-set entry per key it yields, held until the transaction resolves,
/// and the commit checks each of them while holding the write pipeline
/// that every writer of the database, [`crate::Db::put`] included, waits
/// on: the commit cost is one check per scanned key, and a large scan
/// stalls every writer for that long. Below this level a scan records one
/// entry per stretch of keys it walked, not one per key.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum IsolationLevel {
    /// Validate nothing beyond what the transaction wrote.
    ReadCommitted,
    /// Validate writes and keys read through
    /// [`Transaction::get_for_update`]. regolith's default.
    #[default]
    SnapshotIsolation,
    /// Validate the entire read set, including every key a transactional
    /// scan yields.
    Serializable,
}

#[derive(Clone, Copy)]
enum TxMode {
    Optimistic,
    Pessimistic { tx_id: u64 },
}

/// An in-flight transaction. Created by
/// [`OptimisticTransactionDb::begin_transaction`] or
/// [`TransactionDb::begin_transaction`] and resolved by
/// [`Transaction::commit`] or [`Transaction::rollback`].
///
/// Reads within the transaction see a consistent snapshot captured
/// at begin time, except for keys that the transaction itself has
/// written; those always read back the buffered write.
///
/// Dropping a `Transaction` without committing is equivalent to
/// calling [`Transaction::rollback`]: buffered writes are
/// discarded and any held locks are released.
pub struct Transaction<'db> {
    engine: Arc<RegolithEngine>,
    /// What the commit-time validation covers. See [`IsolationLevel`].
    isolation: IsolationLevel,
    snapshot_seq: u64,
    durability: crate::engine::DurabilityMode,
    mode: TxMode,
    /// Buffer of point writes. `Some(v)` is a put, `None` is a
    /// delete. Concurrent so that buffering a write takes `&self`;
    /// drained into a `BTreeMap` at commit, which is where the order
    /// the engine applies them in is restored.
    writes: TxnBuffer<Vec<u8>, Option<Vec<u8>>>,
    /// Range deletes buffered for commit. Not tracked in the
    /// optimistic conflict set (initial impl limitation).
    range_deletes: SegQueue<(Vec<u8>, Vec<u8>)>,
    /// Merge operands buffered for commit.
    merges: SegQueue<(Vec<u8>, Vec<u8>)>,
    /// What this transaction has observed about each key it read,
    /// through a point read, or through a scan at Serializable. Sorted
    /// at commit so a multi-key conflict always reports the same key.
    /// Never rewound: a savepoint rollback undoes buffered writes, not
    /// reads that already happened.
    tracked: TxnBuffer<Vec<u8>, Arc<KeyState>>,
    /// The stretches of snapshot keys this transaction's scans yielded, one
    /// record per stretch rather than one per key. Allocated by the first
    /// scan that yields a snapshot key. Never rewound, like `tracked`.
    ///
    /// Boxed so the queue (and its 32-slot first segment once it exists)
    /// stays off the `Transaction` struct itself: every commit moves this
    /// value, and a transaction that never scans must not pay for it.
    scan_runs: OnceLock<Box<SegQueue<Arc<ScanRun>>>>,
    /// Highest sequence [`Transaction::get_for_update`] has ever promoted a
    /// key to; `snapshot_seq` while nothing has been promoted past it.
    /// Lets `scan_read_seq` skip the `tracked` lookup outright for a
    /// pessimistic scan that could not possibly find a promoted key,
    /// instead of walking `tracked` once per yielded key.
    promoted_seq: AtomicU64,
    /// Savepoint stack. Each entry captures the full write buffer
    /// and a count of locks held at that point.
    savepoints: Vec<Savepoint>,
    /// Keys for which this transaction holds a pessimistic lock.
    /// A set rather than a list: membership is checked on every
    /// locking operation, and release order does not matter.
    /// Released by `Drop` if not already released by `commit` or
    /// `rollback`.
    held_locks: TxnBuffer<Vec<u8>, ()>,
    lock_manager: Option<Arc<LockManager>>,
    lock_timeout: Duration,
    /// See [`crate::Options::transaction_keys_inline`]. Kept so a
    /// savepoint rollback rebuilds the buffer the same way.
    keys_inline: usize,
    resolved: bool,
    resources_released: bool,
    _phantom: std::marker::PhantomData<&'db ()>,
}

#[derive(Clone)]
struct Savepoint {
    writes: BTreeMap<Vec<u8>, Option<Vec<u8>>>,
    range_deletes: Vec<(Vec<u8>, Vec<u8>)>,
    merges: Vec<(Vec<u8>, Vec<u8>)>,
    held_lock_count: usize,
}

/// What one transaction knows about one key it has read.
///
/// Shared, never copied: `tracked` holds an `Arc` of this cell and every
/// observation of the key folds into that one instance. The mutable
/// fields are atomic and every update is monotonic, so two threads
/// reading the same key through the same transaction cannot lose an
/// observation between them: `read_seq` only rises and `for_update` only
/// latches on. Copying the cell, or a non-atomic read-modify-write on
/// it, would let one thread's observation overwrite another's and
/// silently shrink the commit-time validation set.
struct KeyState {
    /// Sequence this transaction first observed the key at.
    /// Validation uses this one, because it is the read a later
    /// write of the same key would otherwise silently overwrite.
    /// Written once, when the cell is created, then read-only.
    first_read_seq: u64,
    /// Sequence later reads of the key are served at. Only ever
    /// moves forward, so `get_for_update` can promote a key that was
    /// already read at the begin snapshot to the lock horizon
    /// without any read of this transaction going backwards.
    read_seq: AtomicU64,
    /// The key was read through [`Transaction::get_for_update`], so
    /// it is validated at commit whether or not it is written.
    for_update: AtomicBool,
}

impl KeyState {
    fn new(horizon: u64, for_update: bool) -> Self {
        Self {
            first_read_seq: horizon,
            read_seq: AtomicU64::new(horizon),
            for_update: AtomicBool::new(for_update),
        }
    }
}

impl<'db> Transaction<'db> {
    #[allow(clippy::too_many_arguments)]
    fn new(
        engine: Arc<RegolithEngine>,
        snapshot_seq: u64,
        durability: crate::engine::DurabilityMode,
        mode: TxMode,
        lock_manager: Option<Arc<LockManager>>,
        lock_timeout: Duration,
        isolation: IsolationLevel,
        keys_inline: usize,
    ) -> Self {
        Self {
            engine,
            snapshot_seq,
            durability,
            mode,
            isolation,
            writes: TxnBuffer::new(keys_inline),
            range_deletes: SegQueue::new(),
            merges: SegQueue::new(),
            tracked: TxnBuffer::new(keys_inline),
            scan_runs: OnceLock::new(),
            promoted_seq: AtomicU64::new(snapshot_seq),
            savepoints: Vec::new(),
            held_locks: TxnBuffer::new(keys_inline),
            lock_manager,
            lock_timeout,
            keys_inline,
            resolved: false,
            resources_released: false,
            _phantom: std::marker::PhantomData,
        }
    }

    /// Read `key` from the default column family. Returns the
    /// buffered write if the transaction has already written to
    /// `key`, otherwise the value visible at the sequence this
    /// transaction observes `key` at: its begin snapshot, or, for a
    /// key a pessimistic transaction already holds a lock on, the
    /// horizon sampled when that lock was acquired.
    ///
    /// Takes no lock. The read is remembered, so writing the same
    /// key later turns it into a read-modify-write that is validated
    /// at commit and aborts with [`TransactionError::Conflict`]
    /// rather than losing the update. Below
    /// [`IsolationLevel::Serializable`], a key that is read and
    /// never written is not validated: use
    /// [`Transaction::get_for_update`] when a read must participate
    /// in conflict detection on its own.
    pub fn get(&self, key: &[u8]) -> TxResult<Option<Vec<u8>>> {
        let prefixed = prefix_key(DEFAULT_CF_ID, key);
        if let Some(buffered) = self.writes.get(&prefixed) {
            return Ok(buffered);
        }
        let read_seq = self.observe(&prefixed, self.snapshot_seq, false);
        self.engine
            .get_at(&prefixed, read_seq)
            .map_err(TransactionError::Io)
    }

    /// [`Transaction::get`] without copying the value.
    ///
    /// The returned [`DbSlice`] borrows the bytes the database already
    /// holds, or the buffered write this transaction made. Nothing is
    /// materialized on the way out.
    pub fn get_slice(&self, key: &[u8]) -> TxResult<Option<DbSlice>> {
        let prefixed = prefix_key(DEFAULT_CF_ID, key);
        if let Some(buffered) = self.writes.get(&prefixed) {
            return Ok(buffered.map(DbSlice::from));
        }
        let read_seq = self.observe(&prefixed, self.snapshot_seq, false);
        self.engine
            .get_slice_at(&prefixed, read_seq)
            .map_err(TransactionError::Io)
    }

    /// Scan a key range without materializing it, merging this
    /// transaction's buffered writes over the snapshot underneath.
    ///
    /// The database side is streamed, and a caller that stops early pays
    /// only for what it read. The transaction's own writes are sorted up
    /// front, which is bounded by what this transaction has written rather
    /// than by what the database holds.
    ///
    /// What the scan leaves in the transaction depends on the level. Below
    /// [`IsolationLevel::Serializable`] it records each unbroken stretch of
    /// snapshot keys it yields once, as its first and last key, so what it
    /// holds until the transaction resolves grows with the number of scans
    /// (and the transaction's own writes inside the range), not with the size
    /// of the range. At `Serializable` it also records every yielded key as a
    /// read, exactly as [`Transaction::get`] does: that grows by one entry per
    /// distinct key yielded, and the commit checks each one while holding the
    /// write pipeline, so every writer waits one check per scanned key.
    ///
    /// At every level, a key inside a stretch the scan walked that the
    /// transaction then writes is validated as a read from the begin
    /// snapshot, as a `get` followed by the write would be, so it is never
    /// elided as a blind write. At `Serializable` a concurrent commit to any
    /// yielded key also aborts the transaction. Keys yielded from the
    /// transaction's own buffered writes are not recorded and end a stretch,
    /// as `get` does not record them either. A key a pessimistic transaction
    /// already locked through [`Transaction::get_for_update`] is served where
    /// `get` serves it, at the lock horizon. A key a concurrent transaction
    /// inserts into the range is not detected unless this transaction
    /// validates it anyway; see [`IsolationLevel`].
    ///
    /// A stretch is recorded when its first key is yielded and closed when
    /// the stream is exhausted or dropped. A stream that is never dropped
    /// (leaked) counts as having walked to the end of the keyspace in its
    /// direction.
    pub fn scan_stream(&self, start: Option<&[u8]>, end: Option<&[u8]>) -> TxnScanStream<'_> {
        self.scan_stream_in(start, end, ScanDirection::Forward)
    }

    /// [`Transaction::scan_stream`], walking `direction`.
    ///
    /// The range is `[start, end)` either way; only the order the entries
    /// arrive in changes. Reverse starts at the highest key below `end` and
    /// walks down to `start` inclusive.
    ///
    /// Both sides of the merge reverse together: the snapshot cursor steps
    /// with `prev`, and the transaction's own writes are sorted descending, so
    /// a buffered put still replaces the snapshot entry it shadows and a
    /// buffered delete still hides it.
    pub fn scan_stream_in(
        &self,
        start: Option<&[u8]>,
        end: Option<&[u8]>,
        direction: ScanDirection,
    ) -> TxnScanStream<'_> {
        // `scan_read_seq` indexes `tracked` itself, lazily, the first time
        // it finds a promotion; a `&self` stream and `&self` `get_for_update`
        // mean a promotion can land after this call returns, so indexing
        // only here would miss it. See `scan_read_seq`.
        let lo = start.map(|s| prefix_key(DEFAULT_CF_ID, s));
        let hi = end.map(|e| prefix_key(DEFAULT_CF_ID, e));
        let reverse = direction == ScanDirection::Reverse;

        let mut buffered: Vec<(Vec<u8>, Option<Vec<u8>>)> = self.writes.snapshot_matching(|key| {
            lo.as_ref().is_none_or(|lo| key >= lo) && hi.as_ref().is_none_or(|hi| key < hi)
        });
        if reverse {
            buffered.sort_unstable_by(|a, b| b.0.cmp(&a.0));
        } else {
            buffered.sort_unstable_by(|a, b| a.0.cmp(&b.0));
        }

        let mut cursor = crate::CfIter::new(
            crate::Iter::from_internal(self.engine.new_iter_at(self.snapshot_seq)),
            DEFAULT_CF_ID,
        );
        if reverse {
            match &hi {
                // `end` is exclusive, so a backward walk starts below it.
                Some(hi) => {
                    let end = &hi[4..];
                    cursor.seek_for_prev(end);
                    if cursor.valid() && cursor.key() == Some(end) {
                        cursor.prev();
                    }
                }
                None => cursor.seek_to_last(),
            }
        } else {
            match &lo {
                Some(lo) => cursor.seek(&lo[4..]),
                None => cursor.seek_to_first(),
            }
        }

        TxnScanStream {
            txn: self,
            cursor,
            cursor_done: false,
            buffered: buffered.into_iter().peekable(),
            start: lo.map(|lo| lo[4..].to_vec()),
            end: hi.map(|hi| hi[4..].to_vec()),
            reverse,
            run: None,
            probe: Vec::new(),
            error: None,
        }
    }

    /// Read `key`, flag it for conflict detection at commit, and,
    /// for pessimistic transactions, take an exclusive lock on it
    /// for the rest of the transaction.
    ///
    /// A pessimistic transaction reads the value as of the moment
    /// it acquired the lock, not as of its begin snapshot, so a
    /// read-modify-write under `get_for_update` observes every
    /// transaction that committed before the lock was released to
    /// it. An optimistic transaction reads at its begin snapshot
    /// and detects the conflict at commit instead.
    pub fn get_for_update(&self, key: &[u8]) -> TxResult<Option<Vec<u8>>> {
        let prefixed = prefix_key(DEFAULT_CF_ID, key);
        let already_held = self.lock_key(&prefixed)?;
        let horizon = self.read_horizon(&prefixed, already_held);
        let read_seq = self.observe(&prefixed, horizon, true);
        // Tells `scan_read_seq` a promoted key might exist, so it is worth
        // looking `tracked` up for a pessimistic scan.
        self.promoted_seq.fetch_max(read_seq, Ordering::AcqRel);
        if let Some(buffered) = self.writes.get(&prefixed) {
            return Ok(buffered);
        }
        self.engine
            .get_at(&prefixed, read_seq)
            .map_err(TransactionError::Io)
    }

    /// Buffer a put. For pessimistic transactions, acquires an
    /// exclusive lock on the key if not already held.
    pub fn put(&self, key: &[u8], value: &[u8]) -> TxResult<()> {
        let prefixed = prefix_key(DEFAULT_CF_ID, key);
        self.lock_key(&prefixed)?;
        self.writes.insert(prefixed, Some(value.to_vec()));
        Ok(())
    }

    /// Buffer a delete. For pessimistic transactions, acquires an
    /// exclusive lock on the key if not already held.
    pub fn delete(&self, key: &[u8]) -> TxResult<()> {
        let prefixed = prefix_key(DEFAULT_CF_ID, key);
        self.lock_key(&prefixed)?;
        self.writes.insert(prefixed, None);
        Ok(())
    }

    /// Attempt to delete every key in `[start, end)`.
    ///
    /// Non-empty transactional range deletes are rejected until
    /// they can participate in optimistic conflict detection or
    /// pessimistic range locking. For correctness-critical
    /// workloads, delete known keys individually with
    /// [`Transaction::delete`] and use [`Transaction::get_for_update`]
    /// when a read must also participate in conflict detection.
    ///
    /// Calls with `start >= end` are treated as no-ops and return
    /// `Ok(())`. That is deliberate and it is the one place where a
    /// transactional write's acceptance depends on the arguments being
    /// empty: `Db::write` rejects an empty batch on a read-only handle
    /// because handle state is not an argument, while here the
    /// rejection is a missing feature and an empty range asks for no
    /// work from it. Callers that want the unsupported-feature error
    /// unconditionally must check the range themselves.
    pub fn delete_range(&self, start: &[u8], end: &[u8]) -> TxResult<()> {
        if start >= end {
            return Ok(());
        }
        Err(TransactionError::UnsupportedRangeDelete)
    }

    /// Buffer a merge operand. Merges are conflict-checked at the
    /// key level: two transactions cannot concurrently merge the
    /// same key under optimistic concurrency control.
    pub fn merge(&self, key: &[u8], operand: &[u8]) -> TxResult<()> {
        let prefixed = prefix_key(DEFAULT_CF_ID, key);
        self.lock_key(&prefixed)?;
        self.merges.push((prefixed, operand.to_vec()));
        Ok(())
    }

    /// Save the current state of buffered writes. A later call to
    /// [`Transaction::rollback_to_savepoint`] reverts every buffered
    /// write made after this call.
    pub fn set_savepoint(&mut self) {
        // `&mut self` is what makes this coherent: a savepoint over a
        // buffer another thread is still writing would capture a torn
        // state, so taking one is an exclusive operation even though
        // buffering is not.
        self.savepoints.push(Savepoint {
            writes: self.writes.snapshot().into_iter().collect(),
            range_deletes: drain(&self.range_deletes),
            merges: drain(&self.merges),
            held_lock_count: self.held_locks.len(),
        });
        // `drain` emptied them, so put back what the savepoint captured.
        if let Some(sp) = self.savepoints.last() {
            for entry in &sp.range_deletes {
                self.range_deletes.push(entry.clone());
            }
            for entry in &sp.merges {
                self.merges.push(entry.clone());
            }
        }
    }

    /// Roll back to the most recent savepoint. Discards every
    /// buffered write made after the savepoint. Locks acquired
    /// after the savepoint stay held: regolith's pessimistic lock
    /// manager does not release mid-transaction locks.
    ///
    /// Reads are not rolled back. A key this transaction has already
    /// read keeps the sequence it was read at, so a rollback can
    /// neither rewind a later read of that key nor launder a write
    /// that landed around the lock manager in the meantime.
    pub fn rollback_to_savepoint(&mut self) -> TxResult<()> {
        let sp = self.savepoints.pop().ok_or(TransactionError::NoSavepoint)?;
        self.writes = TxnBuffer::new(self.keys_inline);
        for (key, value) in sp.writes {
            self.writes.insert(key, value);
        }
        self.range_deletes = SegQueue::new();
        for entry in sp.range_deletes {
            self.range_deletes.push(entry);
        }
        self.merges = SegQueue::new();
        for entry in sp.merges {
            self.merges.push(entry);
        }
        // Locks acquired after the savepoint remain held.
        let _ = sp.held_lock_count;
        Ok(())
    }

    /// Commit the transaction. Every key in the validation set is
    /// re-checked against the earliest sequence this transaction
    /// observed it at, and any conflict surfaces as
    /// [`TransactionError::Conflict`]; otherwise the buffered
    /// writes are applied atomically.
    ///
    /// An optimistic transaction validates every key it wrote or
    /// read through [`Transaction::get_for_update`] against its
    /// begin snapshot, so the check catches any concurrent writer. A
    /// pessimistic transaction validates every key it read and then
    /// wrote, plus every key it read through `get_for_update`,
    /// against the sequence that read observed. The check passes
    /// whenever every writer went through the lock manager and fires
    /// for a write that bypassed it or that landed before the lock
    /// was taken. A pessimistic blind write is not validated: the
    /// key lock orders it, and there is no read to lose.
    ///
    /// A commit that carries writes passes the same admission as a plain
    /// write with [`crate::WriteOptions::default`], in the same order: key
    /// and value sizes are validated first, along with the size of the
    /// record the commit will log (at most 1 GiB), so an oversized commit
    /// is rejected before it waits, then it blocks while a stop trigger is
    /// active and pays the slowdown delay while a slowdown trigger is
    /// active, before the conflict check and before any commit lock is
    /// taken. A wait that admits the commit is charged to
    /// [`crate::Ticker::WriteStallMicros`]. A stall the engine cannot
    /// relieve surfaces as [`TransactionError::Io`] carrying the same
    /// reason a plain write reports through [`crate::Error::Busy`]. A
    /// commit too large to log fails with [`TransactionError::Io`] of kind
    /// [`std::io::ErrorKind::InvalidInput`] and applies nothing; split it
    /// into smaller transactions. A commit with no buffered writes never
    /// waits: it validates its read set and returns. A pessimistic
    /// transaction keeps its key locks for the duration of the wait.
    pub fn commit(mut self) -> TxResult<()> {
        let result = self.commit_inner();
        self.resolved = true;
        // Drop runs the cleanup (release locks, release snapshot).
        result
    }

    /// Discard the transaction's buffered writes and release any
    /// pessimistic locks. Equivalent to dropping the transaction,
    /// but surfaces as an explicit call in user code.
    pub fn rollback(mut self) {
        self.resolved = true;
        self.release_resources();
    }

    fn commit_inner(&mut self) -> TxResult<()> {
        // `&mut self` here means buffering is over, so draining the
        // concurrent buffers cannot race. Every buffer is moved out
        // rather than copied: the transaction is being consumed, so
        // nothing needs the buffers' own copies afterwards, and draining
        // hands over the stored keys and values instead of cloning each
        // one.
        //
        // A buffer yields the newest write of a key first, with the ones
        // it replaced behind it, so the first value seen for a key is the
        // one that commits. Collecting into a `BTreeMap` with `or_insert`
        // keeps that value and restores the key order the engine applies
        // them in.
        let mut writes: BTreeMap<Vec<u8>, Option<Vec<u8>>> = BTreeMap::new();
        for (key, value) in self.writes.drain() {
            writes.entry(key).or_insert(value);
        }
        let range_deletes = drain(&self.range_deletes);
        let merges = drain(&self.merges);
        let tracked = self.tracked.drain();
        let mut checks = self.validation_set(tracked, &writes, &merges);
        // Behind the `take`, not threaded through `validation_set`, so a
        // transaction that never scans (the common case) pays no `Vec`
        // round trip for an empty run list on its commit path.
        if let Some(runs) = self.scan_runs.take() {
            let runs = drain(&runs);
            scan_range::cover(
                &mut checks.reads,
                &runs,
                &writes,
                &merges,
                self.snapshot_seq,
            );
        }

        // The write-stall admission (same order as a plain write with
        // `WriteOptions::default()`: closed/read-only, then size
        // validation, then the stall wait) runs inside
        // `commit_optimistic`, after its own `ensure_writable` and
        // `validate_ops_sizes` and before the pipeline mutex, gated on
        // the commit carrying an op. See the comment there for why.
        let outcome = self
            .engine
            .commit_with_conflict_check(&checks, writes, range_deletes, merges, self.durability)
            .map_err(TransactionError::Io)?;
        match outcome {
            CommitOutcome::Ok => Ok(()),
            CommitOutcome::Conflict {
                key,
                observed_seq,
                latest_seq,
            } => Err(TransactionError::Conflict {
                key: strip_cf_prefix(key),
                observed_seq,
                latest_seq,
            }),
        }
    }

    /// What this commit validates beyond the keys it writes: every tracked
    /// read the isolation level cares about, at the earliest sequence the
    /// transaction observed it, plus the anchor the written keys are checked
    /// against.
    ///
    /// The size of this set *is* the isolation level:
    ///
    /// * [`IsolationLevel::ReadCommitted`] validates only what the
    ///   transaction wrote, so a read it did not write is never checked.
    /// * [`IsolationLevel::SnapshotIsolation`] adds keys read through
    ///   `get_for_update`, which is what stops a lost update. A plain
    ///   read is still unvalidated, which is what leaves write skew
    ///   reachable.
    /// * [`IsolationLevel::Serializable`] adds every remaining read, so
    ///   no anti-dependency edge can form unseen.
    ///
    /// Optimistic: the written and merged keys are validated against the
    /// begin snapshot; a key that was also read is validated once, as the
    /// read. Pessimistic: written keys are not validated (`writes_at` is
    /// `None`), the key lock already orders them and there is no read for a
    /// concurrent writer to invalidate.
    ///
    /// This set does not yet account for what a transactional scan walked;
    /// `commit_inner` folds that in afterward with `scan_range::cover`,
    /// skipped entirely when the transaction ran no scan.
    fn validation_set(
        &self,
        mut tracked: Vec<(Vec<u8>, Arc<KeyState>)>,
        writes: &BTreeMap<Vec<u8>, Option<Vec<u8>>>,
        merges: &[(Vec<u8>, Vec<u8>)],
    ) -> ValidationSet {
        let optimistic = matches!(self.mode, TxMode::Optimistic);
        let serializable = self.isolation == IsolationLevel::Serializable;
        let read_committed = self.isolation == IsolationLevel::ReadCommitted;
        // The drain yields the newest node first and a stable sort keeps that
        // within a key, so dedup keeps the cell every reader of the key used
        // (`get_or_insert` settles a race by re-reading, newest first).
        tracked.sort_by(|a, b| a.0.cmp(&b.0));
        tracked.dedup_by(|later, first| later.0 == first.0);
        let reads = tracked
            .into_iter()
            .filter(|(key, state)| {
                let written =
                    writes.contains_key(key) || merges.iter().any(|(merged, _)| merged == key);
                if serializable {
                    // Every read, whether or not the transaction wrote it.
                    true
                } else if read_committed {
                    written
                } else {
                    state.for_update.load(Ordering::Acquire) || written
                }
            })
            // Any read at all, whatever the level. This flag exists to
            // stop an idempotent-write elision at commit, and the
            // equivalence that elision rests on holds only for a write
            // nobody derived from a read.
            //
            // A read-modify-write is the counterexample: two transactions
            // read a counter at 5 and both write 6. The writes are
            // byte-identical, so eliding the second lets both commit and
            // the counter advances once, losing an increment. No serial
            // order produces that: run second, the transaction reads 6 and
            // writes 7. `first_read_seq` anchors the check at the read for
            // exactly this reason, and honouring the anchor is what makes
            // the abort correct.
            .map(|(key, state)| ConflictKey {
                key,
                observed_seq: state.first_read_seq,
            })
            .collect();
        ValidationSet {
            reads,
            writes_at: optimistic.then_some(self.snapshot_seq),
        }
    }

    /// Take `key`'s exclusive lock in pessimistic mode. Returns
    /// `true` when this transaction already held it. A no-op for an
    /// optimistic transaction, which takes no locks.
    fn lock_key(&self, key: &[u8]) -> TxResult<bool> {
        match self.mode {
            TxMode::Optimistic => Ok(false),
            TxMode::Pessimistic { tx_id } => self.acquire_lock(key, tx_id),
        }
    }

    /// Sequence a fresh read of `key` is anchored at, given whether
    /// this transaction already held the key's lock.
    ///
    /// The pessimistic horizon is sampled with the lock held: a
    /// committing writer publishes the engine's visible seq before
    /// releasing the lock, and the lock manager's mutex is the
    /// release/acquire edge, so nothing newer can hide behind it.
    /// Under a lock this transaction already holds nothing can have
    /// advanced, so the anchor recorded then still stands.
    fn read_horizon(&self, key: &[u8], already_held: bool) -> u64 {
        match self.mode {
            TxMode::Optimistic => self.snapshot_seq,
            TxMode::Pessimistic { .. } => {
                if already_held && let Some(state) = self.tracked.get(key) {
                    return state.read_seq.load(Ordering::Acquire);
                }
                self.engine.snapshot_seq()
            }
        }
    }

    /// Record that this transaction observed `key` at `horizon` and
    /// return the sequence the read should be served at.
    ///
    /// `first_read_seq` keeps the earliest observation, because that
    /// is the read a later write would overwrite. `read_seq` only
    /// moves forward, so promoting a key from a plain `get` to
    /// `get_for_update` never makes a later read of the same key
    /// return an older value than an earlier one.
    fn observe(&self, key: &[u8], horizon: u64, for_update: bool) -> u64 {
        let state = self
            .tracked
            .get_or_insert(key.to_vec(), Arc::new(KeyState::new(horizon, for_update)));
        // `get_or_insert` is linearizable, so exactly one caller's cell
        // wins and every other caller folds its observation into that
        // one. Each fold is monotonic, so the result does not depend on
        // the order they land in.
        // `first_read_seq` is deliberately not touched here. It is set
        // once, by whichever call created the cell, and every later read
        // of the key is served at `read_seq`, which only rises. So every
        // read this transaction made happened at or after
        // `first_read_seq`, and validating against it is the strictest
        // check that is still true. Lowering it to a later call's
        // requested horizon would invent conflicts: a pessimistic
        // `get_for_update` anchors at the lock horizon on purpose, and a
        // plain `get` afterwards is served there too, not at the older
        // begin snapshot it asked for.
        if for_update {
            state.for_update.store(true, Ordering::Release);
        }
        state
            .read_seq
            .fetch_max(horizon, Ordering::AcqRel)
            .max(horizon)
    }

    /// The sequence a scan serves `key` (CF-prefixed) at, recording nothing:
    /// the begin snapshot, or the sequence a pessimistic transaction already
    /// reads the key at because `get_for_update` promoted it, which is what
    /// [`Transaction::get`] would serve.
    ///
    /// `tracked` is walked, not indexed, below
    /// [`crate::Options::transaction_keys_inline`] entries, so a `tracked.get`
    /// here would cost O(tracked keys) per yielded key. `promoted_seq` makes
    /// the common case (no `get_for_update` promoted anything past the begin
    /// snapshot) one Acquire load instead: no cell can have `read_seq` above
    /// `snapshot_seq` then, so a lookup could only ever confirm what the
    /// caller already knows.
    ///
    /// When a promotion might exist, this indexes `tracked` right here,
    /// before the lookup, rather than only once when the stream was built:
    /// `scan_stream_in` and `get_for_update` both take `&self`, so a
    /// promotion can land after the stream already exists, and indexing at
    /// construction alone would leave every later key walking the list.
    /// Doing it per key instead of once still costs O(1) per call past the
    /// first: `ensure_indexed` is a single `OnceLock::get` once the index is
    /// built, and it is built at most once (the `OnceLock` inside it makes a
    /// second, concurrent build a no-op). Sound with concurrent promotions:
    /// `get_for_update` inserts into `tracked` before it raises
    /// `promoted_seq` (`Release`-ordered by the `fetch_max` below, paired
    /// with this `Acquire` load), so once this load observes a promotion,
    /// that promotion's entry is already linked into `tracked`'s list and
    /// visible to the index build this call triggers.
    fn scan_read_seq(&self, key: &[u8]) -> u64 {
        match self.mode {
            // An optimistic transaction reads every key at its begin
            // snapshot: `read_horizon` never returns anything else.
            TxMode::Optimistic => self.snapshot_seq,
            TxMode::Pessimistic { .. } => {
                if self.promoted_seq.load(Ordering::Acquire) <= self.snapshot_seq {
                    return self.snapshot_seq;
                }
                self.tracked.ensure_indexed();
                self.tracked.get(key).map_or(self.snapshot_seq, |state| {
                    state
                        .read_seq
                        .load(Ordering::Acquire)
                        .max(self.snapshot_seq)
                })
            }
        }
    }

    /// Register a stretch a scan began, so commit sees it even if the stream
    /// is never closed.
    fn record_scan_run(&self, run: Arc<ScanRun>) {
        self.scan_runs
            .get_or_init(|| Box::new(SegQueue::new()))
            .push(run);
    }

    /// Acquire `key`'s exclusive lock. Returns `true` when this
    /// transaction already held it.
    fn acquire_lock(&self, key: &[u8], tx_id: u64) -> TxResult<bool> {
        let Some(lm) = self.lock_manager.as_ref() else {
            return Ok(false);
        };
        if self.held_locks.get(key).is_some() {
            return Ok(true);
        }
        lm.acquire(key, tx_id, self.lock_timeout)
            .map_err(|_| TransactionError::Busy(strip_cf_prefix(key.to_vec())))?;
        self.held_locks.insert(key.to_vec(), ());
        Ok(false)
    }

    fn release_resources(&mut self) {
        if self.resources_released {
            return;
        }
        self.resources_released = true;
        if let Some(lm) = self.lock_manager.as_ref()
            && let TxMode::Pessimistic { tx_id } = self.mode
        {
            for (key, ()) in self.held_locks.drain() {
                lm.release(&key, tx_id);
            }
        }
        self.engine.release_snapshot(self.snapshot_seq);
    }
}

/// The transaction's own writes for a range, sorted and ready to merge.
/// `Some` is a put, `None` a delete.
type BufferedWrites = std::iter::Peekable<std::vec::IntoIter<(Vec<u8>, Option<Vec<u8>>)>>;

/// A transaction's view of a key range, streamed.
///
/// Merges the transaction's buffered writes over a snapshot cursor, so a
/// scan inside a transaction sees its own uncommitted writes without
/// either side being materialized: the database side is a cursor, and the
/// buffered side is bounded by what this transaction wrote.
///
/// A buffered delete hides the snapshot's entry for that key, and a
/// buffered put replaces it. Each unbroken stretch of snapshot entries it
/// yields is recorded in the transaction once, as the first and the last
/// key of the stretch (per key as well at Serializable); entries that come
/// from the transaction's own writes are not recorded and end the stretch.
pub struct TxnScanStream<'txn> {
    /// The transaction this scan reads for: its stretches are registered
    /// there, and a key it already promoted through `get_for_update` is
    /// served at that key's read sequence.
    txn: &'txn Transaction<'txn>,
    cursor: crate::CfIter<'txn>,
    cursor_done: bool,
    buffered: BufferedWrites,
    /// Inclusive lower bound, user-visible form. Where a reverse walk stops.
    start: Option<Vec<u8>>,
    /// Exclusive upper bound, user-visible form. Where a forward walk stops.
    end: Option<Vec<u8>>,
    reverse: bool,
    /// The stretch of snapshot keys being yielded. Dropping it closes it.
    run: Option<OpenRun>,
    /// The key being handed out, CF-prefixed, reused across yields.
    probe: Vec<u8>,
    /// A read of a key served past the begin snapshot that failed.
    error: Option<std::io::Error>,
}

impl TxnScanStream<'_> {
    /// Why the snapshot side of the walk stopped.
    ///
    /// `Ok(())` means the range ended. An error means it did not: the
    /// entries handed out are the transaction's buffered writes merged with
    /// a *prefix* of what the database holds, and the rest was never read,
    /// or a read of a key this transaction already locked through
    /// [`Transaction::get_for_update`] failed.
    ///
    /// A merged stream cannot report this any other way. `Iterator` has
    /// nowhere to put a failure, and a cursor that dies mid-range goes
    /// invalid exactly as one that reached the end does, after which the
    /// merge finishes on the buffered side alone and looks complete. Check
    /// this after iterating whenever a missing row would be worse than an
    /// error. It is the same contract as [`crate::ScanStream::status`].
    pub fn status(&self) -> Result<()> {
        if let Some(e) = &self.error {
            return Err(std::io::Error::new(e.kind(), e.to_string()).into());
        }
        self.cursor.status()
    }

    /// The next snapshot entry inside the range, or `None` past the end.
    ///
    /// Whichever way the walk runs, it stops at the bound it is running
    /// towards: `end` is exclusive going forward, `start` inclusive going
    /// back.
    fn peek_cursor(&mut self) -> Option<Vec<u8>> {
        if self.cursor_done || !self.cursor.valid() {
            // The cursor going invalid means one of two things and this is
            // where they become indistinguishable: the range ended, or the
            // walk failed and the merge is about to finish on the buffered
            // side as though the database held nothing more. Say it out
            // loud; `status` returns it to a caller that checks.
            if let Err(e) = self.cursor.status() {
                tracing::error!(
                    error = %e,
                    "transaction scan ended early: the snapshot cursor failed \
                     mid-range, so the rows returned are a prefix and not the range"
                );
            }
            return None;
        }
        let key = self.cursor.key()?.to_vec();
        let past_bound = if self.reverse {
            self.start
                .as_ref()
                .is_some_and(|start| key.as_slice() < start.as_slice())
        } else {
            self.end
                .as_ref()
                .is_some_and(|end| key.as_slice() >= end.as_slice())
        };
        if past_bound {
            self.cursor_done = true;
            return None;
        }
        Some(key)
    }

    /// Step the snapshot cursor the way this scan runs.
    fn step_cursor(&mut self) {
        if self.reverse {
            self.cursor.prev();
        } else {
            self.cursor.next();
        }
    }

    /// Whether `first` comes before `second` in this scan's order.
    fn precedes(&self, first: &[u8], second: &[u8]) -> std::cmp::Ordering {
        if self.reverse {
            second.cmp(first)
        } else {
            first.cmp(second)
        }
    }

    /// Hand out the entry under the cursor and record the read.
    ///
    /// `Break(Some(entry))` hands `entry` out, `Break(None)` ends the stream,
    /// `Continue` moves on to the next entry.
    ///
    /// A key a pessimistic transaction already promoted past the begin
    /// snapshot through `get_for_update` is served where `get` serves it, at
    /// its `read_seq`, and is skipped when nothing is visible there. Its cell
    /// already records that read, so it ends the current stretch instead of
    /// joining it: the stretch must hold only keys observed at the begin
    /// snapshot. Every other key is served from the cursor at the begin
    /// snapshot and extends the stretch (starting one, and registering it,
    /// on the first such key). At Serializable the key is also recorded per
    /// key through `observe`.
    fn yield_cursor(&mut self, key: Vec<u8>) -> ControlFlow<Option<(Vec<u8>, DbSlice)>> {
        let txn = self.txn;
        self.probe.clear();
        self.probe.extend_from_slice(&DEFAULT_CF_ID.to_be_bytes());
        self.probe.extend_from_slice(&key);
        let read_seq = txn.scan_read_seq(&self.probe);
        if read_seq > txn.snapshot_seq {
            self.step_cursor();
            self.run = None;
            return match txn.engine.get_slice_at(&self.probe, read_seq) {
                Ok(Some(value)) => ControlFlow::Break(Some((key, value))),
                Ok(None) => ControlFlow::Continue(()),
                Err(e) => {
                    tracing::error!(
                        error = %e,
                        "transaction scan ended early: a read failed mid-range, \
                         so the rows returned are a prefix and not the range"
                    );
                    self.error = Some(e);
                    self.cursor_done = true;
                    ControlFlow::Continue(())
                }
            };
        }
        let Some(value) = self.cursor.value_slice() else {
            self.run = None;
            return ControlFlow::Break(None);
        };
        self.step_cursor();
        match &mut self.run {
            Some(open) => open.extend(&self.probe),
            None => {
                let (run, open) = OpenRun::start(&self.probe, self.reverse);
                txn.record_scan_run(run);
                self.run = Some(open);
            }
        }
        if txn.isolation == IsolationLevel::Serializable {
            txn.observe(&self.probe, txn.snapshot_seq, false);
        }
        ControlFlow::Break(Some((key, value)))
    }
}

impl Iterator for TxnScanStream<'_> {
    type Item = (Vec<u8>, DbSlice);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let cursor_key = self.peek_cursor();
            // Buffered keys carry the CF prefix; the cursor reports the
            // user-visible key, so compare on the stripped form.
            let buffered_key = self.buffered.peek().map(|(key, _)| key[4..].to_vec());

            match (cursor_key, buffered_key) {
                (None, None) => {
                    self.run = None;
                    return None;
                }
                // Only the transaction has this key.
                (None, Some(_)) => {
                    self.run = None;
                    let (key, value) = self.buffered.next()?;
                    if let Some(value) = value {
                        return Some((key[4..].to_vec(), DbSlice::from(value)));
                    }
                }
                // Only the database has it.
                (Some(key), None) => {
                    if let ControlFlow::Break(item) = self.yield_cursor(key) {
                        return item;
                    }
                }
                (Some(ckey), Some(bkey)) => match self.precedes(&ckey, &bkey) {
                    std::cmp::Ordering::Less => {
                        if let ControlFlow::Break(item) = self.yield_cursor(ckey) {
                            return item;
                        }
                    }
                    std::cmp::Ordering::Greater => {
                        self.run = None;
                        let (key, value) = self.buffered.next()?;
                        if let Some(value) = value {
                            return Some((key[4..].to_vec(), DbSlice::from(value)));
                        }
                    }
                    // The transaction wrote a key the snapshot also has,
                    // so its write wins and the snapshot entry is skipped
                    // whether that write was a put or a delete.
                    std::cmp::Ordering::Equal => {
                        self.run = None;
                        self.step_cursor();
                        let (key, value) = self.buffered.next()?;
                        if let Some(value) = value {
                            return Some((key[4..].to_vec(), DbSlice::from(value)));
                        }
                    }
                },
            }
        }
    }
}

impl std::fmt::Debug for TxnScanStream<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TxnScanStream").finish_non_exhaustive()
    }
}

/// Empty a queue into a `Vec`, preserving push order.
///
/// Only ever called with exclusive access to the transaction, so no
/// producer can be pushing concurrently and the result is the complete
/// buffer rather than a snapshot of one.
fn drain<T: 'static>(queue: &SegQueue<T>) -> Vec<T> {
    let mut drained = Vec::with_capacity(queue.len());
    while let Some(entry) = queue.pop() {
        drained.push(entry);
    }
    drained
}

/// Drop the 4-byte column-family prefix that `prefix_key` adds so
/// errors surface the key the caller passed in.
fn strip_cf_prefix(key: Vec<u8>) -> Vec<u8> {
    if key.len() >= 4 {
        key[4..].to_vec()
    } else {
        key
    }
}

/// A [`Transaction`] bundled with an owning handle on the database that
/// began it.
///
/// [`Transaction`] carries a `'db` lifetime, which makes it impossible to
/// place in a `'static` container such as a boxed trait object. The
/// lifetime is the only thing tying it to its database: every field it
/// holds is already an `Arc`. `OwnedTransaction` makes that ownership
/// explicit by keeping an `Arc` on the database alongside the
/// transaction, so the database cannot be dropped out from under an
/// in-flight transaction and the pair can be stored and moved freely.
///
/// Deref gives the full [`Transaction`] surface; [`Self::commit`] and
/// [`Self::rollback`] are re-stated here because they consume the
/// transaction and cannot go through `Deref`.
pub struct OwnedTransaction {
    /// Declared first so it drops first: the transaction releases its
    /// snapshot pin and any held locks before the database handle goes.
    txn: Transaction<'static>,
    _db: Arc<dyn core::any::Any + Send + Sync>,
}

impl OwnedTransaction {
    fn new(txn: Transaction<'static>, db: Arc<dyn core::any::Any + Send + Sync>) -> Self {
        Self { txn, _db: db }
    }

    /// Validate and apply the transaction. See [`Transaction::commit`].
    pub fn commit(self) -> TxResult<()> {
        self.txn.commit()
    }

    /// Discard the transaction. See [`Transaction::rollback`].
    pub fn rollback(self) {
        self.txn.rollback();
    }
}

impl core::ops::Deref for OwnedTransaction {
    type Target = Transaction<'static>;

    fn deref(&self) -> &Self::Target {
        &self.txn
    }
}

impl core::ops::DerefMut for OwnedTransaction {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.txn
    }
}

impl std::fmt::Debug for OwnedTransaction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OwnedTransaction").finish_non_exhaustive()
    }
}

impl Drop for Transaction<'_> {
    fn drop(&mut self) {
        if !self.resolved {
            self.resolved = true;
        }
        self.release_resources();
    }
}

// ─── LockManager ────────────────────────────────────────────────────────────

/// Single-shard exclusive lock manager used by [`TransactionDb`].
///
/// The hash map maps user keys to the tx id that currently holds
/// the lock. Acquires block on the condvar until the lock is free
/// or the deadline expires. Sharding the map for higher
/// concurrency is a future optimization: regolith transactions today
/// expect low-to-moderate concurrency, so a single mutex is fine.
struct LockManager {
    locks: Mutex<HashMap<Vec<u8>, u64>>,
    cvar: Condvar,
}

impl LockManager {
    fn new() -> Self {
        Self {
            locks: Mutex::new(HashMap::new()),
            cvar: Condvar::new(),
        }
    }

    /// Acquire an exclusive lock on `key` for `tx_id`. Blocks up
    /// to `timeout`. Returns `Err(())` on timeout.
    fn acquire(&self, key: &[u8], tx_id: u64, timeout: Duration) -> std::result::Result<(), ()> {
        // Microseconds from the platform clock. `None` means this
        // platform cannot measure a timeout at all, which is the same
        // single-threaded platform on which no other transaction can
        // be holding the lock, so the wait simply is not bounded by a
        // deadline there.
        let deadline =
            crate::env::platform_micros().map(|now| now.saturating_add(timeout.as_micros() as u64));
        let mut guard = self.locks.lock();
        loop {
            match guard.get(key) {
                Some(&holder) if holder == tx_id => {
                    // Re-entrant: same transaction already holds the
                    // lock. Treat as a success.
                    return Ok(());
                }
                Some(_) => {
                    let remaining = match (deadline, crate::env::platform_micros()) {
                        (Some(deadline), Some(now)) => {
                            if now >= deadline {
                                return Err(());
                            }
                            Duration::from_micros(deadline - now)
                        }
                        _ => timeout,
                    };
                    let (next, result) = self
                        .cvar
                        .wait_timeout(guard, remaining)
                        .unwrap_or_else(std::sync::PoisonError::into_inner);
                    guard = next;
                    if result.timed_out() && guard.get(key).is_some_and(|&h| h != tx_id) {
                        return Err(());
                    }
                }
                None => {
                    guard.insert(key.to_vec(), tx_id);
                    return Ok(());
                }
            }
        }
    }

    /// Release `key`'s lock if held by `tx_id`. Notifies any
    /// waiters.
    fn release(&self, key: &[u8], tx_id: u64) {
        let mut guard = self.locks.lock();
        if let Some(&holder) = guard.get(key)
            && holder == tx_id
        {
            guard.remove(key);
            self.cvar.notify_all();
        }
    }
}

#[cfg(test)]
mod validation_set_tests;

#[cfg(test)]
mod record_limit_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Statistics, Ticker};
    use tempfile::TempDir;

    fn opt_db() -> (OptimisticTransactionDb, TempDir) {
        let dir = TempDir::new().unwrap();
        let db = OptimisticTransactionDb::open(dir.path(), Options::default()).unwrap();
        (db, dir)
    }

    fn pes_db() -> (TransactionDb, TempDir) {
        let dir = TempDir::new().unwrap();
        let db = TransactionDb::open(dir.path(), Options::default()).unwrap();
        (db, dir)
    }

    // ── Optimistic flavor ───────────────────────────────────────────────

    #[test]
    fn optimistic_basic_put_commit_read() {
        let (db, _dir) = opt_db();
        let tx = db.begin_transaction();
        tx.put(b"k", b"v").unwrap();
        tx.commit().unwrap();
        assert_eq!(db.db().get(b"k").unwrap(), Some(b"v".to_vec()));
    }

    #[test]
    fn optimistic_read_your_own_writes() {
        let (db, _dir) = opt_db();
        db.db().put(b"k", b"initial").unwrap();
        let tx = db.begin_transaction();
        assert_eq!(tx.get(b"k").unwrap(), Some(b"initial".to_vec()));
        tx.put(b"k", b"staged").unwrap();
        // Tx sees its own write.
        assert_eq!(tx.get(b"k").unwrap(), Some(b"staged".to_vec()));
        // Outside the tx the old value is still visible until commit.
        assert_eq!(db.db().get(b"k").unwrap(), Some(b"initial".to_vec()));
        tx.commit().unwrap();
        assert_eq!(db.db().get(b"k").unwrap(), Some(b"staged".to_vec()));
    }

    #[test]
    fn optimistic_rollback_discards_writes() {
        let (db, _dir) = opt_db();
        let tx = db.begin_transaction();
        tx.put(b"k", b"never").unwrap();
        tx.rollback();
        assert_eq!(db.db().get(b"k").unwrap(), None);
    }

    #[test]
    fn optimistic_rollback_releases_shared_snapshot_pin_once() {
        let (db, _dir) = opt_db();
        let tx1 = db.begin_transaction();
        let tx2 = db.begin_transaction();
        assert_eq!(db.db().get_int_property("regolith.num-snapshots"), Some(2));

        tx1.rollback();
        assert_eq!(db.db().get_int_property("regolith.num-snapshots"), Some(1));

        drop(tx2);
        assert_eq!(db.db().get_int_property("regolith.num-snapshots"), Some(0));
    }

    #[test]
    fn optimistic_conflict_detected() {
        let (db, _dir) = opt_db();
        db.db().put(b"k", b"v0").unwrap();
        let tx1 = db.begin_transaction();
        assert_eq!(tx1.get(b"k").unwrap(), Some(b"v0".to_vec()));
        // Concurrent writer bumps the key.
        db.db().put(b"k", b"v1").unwrap();
        tx1.put(b"k", b"v2").unwrap();
        match tx1.commit() {
            Err(TransactionError::Conflict { key, .. }) => {
                assert_eq!(key, b"k".to_vec());
            }
            other => panic!("expected conflict, got {other:?}"),
        }
        // db still reflects the concurrent writer's value.
        assert_eq!(db.db().get(b"k").unwrap(), Some(b"v1".to_vec()));
    }

    #[test]
    fn optimistic_get_for_update_tracks_conflicts() {
        let (db, _dir) = opt_db();
        db.db().put(b"k", b"v0").unwrap();
        let tx = db.begin_transaction();
        assert_eq!(tx.get_for_update(b"k").unwrap(), Some(b"v0".to_vec()));
        // Concurrent writer invalidates the read.
        db.db().put(b"k", b"v1").unwrap();
        // The tx didn't buffer a write on k, but it flagged k for
        // conflict detection, so commit must still detect.
        tx.put(b"other", b"stuff").unwrap();
        match tx.commit() {
            Err(TransactionError::Conflict { key, .. }) => {
                assert_eq!(key, b"k".to_vec());
            }
            other => panic!("expected conflict, got {other:?}"),
        }
    }

    #[test]
    fn optimistic_conflict_reports_the_lowest_conflicting_key() {
        let (db, _dir) = opt_db();
        db.db().put(b"a", b"v0").unwrap();
        db.db().put(b"z", b"v0").unwrap();
        let tx = db.begin_transaction();
        // Tracked in the reverse of their sort order.
        tx.get_for_update(b"z").unwrap();
        tx.get_for_update(b"a").unwrap();
        db.db().put(b"z", b"v1").unwrap();
        db.db().put(b"a", b"v1").unwrap();
        match tx.commit() {
            Err(TransactionError::Conflict { key, .. }) => assert_eq!(key, b"a".to_vec()),
            other => panic!("expected conflict, got {other:?}"),
        }
    }

    #[test]
    fn optimistic_no_conflict_passes() {
        let (db, _dir) = opt_db();
        db.db().put(b"k", b"v0").unwrap();
        let tx = db.begin_transaction();
        tx.put(b"other", b"stuff").unwrap();
        tx.commit().unwrap();
        assert_eq!(db.db().get(b"other").unwrap(), Some(b"stuff".to_vec()));
    }

    #[test]
    fn optimistic_snapshot_isolation_reads() {
        let (db, _dir) = opt_db();
        db.db().put(b"k", b"v0").unwrap();
        let tx = db.begin_transaction();
        db.db().put(b"k", b"v1").unwrap();
        // Tx is anchored at the seq before the second put.
        assert_eq!(tx.get(b"k").unwrap(), Some(b"v0".to_vec()));
    }

    #[test]
    fn optimistic_savepoint_rollback() {
        let (db, _dir) = opt_db();
        let mut tx = db.begin_transaction();
        tx.put(b"a", b"1").unwrap();
        tx.set_savepoint();
        tx.put(b"b", b"2").unwrap();
        tx.put(b"c", b"3").unwrap();
        tx.rollback_to_savepoint().unwrap();
        // a survives, b and c are rolled back.
        assert_eq!(tx.get(b"a").unwrap(), Some(b"1".to_vec()));
        assert_eq!(tx.get(b"b").unwrap(), None);
        assert_eq!(tx.get(b"c").unwrap(), None);
        tx.commit().unwrap();
        assert_eq!(db.db().get(b"a").unwrap(), Some(b"1".to_vec()));
        assert_eq!(db.db().get(b"b").unwrap(), None);
    }

    #[test]
    fn optimistic_rollback_to_savepoint_without_savepoint_errors() {
        let (db, _dir) = opt_db();
        let mut tx = db.begin_transaction();
        assert!(matches!(
            tx.rollback_to_savepoint(),
            Err(TransactionError::NoSavepoint)
        ));
    }

    #[test]
    fn optimistic_delete_commit() {
        let (db, _dir) = opt_db();
        db.db().put(b"k", b"v").unwrap();
        let tx = db.begin_transaction();
        tx.delete(b"k").unwrap();
        tx.commit().unwrap();
        assert_eq!(db.db().get(b"k").unwrap(), None);
    }

    #[test]
    fn optimistic_range_delete_is_rejected() {
        let (db, _dir) = opt_db();
        let tx = db.begin_transaction();

        assert!(matches!(
            tx.delete_range(b"a", b"z"),
            Err(TransactionError::UnsupportedRangeDelete)
        ));
        assert!(tx.delete_range(b"z", b"a").is_ok());
    }

    // ── Pessimistic flavor ──────────────────────────────────────────────

    #[test]
    fn pessimistic_basic_put_commit_read() {
        let (db, _dir) = pes_db();
        let tx = db.begin_transaction();
        tx.put(b"k", b"v").unwrap();
        tx.commit().unwrap();
        assert_eq!(db.db().get(b"k").unwrap(), Some(b"v".to_vec()));
    }

    #[test]
    fn pessimistic_range_delete_is_rejected() {
        let (db, _dir) = pes_db();
        let tx = db.begin_transaction();

        assert!(matches!(
            tx.delete_range(b"a", b"z"),
            Err(TransactionError::UnsupportedRangeDelete)
        ));
        assert!(tx.delete_range(b"z", b"a").is_ok());
    }

    #[test]
    fn pessimistic_lock_blocks_second_writer() {
        let (db, _dir) = pes_db();
        let db = Arc::new(db);
        let tx1 = db.begin_transaction();
        tx1.put(b"k", b"v1").unwrap();
        // Second tx with a short timeout must fail to lock `k`.
        let db2 = Arc::clone(&db);
        let join = std::thread::spawn(move || {
            // The default lock timeout is 1s, which is too long for
            // the test, so recreate the transaction with a shorter
            // manual lock acquisition via `get_for_update`. We
            // rely on acquire_lock using the DB's
            // configured timeout; so we just do a normal put and
            // expect `Busy`.
            let tx2 = db2.begin_transaction();
            tx2.put(b"k", b"v2")
        });
        // Give tx2 some time to actually start waiting.
        std::thread::sleep(std::time::Duration::from_millis(50));
        // Commit tx1: lock releases, tx2 should now succeed.
        tx1.commit().unwrap();
        let result = join.join().unwrap();
        assert!(result.is_ok(), "tx2 put should succeed once tx1 commits");
    }

    #[test]
    fn pessimistic_lock_timeout_returns_busy() {
        let dir = TempDir::new().unwrap();
        let db = TransactionDb::open(dir.path(), Options::default())
            .unwrap()
            .with_lock_timeout(Duration::from_millis(50));
        let db = Arc::new(db);
        // tx1 grabs the lock and holds it.
        let tx1 = db.begin_transaction();
        tx1.put(b"k", b"v1").unwrap();
        let db2 = Arc::clone(&db);
        let join = std::thread::spawn(move || {
            let tx2 = db2.begin_transaction();
            tx2.put(b"k", b"v2")
        });
        // tx2 should time out within ~50ms.
        let result = join.join().unwrap();
        assert!(matches!(result, Err(TransactionError::Busy(_))));
        // Cleanup.
        tx1.rollback();
    }

    #[test]
    fn pessimistic_reentrant_lock() {
        let (db, _dir) = pes_db();
        let tx = db.begin_transaction();
        tx.put(b"k", b"v1").unwrap();
        // Re-lock (via a second put) must not deadlock against
        // itself.
        tx.put(b"k", b"v2").unwrap();
        tx.get_for_update(b"k").unwrap();
        tx.commit().unwrap();
        assert_eq!(db.db().get(b"k").unwrap(), Some(b"v2".to_vec()));
    }

    #[test]
    fn pessimistic_rollback_releases_locks() {
        let (db, _dir) = pes_db();
        let db = Arc::new(db);
        let tx1 = db.begin_transaction();
        tx1.put(b"k", b"v1").unwrap();
        tx1.rollback();
        // New tx must now be able to grab the lock without blocking.
        let tx2 = db.begin_transaction();
        tx2.put(b"k", b"v2").unwrap();
        tx2.commit().unwrap();
        assert_eq!(db.db().get(b"k").unwrap(), Some(b"v2".to_vec()));
    }

    #[test]
    fn pessimistic_rollback_releases_shared_snapshot_pin_once() {
        let (db, _dir) = pes_db();
        let tx1 = db.begin_transaction();
        let tx2 = db.begin_transaction();
        assert_eq!(db.db().get_int_property("regolith.num-snapshots"), Some(2));

        tx1.rollback();
        assert_eq!(db.db().get_int_property("regolith.num-snapshots"), Some(1));

        drop(tx2);
        assert_eq!(db.db().get_int_property("regolith.num-snapshots"), Some(0));
    }

    #[test]
    fn pessimistic_drop_releases_locks() {
        let (db, _dir) = pes_db();
        let db = Arc::new(db);
        {
            let tx1 = db.begin_transaction();
            tx1.put(b"k", b"v1").unwrap();
            // tx1 dropped here without explicit rollback.
        }
        let tx2 = db.begin_transaction();
        tx2.put(b"k", b"v2").unwrap();
        tx2.commit().unwrap();
        assert_eq!(db.db().get(b"k").unwrap(), Some(b"v2".to_vec()));
    }

    #[test]
    fn pessimistic_read_your_own_writes() {
        let (db, _dir) = pes_db();
        db.db().put(b"k", b"initial").unwrap();
        let tx = db.begin_transaction();
        tx.put(b"k", b"staged").unwrap();
        assert_eq!(tx.get(b"k").unwrap(), Some(b"staged".to_vec()));
        tx.commit().unwrap();
    }

    #[test]
    fn pessimistic_get_for_update_locks() {
        let dir = TempDir::new().unwrap();
        let db = Arc::new(
            TransactionDb::open(dir.path(), Options::default())
                .unwrap()
                .with_lock_timeout(Duration::from_millis(50)),
        );
        db.db().put(b"k", b"v0").unwrap();
        let tx1 = db.begin_transaction();
        assert_eq!(tx1.get_for_update(b"k").unwrap(), Some(b"v0".to_vec()));
        // Concurrent tx2 can't touch k.
        let db2 = Arc::clone(&db);
        let join = std::thread::spawn(move || {
            let tx2 = db2.begin_transaction();
            tx2.put(b"k", b"v1")
        });
        let result = join.join().unwrap();
        assert!(matches!(result, Err(TransactionError::Busy(_))));
        tx1.rollback();
    }

    #[test]
    fn pessimistic_savepoint_keeps_locks_but_rolls_back_writes() {
        let (db, _dir) = pes_db();
        let mut tx = db.begin_transaction();
        tx.put(b"a", b"1").unwrap();
        tx.set_savepoint();
        tx.put(b"b", b"2").unwrap();
        tx.rollback_to_savepoint().unwrap();
        // a's put survives, b's put is rolled back.
        assert_eq!(tx.get(b"a").unwrap(), Some(b"1".to_vec()));
        assert_eq!(tx.get(b"b").unwrap(), None);
        tx.commit().unwrap();
        assert_eq!(db.db().get(b"a").unwrap(), Some(b"1".to_vec()));
        assert_eq!(db.db().get(b"b").unwrap(), None);
    }

    #[test]
    fn pessimistic_get_for_update_sees_writes_committed_after_begin() {
        let (db, _dir) = pes_db();
        db.db().put(b"k", b"v0").unwrap();
        let tx = db.begin_transaction();
        // Lands after the transaction began, before it locks `k`.
        db.db().put(b"k", b"v1").unwrap();
        assert_eq!(tx.get_for_update(b"k").unwrap(), Some(b"v1".to_vec()));
        // A plain `get` on the locked key reads at the same horizon.
        assert_eq!(tx.get(b"k").unwrap(), Some(b"v1".to_vec()));
        tx.put(b"k", b"v2").unwrap();
        tx.commit().unwrap();
        assert_eq!(db.db().get(b"k").unwrap(), Some(b"v2".to_vec()));
    }

    #[test]
    fn pessimistic_second_locker_does_not_observe_precommit_value() {
        let (db, _dir) = pes_db();
        db.db().put(b"k", b"v0").unwrap();
        // Both transactions begin before either one commits, so both
        // are anchored at the seq where `k` is still `v0`.
        let tx1 = db.begin_transaction();
        let tx2 = db.begin_transaction();
        assert_eq!(tx1.get_for_update(b"k").unwrap(), Some(b"v0".to_vec()));
        tx1.put(b"k", b"v1").unwrap();
        tx1.commit().unwrap();
        // tx2 only now gets the lock, so it must not see `v0`.
        assert_eq!(tx2.get_for_update(b"k").unwrap(), Some(b"v1".to_vec()));
        tx2.put(b"k", b"v2").unwrap();
        tx2.commit().unwrap();
        assert_eq!(db.db().get(b"k").unwrap(), Some(b"v2".to_vec()));
    }

    #[test]
    fn pessimistic_commit_detects_write_from_outside_the_lock_manager() {
        let (db, _dir) = pes_db();
        let tx = db.begin_transaction();
        tx.get_for_update(b"k").unwrap();
        // A raw `Db` write never touches the lock manager.
        db.db().put(b"k", b"racer").unwrap();
        tx.put(b"k", b"mine").unwrap();
        match tx.commit() {
            Err(TransactionError::Conflict { key, .. }) => assert_eq!(key, b"k".to_vec()),
            other => panic!("expected conflict, got {other:?}"),
        }
        assert_eq!(db.db().get(b"k").unwrap(), Some(b"racer".to_vec()));
    }

    #[test]
    fn pessimistic_sequential_transactions_do_not_conflict() {
        let (db, _dir) = pes_db();
        let tx1 = db.begin_transaction();
        tx1.put(b"k", b"v1").unwrap();
        tx1.commit().unwrap();
        let tx2 = db.begin_transaction();
        assert_eq!(tx2.get_for_update(b"k").unwrap(), Some(b"v1".to_vec()));
        tx2.put(b"k", b"v2").unwrap();
        tx2.commit().unwrap();
        assert_eq!(db.db().get(b"k").unwrap(), Some(b"v2".to_vec()));
    }

    #[test]
    fn pessimistic_blind_put_after_external_write_is_not_a_conflict() {
        let (db, _dir) = pes_db();
        db.db().put(b"k", b"v0").unwrap();
        let tx = db.begin_transaction();
        db.db().put(b"k", b"v1").unwrap();
        // Nothing was read, so there is no read to lose: a blind write
        // is last-writer-wins against a non-transactional writer.
        tx.put(b"k", b"v2").unwrap();
        tx.commit().unwrap();
        assert_eq!(db.db().get(b"k").unwrap(), Some(b"v2".to_vec()));
    }

    #[test]
    fn pessimistic_blind_put_before_external_write_is_not_a_conflict() {
        // The mirror ordering: the external write lands after the
        // transaction has already buffered its blind write.
        let (db, _dir) = pes_db();
        db.db().put(b"k", b"v0").unwrap();
        let tx = db.begin_transaction();
        tx.put(b"k", b"v2").unwrap();
        db.db().put(b"k", b"v1").unwrap();
        tx.commit().unwrap();
        assert_eq!(db.db().get(b"k").unwrap(), Some(b"v2".to_vec()));
    }

    #[test]
    fn pessimistic_savepoint_rollback_keeps_untouched_keys_unvalidated() {
        let (db, _dir) = pes_db();
        let mut tx = db.begin_transaction();
        tx.set_savepoint();
        tx.put(b"b", b"rolled-back").unwrap();
        tx.rollback_to_savepoint().unwrap();
        // `b` was written blind and the write was rolled back, so it
        // was never read and is not validated. The lock stays held.
        db.db().put(b"b", b"external").unwrap();
        tx.put(b"a", b"1").unwrap();
        tx.commit().unwrap();
        assert_eq!(db.db().get(b"a").unwrap(), Some(b"1".to_vec()));
        assert_eq!(db.db().get(b"b").unwrap(), Some(b"external".to_vec()));
    }

    #[test]
    fn pessimistic_savepoint_rollback_keeps_the_read_anchor() {
        // Rolling back to a savepoint used to restore the conflict map
        // and let the next write re-anchor at a newer horizon, which
        // laundered a write that had bypassed the lock manager.
        let (db, _dir) = pes_db();
        db.db().put(b"k", b"v0").unwrap();
        let mut tx = db.begin_transaction();
        assert_eq!(tx.get_for_update(b"k").unwrap(), Some(b"v0".to_vec()));
        tx.set_savepoint();
        tx.put(b"k", b"rolled-back").unwrap();
        tx.rollback_to_savepoint().unwrap();
        db.db().put(b"k", b"racer").unwrap();
        tx.put(b"k", b"mine").unwrap();
        let err = tx.commit().expect_err("the bypassing write must be caught");
        assert!(matches!(err, TransactionError::Conflict { .. }), "{err:?}");
        assert_eq!(db.db().get(b"k").unwrap(), Some(b"racer".to_vec()));
    }

    #[test]
    fn pessimistic_reads_do_not_travel_backwards_after_a_savepoint_rollback() {
        let (db, _dir) = pes_db();
        db.db().put(b"k", b"v0").unwrap();
        let mut tx = db.begin_transaction();
        db.db().put(b"k", b"v1").unwrap();
        let first = tx.get_for_update(b"k").unwrap();
        assert_eq!(first, Some(b"v1".to_vec()));
        tx.set_savepoint();
        tx.put(b"k", b"staged").unwrap();
        tx.rollback_to_savepoint().unwrap();
        // The lock is still held and the read anchor with it, so the
        // second read cannot return an older value than the first.
        assert_eq!(tx.get(b"k").unwrap(), first);
    }

    #[test]
    fn pessimistic_read_then_write_detects_a_concurrent_write() {
        // A read-modify-write through plain `get` takes no lock, so the
        // commit check is the only thing standing between it and a lost
        // update.
        let (db, _dir) = pes_db();
        db.db().put(b"k", b"v0").unwrap();
        let tx = db.begin_transaction();
        assert_eq!(tx.get(b"k").unwrap(), Some(b"v0".to_vec()));
        db.db().put(b"k", b"v1").unwrap();
        tx.put(b"k", b"derived-from-v0").unwrap();
        let err = tx.commit().expect_err("the stale read must be caught");
        assert!(matches!(err, TransactionError::Conflict { .. }), "{err:?}");
        assert_eq!(db.db().get(b"k").unwrap(), Some(b"v1".to_vec()));
    }

    #[test]
    fn pessimistic_read_without_a_write_is_not_validated() {
        let (db, _dir) = pes_db();
        db.db().put(b"read-only", b"v0").unwrap();
        let tx = db.begin_transaction();
        assert_eq!(tx.get(b"read-only").unwrap(), Some(b"v0".to_vec()));
        db.db().put(b"read-only", b"v1").unwrap();
        tx.put(b"other", b"1").unwrap();
        tx.commit().unwrap();
        assert_eq!(db.db().get(b"other").unwrap(), Some(b"1".to_vec()));
    }

    #[test]
    fn pessimistic_range_delete_over_a_tracked_key_is_a_conflict() {
        let (db, _dir) = pes_db();
        db.db().put(b"k", b"v0").unwrap();
        let tx = db.begin_transaction();
        assert_eq!(tx.get_for_update(b"k").unwrap(), Some(b"v0".to_vec()));
        db.db().delete_range(b"a", b"z").unwrap();
        tx.put(b"k", b"resurrected").unwrap();
        let err = tx
            .commit()
            .expect_err("a range delete over a tracked key is a conflict");
        assert!(matches!(err, TransactionError::Conflict { .. }), "{err:?}");
        assert_eq!(db.db().get(b"k").unwrap(), None);
    }

    #[test]
    fn optimistic_range_delete_over_a_tracked_key_is_a_conflict() {
        let (db, _dir) = opt_db();
        db.db().put(b"k", b"v0").unwrap();
        let tx = db.begin_transaction();
        assert_eq!(tx.get_for_update(b"k").unwrap(), Some(b"v0".to_vec()));
        db.db().delete_range(b"a", b"z").unwrap();
        tx.put(b"k", b"resurrected").unwrap();
        let err = tx
            .commit()
            .expect_err("a range delete over a tracked key is a conflict");
        assert!(matches!(err, TransactionError::Conflict { .. }), "{err:?}");
        assert_eq!(db.db().get(b"k").unwrap(), None);
    }

    // ── Shared behavior ─────────────────────────────────────────────────

    #[test]
    fn commit_is_atomic_with_respect_to_other_writers() {
        let (db, _dir) = opt_db();
        let tx = db.begin_transaction();
        tx.put(b"a", b"1").unwrap();
        tx.put(b"b", b"2").unwrap();
        tx.put(b"c", b"3").unwrap();
        tx.commit().unwrap();
        assert_eq!(db.db().get(b"a").unwrap(), Some(b"1".to_vec()));
        assert_eq!(db.db().get(b"b").unwrap(), Some(b"2".to_vec()));
        assert_eq!(db.db().get(b"c").unwrap(), Some(b"3".to_vec()));
    }

    #[test]
    fn multi_get_within_transaction() {
        let (db, _dir) = opt_db();
        db.db().put(b"a", b"1").unwrap();
        db.db().put(b"b", b"2").unwrap();
        let tx = db.begin_transaction();
        tx.put(b"a", b"staged").unwrap();
        assert_eq!(tx.get(b"a").unwrap(), Some(b"staged".to_vec()));
        assert_eq!(tx.get(b"b").unwrap(), Some(b"2".to_vec()));
        assert_eq!(tx.get(b"missing").unwrap(), None);
    }

    // -- Write-stall admission --------------------------------------------

    fn slowdown_opts(stats: &Arc<Statistics>) -> Options {
        Options {
            // Tiny memtable so every handful of puts rolls an L0 file.
            write_buffer_size: 4 * 1024,
            // Disable automatic compaction so L0 can't drain on us.
            l0_compaction_trigger: 1000,
            // Slow down once L0 has 2 files, never stop (high trigger).
            level0_slowdown_writes_trigger: 2,
            level0_stop_writes_trigger: 10_000,
            // Disable the memtable-count trigger so this isolates the L0
            // slowdown path.
            max_write_buffer_number: 0,
            statistics: Some(Arc::clone(stats)),
            ..Options::default()
        }
    }

    /// Drive `plain` past the slowdown trigger with the same recipe as
    /// `test_write_stall_slowdown_accumulates_micros`, then check that a
    /// commit through `begin` is charged the wait only when it carries a
    /// write.
    fn probe_slowdown_ticker<'a>(
        plain: &Db,
        stats: &Statistics,
        begin: impl Fn() -> Transaction<'a>,
    ) {
        let payload = vec![0xCDu8; 600];
        for i in 0..128 {
            let k = format!("k{i:04}");
            plain.put(k.as_bytes(), &payload).unwrap();
        }
        let stall = stats.get_ticker(Ticker::WriteStallMicros);
        assert!(
            stall > 0,
            "expected WriteStallMicros > 0 after crossing the slowdown trigger, got {stall}"
        );

        let before = stats.get_ticker(Ticker::WriteStallMicros);
        let tx = begin();
        tx.get(b"k0000").unwrap();
        tx.commit().unwrap();
        assert_eq!(
            stats.get_ticker(Ticker::WriteStallMicros),
            before,
            "a read-only commit must not be charged for the write-stall wait"
        );

        let tx = begin();
        tx.put(b"txn", b"v").unwrap();
        tx.commit().unwrap();
        assert!(
            stats.get_ticker(Ticker::WriteStallMicros) > before,
            "a writing commit under a slowdown must be charged for the wait"
        );
        assert_eq!(plain.get(b"txn").unwrap(), Some(b"v".to_vec()));
    }

    #[test]
    fn optimistic_commit_is_charged_the_slowdown_like_a_plain_write() {
        let stats = Arc::new(Statistics::new());
        let dir = TempDir::new().unwrap();
        let db = OptimisticTransactionDb::open(dir.path(), slowdown_opts(&stats)).unwrap();
        probe_slowdown_ticker(db.db(), &stats, || db.begin_transaction());
    }

    #[test]
    fn pessimistic_commit_is_charged_the_slowdown_like_a_plain_write() {
        let stats = Arc::new(Statistics::new());
        let dir = TempDir::new().unwrap();
        let db = TransactionDb::open(dir.path(), slowdown_opts(&stats)).unwrap();
        probe_slowdown_ticker(db.db(), &stats, || db.begin_transaction());
    }

    #[test]
    fn commit_on_a_closed_handle_reports_closed_before_it_waits() {
        let dir = TempDir::new().unwrap();
        let db = OptimisticTransactionDb::open(dir.path(), Options::default()).unwrap();
        let tx = db.begin_transaction();
        tx.put(b"k", b"v").unwrap();
        db.db().close().unwrap();
        match tx.commit() {
            Err(TransactionError::Io(e)) => {
                assert_eq!(e.kind(), std::io::ErrorKind::NotConnected);
                assert_eq!(e.to_string(), "database is closed");
            }
            other => panic!("expected a closed-handle Io error, got {other:?}"),
        }
    }

    /// The closed-handle test above cannot tell whether `commit_optimistic`'s
    /// `ensure_writable` call runs before the stall wait, because a closed
    /// handle produces the identical error either way (`wait_for_write_capacity`
    /// also refuses a closed engine). A latched write-ahead-log failure
    /// under `StallPolicy::WaitForWorker` is the one case that can: without
    /// the pre-wait check, the commit would sleep out the slowdown delay
    /// first and only then report the WAL error, charging the wait to
    /// `WriteStallMicros` on the way. Regression for deleting that call.
    #[test]
    fn commit_on_a_wal_failed_handle_is_refused_before_the_stall_wait() {
        let stats = Arc::new(Statistics::new());
        let dir = TempDir::new().unwrap();
        let db = OptimisticTransactionDb::open(dir.path(), slowdown_opts(&stats)).unwrap();

        let payload = vec![0xCDu8; 600];
        for i in 0..128 {
            let k = format!("k{i:04}");
            db.db().put(k.as_bytes(), &payload).unwrap();
        }
        let stall = stats.get_ticker(Ticker::WriteStallMicros);
        assert!(
            stall > 0,
            "expected WriteStallMicros > 0 after crossing the slowdown trigger, got {stall}"
        );

        db.db()
            .engine
            .latch_wal_failure(&std::io::Error::other("injected"));
        let before = stats.get_ticker(Ticker::WriteStallMicros);

        let tx = db.begin_transaction();
        tx.put(b"txn", b"v").unwrap();
        match tx.commit() {
            Err(TransactionError::Io(e)) => {
                assert!(
                    e.to_string()
                        .contains("write-ahead log left in an unknown state"),
                    "expected the WAL failure reason, got: {e}"
                );
            }
            other => panic!("expected a WAL-failure Io error, got {other:?}"),
        }
        assert_eq!(
            stats.get_ticker(Ticker::WriteStallMicros),
            before,
            "a commit refused for a WAL failure must not pay the stall wait"
        );
    }

    // A scan's read set grows by yielded key, not by call: a key it
    // already tracked folds into the same cell, a buffered key it
    // yields is never tracked, and a bound key the walk stops on is
    // never handed out so it never reaches `tracked` either.
    #[test]
    fn a_scan_records_exactly_the_snapshot_keys_it_yields() {
        let (db, _dir) = opt_db();
        db.db().put(b"a", b"0").unwrap();
        db.db().put(b"b", b"0").unwrap();
        db.db().put(b"c", b"0").unwrap();
        let tx = db.begin_transaction_with(IsolationLevel::Serializable);

        assert_eq!(tx.scan_stream(Some(b"x"), Some(b"y")).count(), 0);
        assert_eq!(tx.tracked.len(), 0, "an empty scan tracks nothing");

        assert_eq!(tx.scan_stream(Some(b"a"), Some(b"b")).count(), 1);
        assert_eq!(tx.tracked.len(), 1, "the bound key b is not recorded");

        tx.put(b"c", b"pending").unwrap();
        assert_eq!(tx.scan_stream(None, None).count(), 3);
        assert_eq!(
            tx.tracked.len(),
            2,
            "a folds into its existing cell, b is newly tracked, c came from \
             the write buffer and is not tracked"
        );

        let fresh = db.begin_transaction_with(IsolationLevel::Serializable);
        assert_eq!(fresh.scan_stream(None, None).take(0).count(), 0);
        assert_eq!(
            fresh.tracked.len(),
            0,
            "a stream that yields nothing records nothing"
        );
        assert!(fresh.scan_runs.get().is_none());
    }

    /// Regression: `scan_stream_in` used to index `tracked` only at the
    /// moment the stream was built, so a `get_for_update` promotion that
    /// landed after a stream was already open left every later yielded key
    /// walking the unindexed list instead of hitting the hash index.
    /// `scan_read_seq` now builds the index itself, lazily, the first time
    /// it finds a promotion, so the order `get_for_update` and
    /// `scan_stream` run in cannot matter.
    #[test]
    fn a_promotion_mid_scan_indexes_tracked_lazily_not_only_at_construction() {
        let dir = TempDir::new().unwrap();
        // `0` never indexes from ordinary inserts (`TxnBuffer::new`), so the
        // only thing that can index `tracked` in this test is the lazy
        // build `scan_read_seq` triggers, isolated from the unrelated
        // "past N keys" auto-index a bigger default would also trigger.
        let opts = Options {
            transaction_keys_inline: 0,
            ..Options::default()
        };
        let db = TransactionDb::open(dir.path(), opts).unwrap();
        for i in 0..64u32 {
            db.db().put(format!("k{i:04}").as_bytes(), b"0").unwrap();
        }
        let tx = db.begin_transaction();

        let mut stream = tx.scan_stream(None, None);
        assert_eq!(stream.next().unwrap().0, b"k0000".to_vec());
        assert!(
            !tx.tracked.is_indexed(),
            "nothing is promoted yet: scan_stream_in must not index speculatively"
        );

        // Lands after the begin snapshot; the promotion below must read
        // this, not the snapshot value, proving it is served at the lock
        // horizon like `get` and not accidentally read from the cursor.
        db.db().put(b"k0010", b"promoted").unwrap();
        assert_eq!(
            tx.get_for_update(b"k0010").unwrap(),
            Some(b"promoted".to_vec()),
            "get_for_update while the stream is open reads past the begin snapshot"
        );
        assert!(
            !tx.tracked.is_indexed(),
            "a promotion by itself must not index; the next scan lookup does"
        );

        // Draining the rest is exactly where the bug bit: every one of
        // these calls used to fall back to `TxnBuffer::walk`, O(1) here but
        // O(tracked keys) had more been promoted, because construction-time
        // indexing had already run and missed this promotion.
        let rest: Vec<(Vec<u8>, Vec<u8>)> = stream.map(|(k, v)| (k, v.to_vec())).collect();
        assert!(
            tx.tracked.is_indexed(),
            "scan_read_seq must index tracked lazily on first need, mid-stream, \
             not only when scan_stream_in constructed the stream"
        );
        assert_eq!(rest.len(), 63, "every remaining key is still yielded");
        let promoted = rest
            .iter()
            .find(|(k, _)| k == b"k0010")
            .expect("the promoted key is still yielded");
        assert_eq!(
            promoted.1,
            b"promoted".to_vec(),
            "yielded at the promoted read sequence, not the stale begin snapshot"
        );
    }
}
