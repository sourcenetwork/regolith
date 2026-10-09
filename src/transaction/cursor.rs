//! A transaction's view of a key range, walked a page at a time.
//!
//! [`TxnCursor`] merges the transaction's own buffered writes over a cursor on
//! the begin snapshot, so a scan sees what the transaction wrote without either
//! side being materialized: the database side is a cursor, and the buffered
//! side is bounded by what this transaction wrote. It borrows nothing from the
//! transaction, so a scan survives across task suspensions and a worker can
//! hold many; the transaction is passed to each call.
//!
//! What the scan leaves in the transaction is chosen by its [`ScanCheck`]. A
//! stretch of snapshot keys it yields is recorded once, as its first and last
//! key, and extended in place page by page (see `scan_range`); a validated
//! range is one record moved forward (see `validated_range`). Either way what
//! the transaction holds grows with the number of scans, not with the size of
//! a range.
//!
//! [`TxnScanStream`] is the iterator form of the same walk, one entry at a
//! time.

use std::iter::Peekable;
use std::ops::ControlFlow;
use std::sync::Arc;

use crate::column_family::{DEFAULT_CF_ID, cf_lower_bound, cf_upper_bound, prefix_key};
use crate::engine::range_tombstone::exclusive_successor;
use crate::{CfIter, DbSlice, Error, Iter};

use super::scan_range::OpenRun;
use super::validated_range::RangeRecord;
use super::write_buffer::{KeyWrites, Write, fold_by_key};
use super::{ScanDirection, Transaction, TransactionError, TxResult, read_error};

/// Length of the column-family prefix on the keys a transaction buffers.
const CF_PREFIX_LEN: usize = 4;

/// What a scan leaves behind for the commit to validate.
///
/// Every check works at every isolation level. A classifier never exempts a
/// [`ScanCheck::Range`].
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ScanCheck {
    /// Today's scan: each unbroken stretch of snapshot keys it yields is
    /// recorded, and a key the transaction later writes inside a stretch is
    /// validated as a read from the begin snapshot, so it is never taken for
    /// a blind write. The keys it yielded and the range itself are not
    /// validated (phantoms are possible).
    Stretch,
    /// A [`ScanCheck::Stretch`] whose reads used only these parts of the
    /// values (sorted part ids that [`crate::MergeOperator::touches`]
    /// understands). A key the transaction later merges into inside a
    /// stretch is validated over the parts, as [`Transaction::get_parts`]
    /// would; a key it puts or deletes there is validated in whole, since
    /// the write replaces every part. With no parts the scan is never
    /// validated at all. Where the level or the transaction cannot project
    /// (anything but an optimistic transaction at
    /// [`crate::IsolationLevel::DefraLevel`]), it behaves as
    /// [`ScanCheck::Stretch`].
    ///
    /// The caller must name every part its decision used.
    Parts(Box<[u32]>),
    /// A scan whose result may decide: at commit, any put, delete, merge or
    /// range delete newer than the snapshot inside the range it covered
    /// conflicts, so a key that left the range and a key that appeared in it
    /// (a phantom) both do. The range runs from the scan's start to the last
    /// key the caller consumed, or to the range end once the scan is
    /// exhausted, so stopping early validates only what was read. The
    /// conflict names [`crate::Access::ScannedRange`].
    ///
    /// A write-free optimistic transaction at DefraLevel validates nothing,
    /// this included: its snapshot is consistent on its own.
    ///
    /// The check reads every block of the range at commit, while the commit
    /// holds the write pipeline, so a range that is large against the writes
    /// since the snapshot makes every writer wait for it.
    Range,
}

/// One page of a scan.
#[derive(Debug)]
#[non_exhaustive]
pub struct Page {
    /// The entries in scan order, keys without the column-family prefix. The
    /// values are views of the bytes the database already holds.
    pub entries: Vec<(Vec<u8>, DbSlice)>,
    /// The scan reached the end of its range during this call. The page that
    /// reports it may hold the last entries, or none at all; no later call
    /// returns an entry.
    pub done: bool,
}

/// How the cursor records the stretches it yields.
enum Recording {
    /// No stretch: a validated range, or a scan by no parts.
    Nothing,
    Stretch,
    Parts(Arc<[u32]>),
}

/// A failed read, kept so every later call reports it again: a scan that
/// failed must not look like one that ended.
struct Failure {
    io: std::io::Error,
    /// The prefixed key whose read or merge failed, when there was one.
    key: Option<Vec<u8>>,
}

impl Failure {
    fn error(&self) -> TransactionError {
        let io = Error::clone_io(&self.io);
        match &self.key {
            Some(key) => read_error(io, key),
            None => TransactionError::Engine(io.into()),
        }
    }
}

/// One entry of a scan: its key without the column-family prefix, and its value.
type Entry = (Vec<u8>, DbSlice);

/// The transaction's own writes for a range, folded per key, sorted and ready
/// to merge.
type BufferedWrites = Peekable<std::vec::IntoIter<(Vec<u8>, KeyWrites)>>;

/// A scan of a key range as one transaction sees it, resumable a page at a
/// time. Made by [`Transaction::cursor`].
///
/// The cursor holds no borrow of its transaction: pass the same transaction
/// to every [`TxnCursor::next_page`]. A cursor moved to another transaction's
/// calls reads the wrong snapshot and records its stretches in the wrong
/// place, which regolith rejects only when the two differ in database or
/// begin snapshot.
///
/// It merges the transaction's buffered writes over the begin snapshot and
/// folds them again only when the transaction has written since the last
/// call, so a write ahead of the cursor's position is seen by the pages
/// after it and one behind it is not. A key a pessimistic transaction
/// already locked through [`Transaction::get_for_update`] is served where
/// `get` serves it.
///
/// An error is final: once a call returns one, every later call returns it
/// again and the scan never reports the end of its range.
pub struct TxnCursor {
    cursor: CfIter<'static>,
    cursor_done: bool,
    buffered: BufferedWrites,
    /// The write buffer's generation when `buffered` was folded.
    folded_at: u64,
    /// Inclusive lower bound, CF-prefixed.
    lo: Option<Vec<u8>>,
    /// Exclusive upper bound, CF-prefixed.
    hi: Option<Vec<u8>>,
    reverse: bool,
    /// The last key handed out, CF-prefixed. What the next fold starts after.
    position: Option<Vec<u8>>,
    recording: Recording,
    /// The stretch of snapshot keys being yielded. Dropping it closes it.
    run: Option<OpenRun>,
    /// The range a [`ScanCheck::Range`] covers.
    range: Option<Arc<RangeRecord>>,
    /// The key being handed out, CF-prefixed, reused across yields.
    probe: Vec<u8>,
    failure: Option<Failure>,
    exhausted: bool,
    /// The database and begin snapshot of the transaction that made it.
    owner: (usize, u64),
}

impl std::fmt::Debug for TxnCursor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TxnCursor")
            .field("reverse", &self.reverse)
            .field("exhausted", &self.exhausted)
            .finish_non_exhaustive()
    }
}

impl Transaction {
    /// Walk `[start, end)` in `direction`, a page at a time, merging this
    /// transaction's buffered writes over its begin snapshot. `check` decides
    /// what the commit validates of the walk (see [`ScanCheck`]).
    ///
    /// Nothing is read until the first [`TxnCursor::next_page`]. The range
    /// is the same either way: `start` inclusive and `end` exclusive; only
    /// the order changes. Reverse starts at the highest key below `end` and
    /// walks down to `start` inclusive, both sides of the merge reversed
    /// together.
    pub fn cursor(
        &self,
        start: Option<&[u8]>,
        end: Option<&[u8]>,
        direction: ScanDirection,
        check: ScanCheck,
    ) -> TxnCursor {
        TxnCursor::new(self, start, end, direction, check)
    }

    /// The write buffer's generation: changes whenever a write lands or the
    /// buffer is cut back (by a savepoint rollback or a failed callback), and
    /// never returns to an earlier value.
    pub(super) fn write_mark(&self) -> u64 {
        self.writes.generation()
    }
}

impl TxnCursor {
    fn new(
        txn: &Transaction,
        start: Option<&[u8]>,
        end: Option<&[u8]>,
        direction: ScanDirection,
        check: ScanCheck,
    ) -> Self {
        let lo = start.map(|s| prefix_key(DEFAULT_CF_ID, s));
        let hi = end.map(|e| prefix_key(DEFAULT_CF_ID, e));
        let reverse = direction == ScanDirection::Reverse;

        let mut cursor: CfIter<'static> = CfIter::new(
            Iter::from_internal(txn.engine.new_iter_at(txn.snapshot_seq)),
            DEFAULT_CF_ID,
        );
        if reverse {
            match &hi {
                // `end` is exclusive, so a backward walk starts below it.
                Some(hi) => {
                    let end = &hi[CF_PREFIX_LEN..];
                    cursor.seek_for_prev(end);
                    if cursor.valid() && cursor.key() == Some(end) {
                        cursor.prev();
                    }
                }
                None => cursor.seek_to_last(),
            }
        } else {
            // The bound must reach the cursor, not only `peek_cursor`: the
            // cursor skips entries this snapshot cannot see before it
            // reports a key, and without it that skip runs past `end`.
            let target = lo.as_deref().map_or(&[][..], |lo| &lo[CF_PREFIX_LEN..]);
            cursor.seek_bounded(target, hi.as_deref().map(|hi| &hi[CF_PREFIX_LEN..]));
        }

        let projects = txn.projects();
        let (recording, range) = match check {
            ScanCheck::Stretch => (Recording::Stretch, None),
            ScanCheck::Parts(parts) if !projects => {
                let _ = parts;
                (Recording::Stretch, None)
            }
            ScanCheck::Parts(parts) => {
                let mut parts = parts.into_vec();
                parts.sort_unstable();
                parts.dedup();
                if parts.is_empty() {
                    (Recording::Nothing, None)
                } else {
                    (Recording::Parts(parts.into()), None)
                }
            }
            ScanCheck::Range => {
                let floor = lo.clone().unwrap_or_else(|| cf_lower_bound(DEFAULT_CF_ID));
                let ceil = hi.clone().unwrap_or_else(|| cf_upper_bound(DEFAULT_CF_ID));
                // Nothing is consumed yet, so the record covers nothing.
                let record = if reverse {
                    RangeRecord::new(ceil.clone(), ceil)
                } else {
                    RangeRecord::new(floor.clone(), floor)
                };
                txn.record_scan_range(Arc::clone(&record));
                (Recording::Nothing, Some(record))
            }
        };

        let mut cursor = Self {
            cursor,
            cursor_done: false,
            buffered: Vec::new().into_iter().peekable(),
            folded_at: txn.write_mark(),
            lo,
            hi,
            reverse,
            position: None,
            recording,
            run: None,
            range,
            probe: Vec::new(),
            failure: None,
            exhausted: false,
            owner: owner_of(txn),
        };
        cursor.fold(txn);
        cursor
    }

    /// Read the next page: entries in scan order until their keys and values
    /// hold at least `max_bytes`, or the range ends. A page holds at least
    /// one entry unless the range ended first, so a `max_bytes` of zero reads
    /// one entry at a time, and it can overshoot `max_bytes` by one entry.
    ///
    /// `txn` must be the transaction that made the cursor. The page's entries
    /// are recorded with the transaction as the scan's check says, and a
    /// commit between two pages sees the scan as far as the last page took
    /// it.
    ///
    /// An error reaches the caller as `Err`, never as the end of the range:
    /// a read of the database failed, or the merge operator declined a key
    /// the transaction merged into. When it strikes after the page already
    /// holds entries, that page is returned and the next call reports the
    /// error.
    pub fn next_page(&mut self, txn: &Transaction, max_bytes: usize) -> TxResult<Page> {
        if owner_of(txn) != self.owner {
            return Err(TransactionError::Engine(Error::invalid_argument(
                "the cursor belongs to a different transaction",
            )));
        }
        let mut entries = Vec::new();
        let mut taken = 0usize;
        let mut done = false;
        let mut failed = None;
        while entries.is_empty() || taken < max_bytes {
            match self.step(txn) {
                Ok(Some((key, value))) => {
                    taken = taken.saturating_add(key.len()).saturating_add(value.len());
                    entries.push((key, value));
                }
                Ok(None) => {
                    done = true;
                    break;
                }
                Err(error) => {
                    failed = Some(error);
                    break;
                }
            }
        }
        self.publish();
        match failed {
            Some(error) if entries.is_empty() => Err(error),
            // The failure is stored; the next call reports it.
            _ => Ok(Page { entries, done }),
        }
    }

    /// Let a commit see how far the walk has gone.
    fn publish(&self) {
        if let Some(run) = &self.run {
            run.publish();
        }
        let Some(range) = &self.range else {
            return;
        };
        if self.reverse {
            let covered = if self.exhausted {
                self.lo
                    .clone()
                    .unwrap_or_else(|| cf_lower_bound(DEFAULT_CF_ID))
            } else if let Some(position) = &self.position {
                position.clone()
            } else {
                return;
            };
            range.set_lo(&covered);
        } else {
            let covered = if self.exhausted {
                self.hi
                    .clone()
                    .unwrap_or_else(|| cf_upper_bound(DEFAULT_CF_ID))
            } else if let Some(position) = &self.position {
                exclusive_successor(position)
            } else {
                return;
            };
            range.set_hi(&covered);
        }
    }

    /// Fold the transaction's buffered writes for the part of the range the
    /// walk has yet to reach.
    fn fold(&mut self, txn: &Transaction) {
        let (lo, hi, position, reverse) = (&self.lo, &self.hi, &self.position, self.reverse);
        // Read before the buffer is, so a write that lands during the fold
        // makes the next step fold again instead of being taken for folded.
        let generation = txn.write_mark();
        let chains = txn.writes.chains_matching(
            |key| {
                lo.as_ref().is_none_or(|lo| key >= lo)
                    && hi.as_ref().is_none_or(|hi| key < hi)
                    && position
                        .as_ref()
                        .is_none_or(|at| if reverse { key < at } else { key > at })
            },
            Write::is_terminator,
        );
        self.buffered = fold_by_key(chains, reverse, txn.engine.merge_operator())
            .into_iter()
            .peekable();
        self.folded_at = generation;
    }

    /// Record `failure` and return the error it reports.
    fn fail(&mut self, failure: Failure) -> TransactionError {
        let error = failure.error();
        self.failure = Some(failure);
        error
    }

    /// The next entry of the walk, or `None` at the end of the range.
    fn step(&mut self, txn: &Transaction) -> TxResult<Option<Entry>> {
        if let Some(failure) = &self.failure {
            return Err(failure.error());
        }
        // The end of the range is final: a write made after it was reached
        // does not bring the scan back.
        if self.exhausted {
            return Ok(None);
        }
        if txn.write_mark() != self.folded_at {
            self.fold(txn);
        }
        loop {
            let cursor_key = match self.peek_cursor() {
                Ok(key) => key,
                Err(failure) => return Err(self.fail(failure)),
            };
            // Buffered keys carry the CF prefix; the cursor reports the
            // user-visible key, so compare on the stripped form.
            let buffered_key = self
                .buffered
                .peek()
                .map(|(key, _)| key[CF_PREFIX_LEN..].to_vec());

            let flow = match (cursor_key, buffered_key) {
                (None, None) => {
                    self.run = None;
                    self.exhausted = true;
                    return Ok(None);
                }
                // Only the transaction has this key.
                (None, Some(_)) => self.yield_buffered(txn),
                // Only the database has it.
                (Some(key), None) => self.yield_cursor(txn, key),
                (Some(ckey), Some(bkey)) => match self.precedes(&ckey, &bkey) {
                    std::cmp::Ordering::Less => self.yield_cursor(txn, ckey),
                    std::cmp::Ordering::Greater => self.yield_buffered(txn),
                    // The transaction wrote a key the snapshot also has,
                    // so its write wins and the snapshot entry is skipped
                    // whether that write was a put or a delete. Operands
                    // with no put or delete beneath them read the entry
                    // themselves, as `get` would.
                    std::cmp::Ordering::Equal => {
                        self.step_cursor();
                        self.yield_buffered(txn)
                    }
                },
            };
            match flow {
                Err(failure) => return Err(self.fail(failure)),
                Ok(ControlFlow::Continue(())) => {}
                Ok(ControlFlow::Break(None)) => {
                    self.exhausted = true;
                    return Ok(None);
                }
                Ok(ControlFlow::Break(Some((key, value)))) => {
                    let position = self.position.get_or_insert_with(Vec::new);
                    position.clear();
                    position.extend_from_slice(&DEFAULT_CF_ID.to_be_bytes());
                    position.extend_from_slice(&key);
                    return Ok(Some((key, value)));
                }
            }
        }
    }

    /// The next snapshot entry inside the range, or `None` past the end.
    ///
    /// Whichever way the walk runs, it stops at the bound it is running
    /// towards: `end` is exclusive going forward, `start` inclusive going
    /// back. A cursor that went invalid because its walk failed, and not
    /// because the range ended, is a failure.
    fn peek_cursor(&mut self) -> Result<Option<Vec<u8>>, Failure> {
        if self.cursor_done || !self.cursor.valid() {
            // The cursor going invalid means one of two things and this is
            // where they become distinguishable: the range ended, or the
            // walk failed.
            return match self.cursor.status() {
                Ok(()) => Ok(None),
                Err(error) => Err(Failure {
                    io: error.into_io_error(),
                    key: None,
                }),
            };
        }
        let Some(key) = self.cursor.key().map(<[u8]>::to_vec) else {
            return Ok(None);
        };
        let past_bound = if self.reverse {
            self.lo
                .as_ref()
                .is_some_and(|lo| key.as_slice() < &lo[CF_PREFIX_LEN..])
        } else {
            self.hi
                .as_ref()
                .is_some_and(|hi| key.as_slice() >= &hi[CF_PREFIX_LEN..])
        };
        if past_bound {
            self.cursor_done = true;
            return Ok(None);
        }
        Ok(Some(key))
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
    /// `Break(Some(entry))` hands `entry` out, `Break(None)` ends the walk,
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
    fn yield_cursor(
        &mut self,
        txn: &Transaction,
        key: Vec<u8>,
    ) -> Result<ControlFlow<Option<Entry>>, Failure> {
        self.probe.clear();
        self.probe.extend_from_slice(&DEFAULT_CF_ID.to_be_bytes());
        self.probe.extend_from_slice(&key);
        let read_seq = txn.scan_read_seq(&self.probe);
        if read_seq > txn.snapshot_seq {
            self.step_cursor();
            self.run = None;
            return match txn.engine.get_slice_at(&self.probe, read_seq) {
                Ok(Some(value)) => Ok(ControlFlow::Break(Some((key, value)))),
                Ok(None) => Ok(ControlFlow::Continue(())),
                Err(io) => Err(Failure {
                    io,
                    key: Some(self.probe.clone()),
                }),
            };
        }
        let Some(value) = self.cursor.value_slice() else {
            self.run = None;
            return Ok(ControlFlow::Break(None));
        };
        self.step_cursor();
        Self::join_stretch(
            txn,
            &mut self.run,
            &self.recording,
            self.reverse,
            &self.probe,
        );
        Ok(ControlFlow::Break(Some((key, value))))
    }

    /// Take `key` (CF-prefixed), a snapshot key the walk read at the begin
    /// snapshot, into the stretch in `run`, starting and registering one if
    /// none is open. At Serializable the key is also recorded per key through
    /// `observe`.
    fn join_stretch(
        txn: &Transaction,
        run: &mut Option<OpenRun>,
        recording: &Recording,
        reverse: bool,
        key: &[u8],
    ) {
        let parts = match recording {
            Recording::Nothing => None,
            Recording::Stretch => Some(None),
            Recording::Parts(parts) => Some(Some(Arc::clone(parts))),
        };
        if let Some(parts) = parts {
            match run {
                Some(open) => open.extend(key),
                None => {
                    let (record, open) = OpenRun::start(key, reverse, parts);
                    txn.record_scan_run(record);
                    *run = Some(open);
                }
            }
        }
        if txn.isolation.validates_scanned_keys() {
            txn.observe(key, txn.snapshot_seq, false);
        }
    }

    /// Hand out the transaction's own entry at the head of `buffered`.
    ///
    /// The same protocol as `yield_cursor`. A key the transaction merged into
    /// and did not replace has its operands lie on a snapshot key, which the
    /// walk reads as it reads any other: at the key's read sequence, joining
    /// the stretch when that is the begin snapshot and ending it when a
    /// promotion moved it past that, and recording a read of it only at
    /// Serializable. Every other entry comes from the write buffer and ends
    /// the stretch. A merge the operator declines is a failure.
    fn yield_buffered(&mut self, txn: &Transaction) -> Result<ControlFlow<Option<Entry>>, Failure> {
        let Some((prefixed, writes)) = self.buffered.next() else {
            return Ok(ControlFlow::Break(None));
        };
        // Only an entry that reads its base uses the sequence: `apply` takes
        // the closure below for nothing else.
        let read_seq = if writes.reads_base() {
            let read_seq = txn.scan_read_seq(&prefixed);
            if read_seq > txn.snapshot_seq {
                self.run = None;
            } else {
                Self::join_stretch(txn, &mut self.run, &self.recording, self.reverse, &prefixed);
            }
            read_seq
        } else {
            self.run = None;
            txn.snapshot_seq
        };
        let found = writes.apply(txn.engine.merge_operator(), &prefixed, || {
            txn.engine.get_slice_at(&prefixed, read_seq)
        });
        match found {
            Ok(Some(Some(value))) => Ok(ControlFlow::Break(Some((
                prefixed[CF_PREFIX_LEN..].to_vec(),
                DbSlice::from(value),
            )))),
            Ok(_) => Ok(ControlFlow::Continue(())),
            Err(io) => Err(Failure {
                io,
                key: Some(prefixed),
            }),
        }
    }
}

/// Who a cursor belongs to: the database and begin snapshot of its
/// transaction.
fn owner_of(txn: &Transaction) -> (usize, u64) {
    (Arc::as_ptr(&txn.engine) as usize, txn.snapshot_seq)
}

/// A transaction's view of a key range, streamed one entry at a time.
///
/// [`TxnCursor`] without the pages: the iterator pulls one entry per call, so
/// a caller that stops early pays only for what it read. Each item is a
/// `Result`, so an error in the middle of the range reaches the caller as an
/// `Err` and is never mistaken for the end of the range; after it the stream
/// ends. Made by [`Transaction::scan_stream`] and
/// [`Transaction::scan_stream_in`], which document what the scan records.
///
/// Each unbroken stretch of snapshot entries it yields is recorded in the
/// transaction once, as the first and the last key of the stretch (per key as
/// well at Serializable); entries that come from the transaction's own writes
/// are not recorded and end the stretch, except a merged key whose operands
/// lie on a snapshot entry, which joins it. The stretch is closed when the
/// stream is exhausted or dropped.
pub struct TxnScanStream<'txn> {
    txn: &'txn Transaction,
    cursor: TxnCursor,
    ended: bool,
}

impl<'txn> TxnScanStream<'txn> {
    pub(super) fn new(
        txn: &'txn Transaction,
        start: Option<&[u8]>,
        end: Option<&[u8]>,
        direction: ScanDirection,
    ) -> Self {
        Self {
            txn,
            cursor: txn.cursor(start, end, direction, ScanCheck::Stretch),
            ended: false,
        }
    }
}

impl Iterator for TxnScanStream<'_> {
    type Item = TxResult<(Vec<u8>, DbSlice)>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.ended {
            return None;
        }
        match self.cursor.step(self.txn) {
            Ok(Some(entry)) => Some(Ok(entry)),
            Ok(None) => {
                self.ended = true;
                None
            }
            Err(error) => {
                self.ended = true;
                Some(Err(error))
            }
        }
    }
}

impl std::fmt::Debug for TxnScanStream<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TxnScanStream").finish_non_exhaustive()
    }
}
