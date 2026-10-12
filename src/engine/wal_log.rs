//! The write-ahead log the commit pipeline writes: format 2, one record per
//! commit, each written at an offset fixed before any byte of it exists.
//!
//! [`super::wal::Wal`] appends: one caller at a time, each record after the
//! one before. A [`Log`] is written by position instead, so that whichever
//! thread reaches a decided commit first can write its record
//! (`engine::commit`, plan 4.7). The bytes on disk are the same format 2
//! records, sealed the same way, and replay reads them as it reads any log.
//!
//! # What makes a record's bytes the same for every writer
//!
//! A record's frame depends on its offset, on `synced_through` and, in a
//! sealed log, on the AEAD nonce. All three are fixed once, when the commit
//! is decided, in a [`Place`]; given the same `Place` and the same
//! operations, [`Log::finish_record`] produces the same bytes on every
//! thread. Two threads writing one record therefore write identical bytes to
//! the same range, which is harmless.
//!
//! # Invariants
//!
//! - **`durable` only grows, and only by a completed sync.** It is the
//!   offset the last completed [`Log::sync_through`] covered. A record is
//!   stamped with the value read when it was decided, which is at most the
//!   value when it is written: a record never claims bytes a sync did not
//!   cover (`proofs/tla/WalRecovery.tla`, `AppendRecord` and `Sync`).
//! - **One sync at a time.** The pipeline claims the sync before it calls
//!   [`Log::sync_through`]. A sync error is reported to one caller of one
//!   file handle and then cleared by the host, so two syncs overlapping on
//!   the handle could tell a later caller the bytes of a failed one were
//!   safe.
//! - **A rolled back range is not written by a stale writer.** Every write
//!   passes the gate: it counts itself in, compares the epoch its `Place`
//!   was decided in with the log's, and counts itself out. A rollback moves
//!   the epoch on and waits for the count to reach zero before it cuts the
//!   file, so a write of a discarded commit either finished before the cut,
//!   which removes it, or never starts.
//! - **Nothing follows CLOSE.** [`Log::close`] is called with the pipeline
//!   drained, and no commit is decided after it.

use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::seal::{Keyring, NONCE_LEN, OVERHEAD, Sealer};
use super::take::Take;
use super::wal_frame::{self, HEADER_LEN};
use super::wal_seal::{self, SEALED_PREFIX_LEN};
use crate::env::{Env, LogFile, WriteMode};
use crate::portability::{AtomicBool, AtomicU64, AtomicUsize, Ordering};

/// Where one commit's record goes and what frames it: everything about the
/// record that is not its operations, fixed when the commit is decided.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Place {
    /// Offset of the record's first byte.
    pub(crate) offset: u64,
    /// Bytes the record occupies, frame included.
    pub(crate) len: u64,
    /// The durable offset stamped into the record.
    pub(crate) synced_through: u64,
    /// The AEAD nonce of a sealed record; zeros in a log that is not sealed.
    pub(crate) nonce: [u8; NONCE_LEN],
    /// The log's write epoch when the commit was decided.
    pub(crate) epoch: u64,
}

impl Place {
    /// Offset one past the record's last byte.
    pub(crate) fn end(&self) -> u64 {
        self.offset + self.len
    }
}

/// A format 2 log written by position. See the module docs.
pub(crate) struct Log {
    file: Box<dyn LogFile>,
    path: PathBuf,
    env: Arc<dyn Env>,
    /// Drawn when the log is created and written into its stamp. Every
    /// record's header check covers it.
    nonce: u64,
    /// Set when the log is sealed: every record's payload is sealed under
    /// this key, the one its stamp names.
    seal: Option<Sealer>,
    /// Bytes of the stamp, which no record and no rollback reaches into.
    stamp_len: u64,
    /// Every byte below this offset is durable.
    durable: AtomicU64,
    /// The directory entry naming the file is durable.
    parent_synced: AtomicBool,
    /// Moved on by every rollback: a write decided in an older epoch is of a
    /// discarded commit and is not made.
    epoch: AtomicU64,
    /// Writes between the gate's count in and its count out.
    writers: AtomicUsize,
    /// A write or a sync of this log failed and the rollback that discards
    /// what it left has not run yet: no sync may vouch for the log meanwhile.
    poisoned: AtomicBool,
    /// What poisoned the log, for the rollback to hand to every commit it
    /// fails.
    failure: Take<io::Error>,
}

impl Log {
    /// Create the log at `path`, sealed under the current key of `keyring`
    /// when one is given.
    ///
    /// A sealed log's stamp is durable before this returns, and the log
    /// appears under its name only then (`super::wal_seal`).
    pub(crate) fn create_in(
        env: &Arc<dyn Env>,
        path: &Path,
        keyring: Option<&Keyring>,
    ) -> io::Result<Self> {
        let nonce = super::wal::fresh_nonce(env.as_ref(), path);
        let named = |e: io::Error| {
            if crate::Error::is_typed(&e) {
                return e;
            }
            io::Error::new(e.kind(), format!("creating wal {}: {e}", path.display()))
        };
        let (file, seal, stamp_len, synced) = match keyring {
            Some(keyring) => {
                let sealer = keyring.current().map_err(named)?;
                let stamp = wal_seal::encode_stamp(nonce, &sealer)?;
                wal_seal::stage_durably(env, path, &stamp).map_err(named)?;
                let file = env.open_log(path, WriteMode::Update).map_err(named)?;
                (file, Some(sealer), stamp.len() as u64, true)
            }
            None => {
                // Named on failure: creating a log at a path a previous log
                // was unlinked from is the interesting case, because on
                // Windows an unlinked file whose handle is still open keeps
                // its name until that handle closes, and creating over it
                // is refused.
                let file = env.open_log(path, WriteMode::Truncate).map_err(named)?;
                file.write_all_at(0, &wal_frame::encode_stamp(nonce))?;
                (file, None, wal_frame::STAMP_LEN as u64, false)
            }
        };
        Ok(Self {
            file,
            path: path.to_path_buf(),
            env: Arc::clone(env),
            nonce,
            seal,
            stamp_len,
            durable: AtomicU64::new(if synced { stamp_len } else { 0 }),
            parent_synced: AtomicBool::new(synced),
            epoch: AtomicU64::new(0),
            writers: AtomicUsize::new(0),
            poisoned: AtomicBool::new(false),
            failure: Take::empty(),
        })
    }

    /// Take over a log an appending writer began: the same file, opened to
    /// be written by position from `offset` on. `durable` is the offset the
    /// appending writer's last completed sync covered. What open does with
    /// the log it rewrote the recovered writes into.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn adopt(
        env: &Arc<dyn Env>,
        path: &Path,
        nonce: u64,
        seal: Option<Sealer>,
        stamp_len: u64,
        durable: u64,
        parent_synced: bool,
    ) -> io::Result<Self> {
        let file = env.open_log(path, WriteMode::Update)?;
        Ok(Self {
            file,
            path: path.to_path_buf(),
            env: Arc::clone(env),
            nonce,
            seal,
            stamp_len,
            durable: AtomicU64::new(durable),
            parent_synced: AtomicBool::new(parent_synced),
            epoch: AtomicU64::new(0),
            writers: AtomicUsize::new(0),
            poisoned: AtomicBool::new(false),
            failure: Take::empty(),
        })
    }

    /// Create a log through the standard environment.
    #[cfg(test)]
    pub(crate) fn create(path: &Path) -> io::Result<Self> {
        Self::create_in(&crate::env::std_env(), path, None)
    }

    /// Get the path to this log.
    pub(crate) fn path(&self) -> &Path {
        &self.path
    }

    /// The key this log is sealed under, or `None` when it is not sealed.
    pub(crate) fn seal_key(&self) -> Option<crate::KeyId> {
        self.seal.as_ref().map(Sealer::id)
    }

    /// Offset of the first record: the bytes of the stamp.
    pub(crate) fn stamp_len(&self) -> u64 {
        self.stamp_len
    }

    /// Every byte below this offset is durable.
    pub(crate) fn durable(&self) -> u64 {
        self.durable.load(Ordering::Acquire)
    }

    /// Bytes a record occupies in front of its operations: where
    /// [`Log::finish_record`] expects them to start in the buffer.
    pub(crate) fn prefix_len(&self) -> usize {
        if self.seal.is_some() {
            SEALED_PREFIX_LEN
        } else {
            HEADER_LEN
        }
    }

    /// Bytes the record of `payload_len` bytes of operations occupies.
    pub(crate) fn framed_len(&self, payload_len: usize) -> u64 {
        let overhead = if self.seal.is_some() { OVERHEAD } else { 0 };
        (HEADER_LEN + payload_len + overhead) as u64
    }

    /// The log's write epoch: the one a record decided now is written in.
    pub(crate) fn epoch(&self) -> u64 {
        self.epoch.load(Ordering::SeqCst)
    }

    /// Start a log nothing was written to yet in `epoch`, the pipeline's.
    pub(crate) fn start_epoch(&self, epoch: u64) {
        self.epoch.store(epoch, Ordering::SeqCst);
    }

    /// Fix where the record of `payload_len` bytes of operations goes, at
    /// `offset`, and what frames it. Called once per commit, when it is
    /// decided; a sealed log draws the record's nonce here. `epoch` is the
    /// write epoch of the state the commit was decided from, not the log's
    /// own at this instant: a commit decided from a state a rollback has
    /// since discarded must not be written.
    pub(crate) fn place(&self, offset: u64, payload_len: usize, epoch: u64) -> io::Result<Place> {
        let nonce = match &self.seal {
            Some(_) => super::seal::fresh_nonce()?,
            None => [0u8; NONCE_LEN],
        };
        Ok(Place {
            offset,
            len: self.framed_len(payload_len),
            // A record claims only what is behind it. `durable` never passes
            // the offset of a record not yet written, so the bound only
            // matters to a reader of this line.
            synced_through: self.durable().min(offset),
            nonce,
            epoch,
        })
    }

    /// Turn `buf` into the record `place` describes. On entry `buf` holds
    /// [`Log::prefix_len`] bytes of room followed by the record's
    /// operations; on return it holds the whole record, `place.len` bytes.
    /// The same `place` and operations give the same bytes on every thread.
    pub(crate) fn finish_record(
        &self,
        kind: u8,
        place: &Place,
        buf: &mut Vec<u8>,
    ) -> io::Result<()> {
        match &self.seal {
            Some(sealer) => wal_seal::frame_in_place(
                sealer,
                kind,
                place.synced_through,
                self.nonce,
                place.offset,
                &place.nonce,
                buf,
            )?,
            None => {
                let header = wal_frame::encode_header(
                    kind,
                    &buf[HEADER_LEN..],
                    place.synced_through,
                    self.nonce,
                    place.offset,
                );
                buf[..HEADER_LEN].copy_from_slice(&header);
            }
        }
        debug_assert_eq!(
            buf.len() as u64,
            place.len,
            "a record's length is fixed when placed"
        );
        Ok(())
    }

    /// Write `record`, built by [`Log::finish_record`] for `place`, at its
    /// offset. `Ok(false)` when the commit it belongs to was discarded by a
    /// rollback since it was decided: nothing is written.
    pub(crate) fn write_record(&self, place: &Place, record: &[u8]) -> io::Result<bool> {
        // Counted in before the epoch is read: a rollback that moved the
        // epoch and then saw no writer cannot have missed this one.
        self.writers.fetch_add(1, Ordering::SeqCst);
        let current = self.epoch.load(Ordering::SeqCst) == place.epoch;
        let wrote = if current {
            self.file.write_all_at(place.offset, record)
        } else {
            Ok(())
        };
        self.writers.fetch_sub(1, Ordering::SeqCst);
        wrote.map(|()| current)
    }

    /// Make every byte below `through` durable, where `through` is the end
    /// of the contiguous prefix every record of which is written. The one
    /// place a commit waits for the device. The caller holds the pipeline's
    /// sync claim, so no other sync of this log and no rollback is running.
    ///
    /// `sync_data` (`fdatasync`), not `sync_all`, as [`super::wal::Wal`]
    /// syncs. The directory entry naming the file is synced once, on the
    /// first sync. Only a sync that completes advances the durable offset,
    /// and only to `through`.
    pub(crate) fn sync_through(&self, through: u64) -> io::Result<()> {
        if self.poisoned.load(Ordering::Acquire) {
            return Err(io::Error::other(
                "the write-ahead log failed and its unfinished commits are being discarded",
            ));
        }
        #[cfg(test)]
        if super::wal::fault::should_fail_sync(&self.path) {
            return Err(io::Error::other("injected WAL sync failure"));
        }
        self.file.sync_data()?;
        if !self.parent_synced.load(Ordering::Acquire) {
            crate::env::sync_parent_dir(&*self.env, &self.path)?;
            self.parent_synced.store(true, Ordering::Release);
        }
        self.durable.fetch_max(through, Ordering::AcqRel);
        Ok(())
    }

    /// Record that a write or a sync of this log failed with `err`. Until
    /// [`Log::rollback_to`] has discarded what the failure left, no sync
    /// vouches for the log. The first failure is the one kept.
    pub(crate) fn poison(&self, err: io::Error) {
        if !self.poisoned.swap(true, Ordering::AcqRel) {
            self.failure.put(err);
        }
    }

    /// Whether a failure is waiting for its rollback.
    pub(crate) fn is_poisoned(&self) -> bool {
        self.poisoned.load(Ordering::Acquire)
    }

    /// Cut the log back to `offset`, discarding every record at and after
    /// it, and hand back what poisoned the log, if anything did. Called by
    /// the thread that holds the pipeline's sync claim, so no sync of this
    /// log is running.
    ///
    /// Moves the write epoch on to `epoch`, which no record of this log was
    /// decided in, and waits for the writes already past the gate, so no
    /// write of a discarded commit lands after the cut (see the module
    /// docs). The wait is for positional writes already in flight.
    pub(crate) fn rollback_to(
        &self,
        offset: u64,
        epoch: u64,
    ) -> (Option<io::Error>, io::Result<()>) {
        debug_assert!(
            offset >= self.stamp_len && offset >= self.durable(),
            "a rollback reaches neither into the stamp nor below what a sync covered"
        );
        self.epoch.store(epoch, Ordering::SeqCst);
        while self.writers.load(Ordering::SeqCst) != 0 {
            std::thread::yield_now();
        }
        let cut = self.file.set_len(offset);
        let cause = self.failure.take();
        if cut.is_ok() {
            self.poisoned.store(false, Ordering::Release);
        }
        (cause, cut)
    }

    /// Close the log cleanly, whose records end at `end`: sync every record,
    /// write CLOSE, and sync again, so replay finds CLOSE and knows the
    /// whole file is durable. The order is [`super::wal::Wal::close`]'s, for
    /// the reason given there (`proofs/tla/WalRecovery.tla`, RED
    /// `CloseWithoutSync`). Called with the pipeline drained.
    pub(crate) fn close(&self, end: u64) -> io::Result<()> {
        self.sync_through(end)?;
        let mut record = vec![0u8; self.prefix_len()];
        let place = self.place(end, 0, self.epoch())?;
        self.finish_record(wal_frame::KIND_CLOSE, &place, &mut record)?;
        self.write_record(&place, &record)?;
        self.sync_through(place.end())
    }
}

impl std::fmt::Debug for Log {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Log")
            .field("path", &self.path)
            .field("durable", &self.durable())
            .field("sealed", &self.seal.is_some())
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
#[path = "wal_log_tests.rs"]
mod tests;
