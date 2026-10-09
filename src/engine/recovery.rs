//! Recovery from the write-ahead logs at open: replay them into a
//! memtable, deal with the newest log's discarded tail, and rewrite what
//! was recovered into a fresh log.

use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::internal_key;
use super::memtable::MemTable;
use super::seal::Keyring;
use super::wal::{self, TailVerdict, Wal};
use super::wal_replay::{WalPosition, WalReplayIter};
use crate::env::Env;
use crate::event_listener::WalTailDiscardedInfo;
use crate::statistics::Ticker;

const GROUP_BYTES: usize = 64 * 1024;

/// Replay `wal_files`, in id order, into `memtable`.
///
/// Returns the largest sequence number recovered, at least
/// `latest_seq`, and the tail the newest log dropped, if it dropped one,
/// with that log's path. Only the newest log can drop a tail; damage in
/// an earlier one is an error. Sealed logs are read through `keyring`.
pub(super) fn replay_logs(
    env: &Arc<dyn Env>,
    wal_files: &[PathBuf],
    memtable: &MemTable,
    mut latest_seq: u64,
    keyring: Option<&Keyring>,
) -> io::Result<(u64, Option<(PathBuf, TailVerdict)>)> {
    let mut discarded = None;
    for (i, path) in wal_files.iter().enumerate() {
        tracing::info!(path = %path.display(), "Replaying WAL");
        let position = if i + 1 == wal_files.len() {
            WalPosition::Newest
        } else {
            WalPosition::Earlier
        };
        let mut replay = WalReplayIter::open(env, path, position, keyring)?;
        while let Some(entry) = replay.next_entry()? {
            latest_seq = latest_seq.max(super::apply_replayed_wal_entry(memtable, entry));
        }
        if let Some(tail) = replay.discarded_tail() {
            discarded = Some((path.clone(), tail));
        }
    }
    Ok((latest_seq, discarded))
}

/// Tell the operator that replay dropped `tail` of the log at `path`:
/// a warn line, the `WalTailDiscarded` and `WalTailDiscardedBytes`
/// tickers, and every listener's
/// [`crate::EventListener::on_wal_tail_discarded`]. `last_sequence` is
/// the newest write the open kept.
///
/// Runs on the thread that opens the database. A listener that panics
/// fails that open, like any panic outside a commit.
pub(super) fn report_discarded_tail(
    options: &super::EngineOptions,
    path: &Path,
    tail: TailVerdict,
    last_sequence: u64,
) {
    tracing::warn!(
        path = %path.display(),
        offset = tail.offset,
        discarded_bytes = tail.discarded_bytes,
        last_sequence,
        "discarded the end of the write-ahead log: no surviving record proves it was made durable"
    );
    if let Some(stats) = options.statistics.as_ref() {
        stats.add(Ticker::WalTailDiscarded, 1);
        stats.add(Ticker::WalTailDiscardedBytes, tail.discarded_bytes);
    }
    let info = WalTailDiscardedInfo {
        file_path: path.to_path_buf(),
        offset: tail.offset,
        discarded_bytes: tail.discarded_bytes,
        last_sequence,
    };
    crate::event_listener::dispatch(&options.listeners, |l| l.on_wal_tail_discarded(&info));
}

/// Tell the operator that the open dropped `tail` of the manifest at
/// `path` as a crash's unsynced tail: a warn line, and the
/// `ManifestTailDiscarded` and `ManifestTailDiscardedBytes` tickers.
pub(super) fn report_dropped_manifest_tail(
    options: &super::EngineOptions,
    path: &Path,
    tail: super::manifest::DroppedTail,
) {
    tracing::warn!(
        path = %path.display(),
        offset = tail.offset,
        discarded_bytes = tail.bytes,
        "discarded the end of the MANIFEST: no later batch proves it was made durable"
    );
    if let Some(stats) = options.statistics.as_ref() {
        stats.add(Ticker::ManifestTailDiscarded, 1);
        stats.add(Ticker::ManifestTailDiscardedBytes, tail.bytes);
    }
}

pub(super) fn rewrite_recovered_memtable_to_wal(
    memtable: &MemTable,
    wal: &mut Wal,
) -> io::Result<()> {
    let mut groups = RecoveryGroups::new(wal);
    memtable.try_for_each_entry(|internal_key, value| {
        let (user_key, seq, value_type) = internal_key::decode_internal_key(internal_key);
        match value_type {
            internal_key::VALUE_TYPE_VALUE => groups
                .record(wal::put_record_len(user_key, value), |out| {
                    wal::encode_put_record(out, user_key, value, seq)
                }),
            internal_key::VALUE_TYPE_DELETION => groups
                .record(wal::delete_record_len(user_key), |out| {
                    wal::encode_delete_record(out, user_key, seq)
                }),
            internal_key::VALUE_TYPE_MERGE => groups
                .record(wal::merge_record_len(user_key, value), |out| {
                    wal::encode_merge_record(out, user_key, value, seq)
                }),
            other => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("unknown value type {other} in recovered memtable"),
            )),
        }
    })?;

    for tombstone in memtable.clone_range_tombstones() {
        groups.record(
            wal::delete_range_record_len(&tombstone.start, &tombstone.end),
            |out| {
                wal::encode_delete_range_record(
                    out,
                    &tombstone.start,
                    &tombstone.end,
                    tombstone.seq,
                )
            },
        )?;
    }
    groups.finish()
}

struct RecoveryGroups<'a> {
    wal: &'a mut Wal,
    buffer: Vec<u8>,
    wrote_record: bool,
}

impl<'a> RecoveryGroups<'a> {
    fn new(wal: &'a mut Wal) -> Self {
        Self {
            wal,
            buffer: Vec::with_capacity(GROUP_BYTES),
            wrote_record: false,
        }
    }

    fn record(&mut self, len: usize, encode: impl FnOnce(&mut Vec<u8>)) -> io::Result<()> {
        if len > GROUP_BYTES {
            self.flush()?;
            // Keep a large record separate so the reusable group stays bounded.
            let mut record = Vec::with_capacity(len);
            encode(&mut record);
            self.wal.append_group(&record)?;
        } else {
            if len > GROUP_BYTES - self.buffer.len() {
                self.flush()?;
            }
            encode(&mut self.buffer);
        }
        self.wrote_record = true;
        Ok(())
    }

    fn flush(&mut self) -> io::Result<()> {
        if !self.buffer.is_empty() {
            self.wal.append_group(&self.buffer)?;
            self.buffer.clear();
        }
        Ok(())
    }

    fn finish(mut self) -> io::Result<()> {
        if self.wrote_record {
            self.flush()?;
            // The caller retains old WALs until the entire replacement is durable.
            self.wal.sync_data()?;
        }
        Ok(())
    }
}
