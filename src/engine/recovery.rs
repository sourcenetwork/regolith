//! Recovery from the write-ahead logs at open: replay them into a
//! memtable, deal with the newest log's discarded tail, give the tables an
//! open moved out of overlapping levels their range tombstones back in
//! front, and rewrite what was recovered into a fresh log.

use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::internal_key;
use super::manifest::Demotion;
use super::memtable::MemTable;
use super::range_tombstone::RangeTombstone;
use super::seal::Keyring;
use super::wal::{self, TailVerdict, Wal, WalEntry};
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
///
/// The logs' range tombstones go into the memtable together, once every
/// log is read: nothing reads the memtable before that, and one batch costs
/// the memtable one pass where a tombstone at a time can cost it one each
/// (`MemTable::delete_ranges`). They are moved out of the records, so
/// gathering them holds nothing the memtable would not.
pub(super) fn replay_logs(
    env: &Arc<dyn Env>,
    wal_files: &[PathBuf],
    memtable: &MemTable,
    mut latest_seq: u64,
    keyring: Option<&Keyring>,
) -> io::Result<(u64, Option<(PathBuf, TailVerdict)>)> {
    let mut discarded = None;
    let mut range_deletes = Vec::new();
    for (i, path) in wal_files.iter().enumerate() {
        tracing::info!(path = %path.display(), "Replaying WAL");
        let position = if i + 1 == wal_files.len() {
            WalPosition::Newest
        } else {
            WalPosition::Earlier
        };
        let mut replay = WalReplayIter::open(env, path, position, keyring)?;
        while let Some(entry) = replay.next_entry()? {
            latest_seq = latest_seq.max(match entry {
                WalEntry::DeleteRange { start, end, seq } => {
                    range_deletes.push(RangeTombstone::new(start, end, seq));
                    seq
                }
                point => super::apply_replayed_wal_entry(memtable, point),
            });
        }
        if let Some(tail) = replay.discarded_tail() {
            discarded = Some((path.clone(), tail));
        }
    }
    memtable.delete_ranges(range_deletes);
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

/// What an open moved out of overlapping levels, once its tables' range
/// tombstones are in the memtable: what is left to report.
#[derive(Clone, Copy)]
pub(super) struct Moved {
    /// Tables moved to level 0.
    pub(super) tables: u64,
    /// The deepest level that held overlapping tables.
    pub(super) deepest_level: usize,
    /// Range tombstones of those tables, pieces of one delete joined.
    pub(super) range_deletes: usize,
}

/// Put the range tombstones of the tables the open moved out of
/// overlapping levels into `memtable`. Returns what the open moved, `None`
/// when it moved nothing, and the largest sequence recovered, at least
/// `latest_seq`.
///
/// A moved table can hold a range tombstone newer than a key it covers in
/// a source read before it (`manifest/legacy_overlap.rs`), and a read stops
/// at the first source holding the key. The recovered memtable is the
/// newest source, so from it each tombstone is in front of every key it
/// covers, wherever a later flush or compaction takes its table. The log
/// the open writes from this memtable keeps it there across a restart.
/// One a replayed log already brought is not added again.
///
/// One batch: its cost is linear in the tombstones copied, however many
/// share a sequence (`MemTable::delete_ranges`). They are moved in, not
/// cloned, so the copy holds each once. How many there can be is bounded by
/// what the moved tables hold, which their readers keep in memory already;
/// their bytes count toward the memtable's size, so the first write that
/// finds it past the write buffer seals it, and its flush writes them to
/// one level 0 table like any other range tombstone.
pub(super) fn hoist_range_deletes(
    demotion: Option<Demotion>,
    memtable: &MemTable,
    latest_seq: u64,
) -> (Option<Moved>, u64) {
    let Some(demotion) = demotion else {
        return (None, latest_seq);
    };
    let moved = Moved {
        tables: demotion.tables,
        deepest_level: demotion.deepest_level,
        range_deletes: demotion.range_deletes.len(),
    };
    let newest = demotion.range_deletes.iter().map(|t| t.seq).max();
    memtable.delete_ranges(demotion.range_deletes);
    (
        Some(moved),
        newest.map_or(latest_seq, |seq| latest_seq.max(seq)),
    )
}

/// Tell the operator that the open moved tables out of levels an earlier
/// release left overlapping: one warn line and the `ManifestTablesDemoted`
/// ticker. `manifest` is the file that lists them.
///
/// A read-write open calls this once the move is recorded, so a later
/// open has nothing to move and reports nothing. A read-only open moves
/// them in its own view, every time.
pub(super) fn report_demoted_tables(
    options: &super::EngineOptions,
    manifest: &Path,
    demotion: Moved,
    read_only: bool,
) {
    let message = if read_only {
        "moved tables an earlier release left with overlapping key ranges to level 0 \
         for this read-only open: open the database for writing once to keep the move"
    } else {
        "moved tables an earlier release left with overlapping key ranges to level 0: \
         no data was lost and no action is needed"
    };
    tracing::warn!(
        path = %manifest.display(),
        tables = demotion.tables,
        deepest_level = demotion.deepest_level,
        range_deletes = demotion.range_deletes,
        read_only,
        "{message}"
    );
    if let Some(stats) = options.statistics.as_ref() {
        stats.add(Ticker::ManifestTablesDemoted, demotion.tables);
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
