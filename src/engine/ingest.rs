//! External-table ingest without a rewrite (D48, E8).
//!
//! An ingest moves a table built outside the database into it in two phases.
//!
//! **Staging** holds no lock, so writers never wait for it. The file is
//! copied into the table directory, or hard-linked when the caller lets it
//! move, and synced; then the copy is validated where it will be served
//! from: key and value sizes, live column families, and one entry per user
//! key, which is what lets every entry read at one sequence.
//!
//! **Installing** runs under the compaction lock, which keeps every level
//! below L0 as it is and lets L0 only grow, and takes the commit pipeline's
//! mutex only for what has to be ordered against commits:
//!
//! 1. flush the memtables holding a key of the table's range, so writers
//!    wait for a flush only when there is an overlap;
//! 2. place the table: the deepest level L such that no L0 table holds a
//!    key of its range and no table of levels 1..L overlaps it, else the
//!    front of L0 (LsmOrder.tla, `Ingest = "Placed"`; Lean
//!    `ingest_ordered`). A flush in step 1 lands in L0 holding such a key,
//!    so it places the table in L0;
//! 3. sync the active log, so every commit ordered before the ingest is
//!    durable before the ingest is: the memtables step 1 left alone may
//!    hold commits only the log has (IngestDurability.tla);
//! 4. draw the table's sequence;
//! 5. one manifest edit adds the table, recording the sequence its entries
//!    read at (`SsTableMeta::global_seq`), and raises the last sequence;
//! 6. publish the sequence on the read horizon.
//!
//! A commit draws and publishes under the same mutex, so from the draw to
//! the publish the sequence is a pending slot no publication passes
//! (IngestPublication.tla, `RepeatableSnapshot`; Lean
//! `repeatable_snapshot`). A snapshot taken before the publish reads none of
//! the table, whose entries read at the new sequence, and one taken after
//! reads all of it.
//!
//! Which L0 tables hold a key of the range is read before the mutex is
//! taken, since it can read a block; under the mutex only a table that
//! arrived in L0 since then is probed.

use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::env::WriteMode;
use crate::portability::{AtomicU64, Ordering};
use crate::sst_file_writer::IngestOptions;

use super::block_cache::BlockCache;
use super::internal_key::decode_internal_key;
use super::lookup_key::with_key_scratch;
use super::manifest::{MAX_LEVELS, Version, VersionEdit, overlapping};
use super::memtable::MemTable;
use super::pending_outputs::PendingOutputs;
use super::range_tombstone::table_key_range;
use super::sstable::{LiveSst, SsTableMeta, SsTableReader, sst_filename};
use super::{RegolithEngine, event_listener};

/// Block-cache ids for tables being validated, handed out downward from the
/// top of the id space, which `next_file_id` counts up from 1 and never
/// reaches. Unique across concurrent ingests: two tables validated under one
/// id would read each other's cached blocks.
static NEXT_PROBE_ID: AtomicU64 = AtomicU64::new(u64::MAX);

/// A table copied or linked into the table directory and validated, not yet
/// in the version.
struct StagedTable {
    /// The path the caller handed in.
    source: PathBuf,
    /// Where the table now lives, under the id it will be installed with.
    path: PathBuf,
    file_id: u64,
    /// Open under a probe id until the install binds it to `file_id` and
    /// the table's sequence.
    reader: SsTableReader,
    smallest: Vec<u8>,
    largest: Vec<u8>,
    file_size: u64,
    num_entries: u64,
    /// The column families the table holds keys of, ascending, each once.
    /// The install fences them in the ordered step, as a write's keys are.
    families: Vec<u32>,
    /// Unlinks the staged file if the ingest ends before the manifest
    /// edit names it.
    pending: PendingOutputs,
}

/// The table one source was installed as, for the listeners and the log.
struct IngestedTable {
    file_id: u64,
    path: PathBuf,
    level: usize,
    seq: u64,
    file_size: u64,
    num_entries: u64,
}

/// Drops the validation reads from the shared block cache when the ingest
/// returns, by any path: they were read under probe ids nothing asks for
/// again.
struct ProbeIds<'a> {
    cache: &'a BlockCache,
    ids: Vec<u64>,
}

impl ProbeIds<'_> {
    fn next(&mut self) -> u64 {
        let id = NEXT_PROBE_ID.fetch_sub(1, Ordering::Relaxed);
        self.ids.push(id);
        id
    }
}

impl Drop for ProbeIds<'_> {
    fn drop(&mut self) {
        for &id in &self.ids {
            self.cache.evict_file(id);
        }
    }
}

impl RegolithEngine {
    /// Bulk-ingest externally built tables, each at a fresh sequence,
    /// without rewriting them (D48).
    ///
    /// Each file is copied into the table directory, or hard-linked when
    /// `move_files` is set and the environment has hard links, with no lock
    /// held. Writers then wait only for a flush of a memtable holding a key
    /// of the file's range, if there is one, and for the manifest edit that
    /// installs it. The entries order after every write acknowledged before
    /// the call and before every write acknowledged after it, and no
    /// snapshot sees them appear under it. Files are installed one at a
    /// time; an error leaves the ones before it installed.
    ///
    /// With `move_files`, each source path is removed once its table is
    /// installed; a source whose removal fails is left and logged, since
    /// the ingest itself succeeded. A crash between the install and the
    /// removal leaves it too.
    pub(crate) fn ingest_external_files<F>(
        &self,
        files: &[PathBuf],
        opts: &IngestOptions,
        mut validate_user_key: F,
    ) -> io::Result<()>
    where
        F: FnMut(&[u8]) -> io::Result<()>,
    {
        self.ensure_writable()?;
        if files.is_empty() {
            return Ok(());
        }
        if opts.snapshot_consistency && self.oldest_live_seq() != u64::MAX {
            return Err(io::Error::other(
                "ingest_external_files: snapshot isolation would be violated \
                 because a live snapshot is pinned (use snapshot_consistency=false \
                 to override)",
            ));
        }

        let mut probes = ProbeIds {
            cache: &self.cache,
            ids: Vec::with_capacity(files.len()),
        };
        let mut staged = Vec::with_capacity(files.len());
        for path in files {
            staged.push(self.stage(path, opts, &mut validate_user_key, &mut probes)?);
        }

        // Excludes every compaction, so the levels the placement reads stay
        // as they are until the table is in.
        let _compact_guard = self.compaction_lock.write();
        self.ensure_writable()?;
        for table in staged {
            let source = table.source.clone();
            let installed = self.install(table, opts)?;
            self.announce(&source, &installed);
            if opts.move_files
                && let Err(e) = crate::env::remove_file_and_sync_parent(&*self.env, &source)
            {
                tracing::warn!(
                    source = %source.display(),
                    error = %e,
                    "could not remove an ingested file's source"
                );
            }
        }
        self.compaction.lock().notify();
        Ok(())
    }

    /// Copy or link `source` into the table directory under a fresh id,
    /// sync it, and validate the copy. Takes no lock beyond the id
    /// allocation's.
    fn stage<F>(
        &self,
        source: &Path,
        opts: &IngestOptions,
        validate_user_key: &mut F,
        probes: &mut ProbeIds<'_>,
    ) -> io::Result<StagedTable>
    where
        F: FnMut(&[u8]) -> io::Result<()>,
    {
        let named =
            |e: io::Error| io::Error::new(e.kind(), format!("ingest: {}: {e}", source.display()));
        let file_id = {
            let mut versions = self.versions.lock();
            let id = versions.current().next_file_id;
            versions.apply(&[VersionEdit::SetNextFileId(id + 1)])?;
            id
        };
        let path = self.sst_dir.join(sst_filename(file_id));
        let mut pending = PendingOutputs::new(Arc::clone(&self.env));
        pending.track(path.clone());

        // A link shares the source's inode, so it is only taken when the
        // caller lets the file move: a source rewritten in place later
        // would rewrite the table. A link that fails, across devices say,
        // falls back to a copy.
        let linked = opts.move_files
            && self.env.capabilities().hard_link
            && self.env.hard_link(source, &path).is_ok();
        if linked {
            // The source's writer may never have synced it.
            self.env
                .open_write(&path, WriteMode::Update)
                .and_then(|mut file| file.sync_all())
                .map_err(named)?;
        } else {
            let len = self.env.metadata(source).map_err(named)?.len;
            crate::checkpoint::copy_truncated(&*self.env, source, &path, len).map_err(named)?;
        }
        crate::env::sync_parent_dir(&*self.env, &path)?;

        #[cfg(test)]
        if let Some(hook) = WHILE_INGEST_STAGES.with(|slot| slot.borrow_mut().take()) {
            hook();
        }

        let reader = SsTableReader::open_with(
            &self.env,
            &path,
            probes.next(),
            self.options.metadata_policy(),
        )
        .map_err(named)?;
        let mut families = Vec::new();
        let (points, num_entries) = self
            .validate_entries(&reader, validate_user_key, &mut families)
            .map_err(named)?;
        let tombstones = reader.range_tombstones();
        for rt in tombstones {
            note_family(&mut families, &rt.start);
            for (bound, which) in [(&rt.start, "start"), (&rt.end, "end")] {
                self.validate_prefixed_key_size(bound)
                    .and_then(|()| validate_user_key(bound))
                    .map_err(|e| {
                        io::Error::new(
                            e.kind(),
                            format!(
                                "ingest: {} holds a range tombstone {which} it cannot take: {e}",
                                source.display()
                            ),
                        )
                    })?;
            }
        }
        // The range the table is placed by and recorded with, tombstones
        // included.
        let Some((smallest, largest)) = table_key_range(points, tombstones) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("ingest: source file {} is empty", source.display()),
            ));
        };
        let file_size = self.env.metadata(&path)?.len;
        families.sort_unstable();
        families.dedup();
        Ok(StagedTable {
            source: source.to_path_buf(),
            path,
            file_id,
            reader,
            smallest,
            largest,
            file_size,
            num_entries,
            families,
            pending,
        })
    }

    /// Stream every entry of a staged table once, holding one data block:
    /// sizes, column families, and strictly ascending user keys. Returns
    /// the first and last user key, and the entry count.
    #[allow(clippy::type_complexity)]
    fn validate_entries<F>(
        &self,
        reader: &SsTableReader,
        validate_user_key: &mut F,
        families: &mut Vec<u32>,
    ) -> io::Result<(Option<(Vec<u8>, Vec<u8>)>, u64)>
    where
        F: FnMut(&[u8]) -> io::Result<()>,
    {
        let mut first: Option<Vec<u8>> = None;
        let mut last: Vec<u8> = Vec::new();
        let mut count = 0u64;
        let mut entries = reader.iter_internal_stream(&self.cache)?;
        while let Some((ik, value)) = entries.next_entry()? {
            let (user_key, _, _) = decode_internal_key(&ik);
            self.validate_prefixed_key_size(user_key)?;
            self.validate_value_size(&value)?;
            validate_user_key(user_key).map_err(|e| {
                io::Error::new(
                    e.kind(),
                    format!("holds a key outside live column families: {e}"),
                )
            })?;
            // Every entry reads at the one sequence the ingest draws, so two
            // entries of one key would have no order between them.
            if first.is_some() && user_key <= last.as_slice() {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "holds more than one entry for a key, or keys out of order; \
                     an ingested file holds each key once, as SstFileWriter writes it",
                ));
            }
            if first.is_none() {
                first = Some(user_key.to_vec());
            }
            note_family(families, user_key);
            last.clear();
            last.extend_from_slice(user_key);
            count += 1;
        }
        Ok((first.map(|first| (first, last)), count))
    }

    /// Install one staged table: steps 1 to 6 of the module docs.
    fn install(&self, table: StagedTable, opts: &IngestOptions) -> io::Result<IngestedTable> {
        let (lo, hi) = (table.smallest.as_slice(), table.largest.as_slice());
        let probed = if opts.ingest_behind {
            Vec::new()
        } else {
            self.l0_holders(&self.published_version(), lo, hi)?
        };

        let _pipeline = self.pipeline.lock();
        // The ordered step: a family the table writes into that a drop
        // retired since the table was validated refuses the install, before
        // it takes a sequence.
        self.cf_fence_ids(&table.families)?;
        let level = if opts.ingest_behind {
            self.behind_level(lo, hi)?
        } else if self.flush_memtables_holding(lo, hi)? {
            0
        } else {
            let version = self.published_version();
            let mut holds =
                |file: &LiveSst| match probed.iter().find(|(id, _)| *id == file.meta.file_id) {
                    Some(&(_, holds)) => Ok(holds),
                    None => self.table_holds(file, lo, hi),
                };
            placement(&version, lo, hi, &mut holds)?
        };
        self.sync_active_wal()?;

        let seq = self.latest_seq.fetch_add(1, Ordering::AcqRel) + 1;

        #[cfg(test)]
        if let Some(hook) = AFTER_INGEST_SEQ.with(|slot| slot.borrow_mut().take()) {
            hook();
        }

        let StagedTable {
            path,
            file_id,
            reader,
            smallest,
            largest,
            file_size,
            num_entries,
            pending,
            ..
        } = table;
        let reader = reader.rebind(file_id).with_global_seq(Some(seq));
        let file = LiveSst::new(
            SsTableMeta {
                file_id,
                smallest_key: smallest,
                largest_key: largest,
                file_size,
                num_entries,
                global_seq: Some(seq),
            },
            Arc::new(reader),
        );
        pending.offered_to_manifest();
        self.versions.lock().apply(&[
            VersionEdit::AddFile { level, file },
            VersionEdit::SetLastSeq(seq),
        ])?;
        self.visible_seq.publish(seq);

        Ok(IngestedTable {
            file_id,
            path,
            level,
            seq,
            file_size,
            num_entries,
        })
    }

    /// The L0 tables of `version` whose recorded range meets `[lo, hi]`,
    /// each with whether it holds a key of `[lo, hi]`.
    fn l0_holders(&self, version: &Version, lo: &[u8], hi: &[u8]) -> io::Result<Vec<(u64, bool)>> {
        version.levels[0]
            .iter()
            .filter(|file| meets(file, lo, hi))
            .map(|file| Ok((file.meta.file_id, self.table_holds(file, lo, hi)?)))
            .collect()
    }

    fn table_holds(&self, file: &LiveSst, lo: &[u8], hi: &[u8]) -> io::Result<bool> {
        with_key_scratch(|buf| file.reader.holds_key_in(lo, hi, buf, &self.cache))
    }

    /// Flush, oldest first, every memtable up to the newest one holding a
    /// key of `[lo, hi]`, and say whether there was one. Caller holds the
    /// pipeline mutex, so the active memtable takes no write meanwhile.
    fn flush_memtables_holding(&self, lo: &[u8], hi: &[u8]) -> io::Result<bool> {
        let view = self.view.load();
        let target = if view.active.holds_key_in(lo, hi) {
            drop(view);
            self.seal_active()?
        } else {
            match view.frozen.iter().rev().find(|mt| mt.holds_key_in(lo, hi)) {
                Some(frozen) => Arc::clone(frozen),
                None => return Ok(false),
            }
        };
        let flushed = self.flush_until_retired(&target);
        self.refresh_stall_level();
        flushed?;
        Ok(true)
    }

    /// Sync the active log, so every commit ordered before the ingest is
    /// durable before the manifest record that makes the ingest durable:
    /// under `Eventual` a power cut must leave a gap-free prefix of commit
    /// order, and the memtables holding none of the file's keys are not
    /// flushed. A failed sync latches the log, as a rotation's does. Caller
    /// holds the pipeline mutex, so no group is appending.
    fn sync_active_wal(&self) -> io::Result<()> {
        let mut guard = self.active_wal.lock();
        let wal = guard.as_mut().ok_or_else(Self::read_only_error)?;
        if let Err(err) = wal.sync_data() {
            drop(guard);
            tracing::error!(error = %err, "syncing the write-ahead log before an ingest failed");
            self.latch_wal_failure(&err);
            self.notify_wal_error(&err)?;
            return Err(err);
        }
        Ok(())
    }

    /// `ingest_behind`'s level: the bottom one, refused when anything in the
    /// tree holds or may hold a key of `[lo, hi]`. Caller holds the pipeline
    /// mutex.
    fn behind_level(&self, lo: &[u8], hi: &[u8]) -> io::Result<usize> {
        let view = self.view.load();
        let in_memory = std::iter::once(&view.active)
            .chain(view.frozen.iter())
            .any(|mt: &Arc<MemTable>| mt.holds_key_in(lo, hi));
        let in_tables = view
            .version
            .levels
            .iter()
            .any(|files| files.iter().any(|file| meets(file, lo, hi)));
        if in_memory || in_tables {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "ingest_behind: input range overlaps existing data",
            ));
        }
        Ok(MAX_LEVELS - 1)
    }

    /// Tell the listeners and the log about an installed table, with the
    /// pipeline released: a listener is user code.
    fn announce(&self, source: &Path, table: &IngestedTable) {
        if !self.options.listeners.is_empty() {
            let create_info = event_listener::TableFileCreationInfo {
                file_id: table.file_id,
                file_path: table.path.clone(),
                level: table.level,
                reason: event_listener::TableFileCreationReason::Recovery,
                file_size: table.file_size,
                num_entries: table.num_entries,
            };
            event_listener::dispatch(&self.options.listeners, |l| {
                l.on_table_file_created(&create_info)
            });
            let ingest_info = event_listener::ExternalFileIngestionInfo {
                external_file_path: source.to_path_buf(),
                internal_file_id: table.file_id,
                level: table.level,
                num_entries: table.num_entries,
                file_size: table.file_size,
            };
            event_listener::dispatch(&self.options.listeners, |l| {
                l.on_external_file_ingested(&ingest_info)
            });
        }
        tracing::info!(
            file_id = table.file_id,
            target_level = table.level,
            ingest_seq = table.seq,
            entries = table.num_entries,
            size = table.file_size,
            source = %source.display(),
            "Ingested external SSTable"
        );
    }
}

/// The table's recorded range meets `[lo, hi]`.
fn meets(file: &LiveSst, lo: &[u8], hi: &[u8]) -> bool {
    file.meta.smallest_key.as_slice() <= hi && lo <= file.meta.largest_key.as_slice()
}

/// Record the column family `key` belongs to, once per run of keys in one
/// family. Keys arrive sorted, so the run ends only when the family does.
fn note_family(families: &mut Vec<u32>, key: &[u8]) {
    if let Some(prefix) = key.first_chunk::<{ crate::column_family::CF_PREFIX_LEN }>() {
        let id = u32::from_be_bytes(*prefix);
        if families.last() != Some(&id) {
            families.push(id);
        }
    }
}

/// LsmOrder.tla's placement of a table of range `[lo, hi]`, nothing in the
/// memtables holding a key of it: the deepest level L such that no L0 table
/// holds a key of the range (`holds`) and no table of levels 1..L meets it;
/// 0, the front of L0, when there is none.
fn placement(
    version: &Version,
    lo: &[u8],
    hi: &[u8],
    holds: &mut dyn FnMut(&LiveSst) -> io::Result<bool>,
) -> io::Result<usize> {
    for file in version.levels[0].iter().filter(|file| meets(file, lo, hi)) {
        if holds(file)? {
            return Ok(0);
        }
    }
    Ok((1..MAX_LEVELS)
        .take_while(|&level| overlapping(&version.levels[level], lo, hi).is_empty())
        .last()
        .unwrap_or(0))
}

#[cfg(test)]
thread_local! {
    /// Test seam: runs once, on this thread, right after the next ingest
    /// has taken its sequence and before it installs its table.
    /// Thread-local so a parallel test never fires another test's hook.
    static AFTER_INGEST_SEQ: std::cell::RefCell<Option<Box<dyn FnOnce()>>> =
        const { std::cell::RefCell::new(None) };

    /// Test seam: runs once, on this thread, once the next ingest has
    /// copied or linked its file and before it validates it.
    static WHILE_INGEST_STAGES: std::cell::RefCell<Option<Box<dyn FnOnce()>>> =
        const { std::cell::RefCell::new(None) };
}

#[cfg(test)]
#[path = "ingest_tests.rs"]
mod tests;

/// Test-only: run `hook` once, on this thread, right after the next ingest
/// has taken its sequence and before it installs its table.
#[cfg(test)]
pub(crate) fn after_next_ingest_seq(hook: impl FnOnce() + 'static) {
    AFTER_INGEST_SEQ.with(|slot| *slot.borrow_mut() = Some(Box::new(hook)));
}

/// Test-only: run `hook` once, on this thread, while the next ingest stages
/// its file: copied or linked, before validation and before any lock.
#[cfg(test)]
pub(crate) fn while_next_ingest_stages(hook: impl FnOnce() + 'static) {
    WHILE_INGEST_STAGES.with(|slot| *slot.borrow_mut() = Some(Box::new(hook)));
}
