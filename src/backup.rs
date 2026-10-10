//! Content-addressed incremental backups.
//!
//! [`BackupEngine`] keeps a directory of backups that deduplicate
//! SSTable files across generations. Files are keyed in a `shared/`
//! subdirectory by an xxh3-based content id, and each backup's
//! metadata lists the `(level, file_id, content id, meta)` tuples that
//! reconstruct its version. Backing up an unchanged database a
//! second time adds only the per-backup metadata, not the data.
//! The content id and the metadata checksum are fast accidental-corruption
//! guards, not adversarial tamper protection.
//!
//! On-disk layout:
//!
//! ```text
//! backup_dir/
//!   meta/
//!     000001.backup       # per-backup metadata
//!     000002.backup
//!   shared/
//!     <32-hex>.sst        # content-hashed SST files
//! ```
//!
//! The backup directory may live on a different filesystem from
//! the source database - files are byte-copied, not hard-linked.
//! Restores stream bytes back out of `shared/` into a fresh
//! target directory and write a new MANIFEST reflecting the
//! captured version.
//!
//! # Encrypted databases
//!
//! A backup of a database encrypted at rest ([`crate::Options::key_provider`])
//! seals its metadata through the database's own key provider: the tables
//! are copied as they are, already sealed, and the `.backup` file seals each
//! table's key range and placement under the provider's current key, naming
//! that key so a backup taken before a rotation restores after it. A restore
//! takes a provider, refuses without one as the open does, and seals the
//! MANIFEST it writes. Only what `shared/` shows anyway stays readable
//! without a key: each table's content id and size, how many there are, and
//! when the backup was taken. The `.backup` format is described in
//! `src/backup/format.rs`; the rules are checked in
//! `proofs/tla/BackupSeal.tla` and `proofs/lean/Regolith/BackupSeal.lean`.

mod format;

use std::collections::HashSet;
use std::io::{self};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::engine::seal::Keyring;
use crate::engine::{CheckpointSnapshot, checksum};
use crate::env::{Env, ReadFileCursor, WriteMode};
use crate::{Db, Error, KeyProvider, Result};
use format::{BackupFileEntry, BackupManifest, Listing};

/// Opaque identifier for a single backup generation. Monotonically
/// increasing within a backup directory.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BackupId(pub u64);

impl std::fmt::Display for BackupId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// High-level summary of a backup returned from [`BackupEngine::list_backups`].
#[derive(Debug, Clone)]
pub struct BackupInfo {
    /// Backup identifier.
    pub id: BackupId,
    /// Unix timestamp (seconds) at which the backup was created.
    pub created_at_unix: u64,
    /// Number of SSTable files captured in the backup.
    pub file_count: usize,
    /// Total logical size (sum of SSTable file sizes) in bytes.
    pub bytes: u64,
}

/// A backup [`BackupEngine::list_backups`] found but could not read.
///
/// Its metadata file is in the repository, but what the backup holds cannot
/// be read: the file is damaged, was written by a version of regolith this
/// build does not read, or the disk failed the read. [`BackupEngine::restore`]
/// refuses it for the same reason.
///
/// While it is in the repository no shared file is removed, because nothing
/// can tell which ones it needs: [`BackupEngine::delete_backup`] and
/// [`BackupEngine::purge_old_backups`] still delete the backups they are
/// asked to, then fail naming it. Deleting it removes it like any other
/// backup.
#[derive(Debug, thiserror::Error)]
#[error("backup {id} cannot be read: {reason}")]
#[non_exhaustive]
pub struct UnreadableBackup {
    /// The backup's id, from its metadata file's name.
    pub id: BackupId,
    /// Why its metadata could not be read: [`Error::Corruption`] for a
    /// damaged file or a version this build does not read, [`Error::Io`]
    /// when the read itself failed.
    #[source]
    pub reason: Error,
}

/// Content-addressed backup repository for one or more databases.
///
/// Multiple [`BackupEngine`] instances must not share a backup directory:
/// there is no cross-process locking, and a delete or purge in one removes
/// every shared file no finished backup lists, including the tables another
/// one's unfinished backup has copied and not yet listed. A single process
/// may reuse one instance for many backups.
///
/// The engine holds no key. A backup of an encrypted database is sealed
/// through that database's provider ([`BackupEngine::create_backup`]), a
/// restore is given one ([`BackupEngine::restore`]), and listing, deleting
/// and purging read only what every backup keeps unsealed.
pub struct BackupEngine {
    root: PathBuf,
    meta_dir: PathBuf,
    shared_dir: PathBuf,
    env: Arc<dyn Env>,
}

impl BackupEngine {
    /// Open or create a backup repository at `backup_dir` on the
    /// standard filesystem.
    pub fn open<P: AsRef<Path>>(backup_dir: P) -> Result<Self> {
        Self::open_with_env(backup_dir, crate::env::std_env())
    }

    /// Open or create a backup repository at `backup_dir` on `env`.
    ///
    /// The repository does not have to live on the same environment
    /// as the database it backs up: bytes are copied, never linked.
    pub fn open_with_env<P: AsRef<Path>>(backup_dir: P, env: Arc<dyn Env>) -> Result<Self> {
        let root = backup_dir.as_ref().to_path_buf();
        let meta_dir = root.join("meta");
        let shared_dir = root.join("shared");
        env.create_dir_all(&meta_dir).map_err(Error::from)?;
        env.create_dir_all(&shared_dir).map_err(Error::from)?;
        crate::env::sync_parent_dir(&*env, &root).map_err(Error::from)?;
        env.sync_dir(&root).map_err(Error::from)?;
        env.sync_dir(&meta_dir).map_err(Error::from)?;
        env.sync_dir(&shared_dir).map_err(Error::from)?;
        Ok(Self {
            root,
            meta_dir,
            shared_dir,
            env,
        })
    }

    /// Root directory of this backup repository.
    pub fn path(&self) -> &Path {
        &self.root
    }

    /// Create a new backup of `db`, deduping against any files
    /// already present in the shared pool.
    ///
    /// On a database encrypted at rest the tables are copied as they are,
    /// sealed, and the backup's metadata is sealed under the database
    /// provider's current key, which it names. A current key the provider
    /// does not provide refuses with [`Error::UnknownKey`] before anything
    /// is copied. A backup of a database without a provider is written in
    /// plaintext, as it always was.
    ///
    /// The metadata is written last, after every table it lists is durable
    /// in `shared/`, so a crash part way leaves no backup and at most some
    /// unlisted shared files, which a later backup of the same tables
    /// reuses and a later delete or purge removes.
    pub fn create_backup(&mut self, db: &Db) -> Result<BackupId> {
        let id = self.next_backup_id()?;
        // A backup records when it was taken. Without a wall clock
        // there is no honest value to write, so the call fails here
        // rather than stamping every backup with the epoch.
        let created_at_unix = self.env.unix_secs().ok_or_else(|| {
            Error::invalid_argument("creating a backup needs a wall clock, and this Env has none")
        })?;
        // Resolved before the first copy, so a current key the provider
        // cannot provide refuses with nothing written, as the open does.
        let sealer = db
            .engine()
            .keyring()
            .map(|ring| ring.current())
            .transpose()
            .map_err(Error::from)?;

        // Take the snapshot in a limited scope so its held
        // compaction lock is released before we touch the backup
        // metadata directory. `checkpoint_capture` holds the
        // engine's compaction lock, which pins the captured file
        // set against concurrent unlink while we hash + copy.
        let (files, next_file_id, last_seq) = {
            let snapshot = db.engine().checkpoint_capture().map_err(Error::from)?;

            let mut files = Vec::new();
            for (level_idx, level) in snapshot.version.levels.iter().enumerate() {
                for file in level {
                    let src = snapshot
                        .sst_dir
                        .join(CheckpointSnapshot::sst_filename(file.meta.file_id));
                    let hash = hash_file(&*self.env, &src).map_err(Error::from)?;
                    let shared_name = shared_filename(hash);
                    let shared_path = self.shared_dir.join(&shared_name);
                    ensure_shared_file(&*self.env, &src, &shared_path, hash, file.meta.file_size)
                        .map_err(Error::from)?;
                    files.push(BackupFileEntry {
                        level: level_idx as u32,
                        file_id: file.meta.file_id,
                        file_size: file.meta.file_size,
                        hash,
                        smallest_key: file.meta.smallest_key.clone(),
                        largest_key: file.meta.largest_key.clone(),
                        num_entries: file.meta.num_entries,
                        global_seq: file.meta.global_seq,
                        seal_key: file.reader.seal_key(),
                    });
                }
            }
            (
                files,
                snapshot.version.next_file_id,
                snapshot.version.last_seq,
            )
            // snapshot drops here, releasing the compaction lock.
        };

        let manifest = BackupManifest {
            created_at_unix,
            files,
            next_file_id,
            last_seq,
            sealed_under: sealer.as_ref().map(|s| s.id()),
        };
        let bytes = format::encode(&manifest, id, sealer.as_ref()).map_err(Error::from)?;
        atomic_write(&*self.env, &self.meta_path(id), &bytes).map_err(Error::from)?;
        Ok(id)
    }

    /// Every backup in the repository, in id order (creation order), each
    /// exactly once: `Ok` with its summary when its metadata reads, `Err`
    /// with its id and the reason when it does not ([`UnreadableBackup`]).
    /// No backup is left out, so the list's length is the number of backups
    /// the repository holds, readable or not.
    ///
    /// A backup is a file in `meta/` named as [`BackupEngine::create_backup`]
    /// names one. Anything else there is not a backup: the staging file a
    /// backup cut short by a crash left, for one, never became one.
    ///
    /// Needs no key: a sealed backup keeps its listing readable, so a backup
    /// of an encrypted database lists as `Ok` without its provider. Reads
    /// every backup's metadata, one file at a time.
    ///
    /// # Errors
    ///
    /// Fails when the `meta/` directory itself cannot be read, since then
    /// no backup can be accounted for.
    pub fn list_backups(&self) -> Result<Vec<std::result::Result<BackupInfo, UnreadableBackup>>> {
        Ok(self
            .backup_ids()?
            .into_iter()
            .map(|id| {
                self.read_listing(id)
                    .and_then(|listing| summarize(id, &listing))
                    .map_err(|e| UnreadableBackup {
                        id,
                        reason: Error::from(e),
                    })
            })
            .collect())
    }

    /// Restore `backup_id` into `target_dir`. The target directory
    /// is created if it does not exist and must be empty (or
    /// contain only empty `sst/`/`wal/` subdirectories, or what an
    /// unfinished restore left). The resulting directory opens cleanly
    /// as a new [`Db`], with `key_provider` when one is given.
    ///
    /// A target that already holds a MANIFEST is a database, and refuses
    /// with [`Error::InvalidArgument`]: restoring over it would replace
    /// tables its MANIFEST still names.
    ///
    /// `key_provider` is the provider the restored database is to be opened
    /// with, and a backup of an encrypted database needs one:
    ///
    /// - without a provider, a sealed backup refuses with
    ///   [`Error::KeyProviderRequired`];
    /// - a key the backup's metadata or one of its tables names, or a
    ///   current key, that the provider does not provide refuses with
    ///   [`Error::UnknownKey`];
    /// - metadata that does not verify under the key it names (a wrong
    ///   key, or a changed or moved byte) refuses with
    ///   [`Error::Corruption`].
    ///
    /// Each of these refusals comes before anything is written: the target
    /// is left as it was. With a provider the MANIFEST the restore writes is
    /// sealed under the provider's current key, whatever key the backup was
    /// taken under; without one it is plaintext, as an unencrypted backup's
    /// metadata is.
    ///
    /// The MANIFEST is written last, once every table is durable in the
    /// target, so a restore that does not return `Ok` (an error, or a
    /// crash) leaves a directory that is not yet a database. Run the
    /// restore again into it before opening it.
    pub fn restore<P: AsRef<Path>>(
        &self,
        backup_id: BackupId,
        target_dir: P,
        key_provider: Option<Arc<dyn KeyProvider>>,
    ) -> Result<()> {
        let target_dir = target_dir.as_ref();
        let manifest_path = target_dir.join("MANIFEST");
        if self.env.exists(&manifest_path) {
            return Err(Error::invalid_argument(format!(
                "{} already holds a database; restore into an empty directory",
                target_dir.display()
            )));
        }
        let keyring = key_provider.map(|provider| Arc::new(Keyring::new(provider)));
        let manifest = self.read_manifest(backup_id, keyring.as_deref())?;
        // Every key the restored database needs, checked before the first
        // write as the open checks its own: the current key the MANIFEST is
        // sealed under, and the key each table names.
        if let Some(ring) = &keyring {
            ring.current().map_err(Error::from)?;
            for key in manifest.files.iter().filter_map(|f| f.seal_key) {
                ring.sealer(key).map_err(Error::from)?;
            }
        }

        let target_sst = target_dir.join("sst");
        let target_wal = target_dir.join("wal");
        self.env.create_dir_all(&target_sst).map_err(Error::from)?;
        self.env.create_dir_all(&target_wal).map_err(Error::from)?;
        crate::env::sync_parent_dir(&*self.env, target_dir).map_err(Error::from)?;
        self.env.sync_dir(target_dir).map_err(Error::from)?;
        self.env.sync_dir(&target_sst).map_err(Error::from)?;
        self.env.sync_dir(&target_wal).map_err(Error::from)?;

        for f in &manifest.files {
            let src = self.shared_dir.join(shared_filename(f.hash));
            verify_shared_file(&*self.env, &src, f.hash, f.file_size).map_err(Error::from)?;
            let dst = target_sst.join(CheckpointSnapshot::sst_filename(f.file_id));
            copy_file_atomic(&*self.env, &src, &dst).map_err(Error::from)?;
        }

        let manifest_bytes =
            encode_engine_manifest(&manifest, keyring.as_ref()).map_err(Error::from)?;
        atomic_write(&*self.env, &manifest_path, &manifest_bytes).map_err(Error::from)?;
        Ok(())
    }

    /// Delete `backup_id`, then remove every shared file no remaining backup
    /// lists.
    ///
    /// Needs no key, and nothing from the deleted backup's own metadata: a
    /// backup that cannot be read ([`UnreadableBackup`]) is deleted like any
    /// other, and the shared files only it listed go with it. Deleting a
    /// backup that is not there deletes nothing and still removes the
    /// shared files no backup lists, such as those a backup cut short by a
    /// crash copied and never listed.
    ///
    /// The deletion is durable before any shared file is removed, so a
    /// power cut never leaves a backup that lists a removed file.
    ///
    /// # Errors
    ///
    /// Every remaining backup's listing is read, sealed or not. When one
    /// cannot be read, `backup_id` is deleted all the same but no shared
    /// file is removed, since leaving that listing out could remove a file
    /// the backup needs; the error names that backup. Delete or repair it,
    /// and the next delete or purge removes them.
    pub fn delete_backup(&mut self, backup_id: BackupId) -> Result<()> {
        self.remove_backups(&[backup_id])?;
        self.collect_shared()
    }

    /// Delete every backup except the `keep` most recent, by id, then
    /// remove every shared file no remaining backup lists.
    ///
    /// Every backup counts, readable or not: one that cannot be read
    /// ([`UnreadableBackup`]) is deleted when it is among the oldest and
    /// kept when it is among the `keep` most recent, as
    /// [`BackupEngine::list_backups`] lists it. Needs no key.
    ///
    /// # Errors
    ///
    /// Fails before deleting anything when the `meta/` directory cannot be
    /// read. When a remaining backup cannot be read, the backups to delete
    /// are deleted all the same but no shared file is removed, as
    /// [`BackupEngine::delete_backup`] does, and the error names it.
    pub fn purge_old_backups(&mut self, keep: usize) -> Result<()> {
        let ids = self.backup_ids()?;
        self.remove_backups(&ids[..ids.len().saturating_sub(keep)])?;
        self.collect_shared()
    }

    /// Remove the metadata of every backup in `ids`, then sync `meta/`
    /// once, before any shared file is removed: a removal undone by a power
    /// cut must not bring back a backup listing a shared file that is gone.
    fn remove_backups(&self, ids: &[BackupId]) -> Result<()> {
        let mut removed = false;
        for &id in ids {
            match self.env.remove_file(&self.meta_path(id)) {
                Ok(()) => removed = true,
                Err(e) if e.kind() == io::ErrorKind::NotFound => {}
                Err(e) => return Err(Error::from(e)),
            }
        }
        if removed {
            self.env.sync_dir(&self.meta_dir).map_err(Error::from)?;
        }
        Ok(())
    }

    /// Remove every shared file no backup in the repository lists: those a
    /// deleted backup held, and those a backup cut short copied and never
    /// listed. Every backup counts, sealed or not, since each keeps its
    /// listing readable without a key; one whose listing cannot be read
    /// stops the collection before anything is removed, because leaving it
    /// out could remove a file it still needs. Only names the engine gives
    /// a shared table are considered; anything else in `shared/` stays.
    fn collect_shared(&self) -> Result<()> {
        let mut listed = HashSet::new();
        for id in self.backup_ids()? {
            let listing = self.read_listing(id).map_err(|e| {
                Error::from(io::Error::new(
                    e.kind(),
                    format!("backup {id} cannot be read, so no shared file was removed: {e}"),
                ))
            })?;
            listed.extend(listing.objects.into_iter().map(|(hash, _)| hash));
        }
        let mut removed = false;
        for entry in self.env.read_dir(&self.shared_dir).map_err(Error::from)? {
            let unlisted = parse_shared_filename(&entry.file_name())
                .is_some_and(|hash| !entry.is_dir && !listed.contains(&hash));
            if !unlisted {
                continue;
            }
            match self.env.remove_file(&entry.path) {
                Ok(()) => removed = true,
                Err(e) if e.kind() == io::ErrorKind::NotFound => {}
                Err(e) => return Err(Error::from(e)),
            }
        }
        // A removal a power cut undoes brings back a file no backup lists,
        // which the next collection removes; one sync covers the batch.
        if removed {
            self.env.sync_dir(&self.shared_dir).map_err(Error::from)?;
        }
        Ok(())
    }

    /// Every backup's id, in order: each file in `meta/` named as
    /// [`BackupEngine::create_backup`] names a backup's metadata.
    fn backup_ids(&self) -> Result<Vec<BackupId>> {
        let mut ids: Vec<BackupId> = self
            .env
            .read_dir(&self.meta_dir)
            .map_err(Error::from)?
            .iter()
            .filter_map(|entry| parse_backup_id(&entry.file_name()))
            .collect();
        ids.sort_unstable();
        Ok(ids)
    }

    fn meta_path(&self, id: BackupId) -> PathBuf {
        self.meta_dir.join(backup_filename(id))
    }

    fn read_manifest(&self, id: BackupId, keyring: Option<&Keyring>) -> Result<BackupManifest> {
        let bytes = self.env.read(&self.meta_path(id)).map_err(Error::from)?;
        format::decode(&bytes, id, keyring).map_err(Error::from)
    }

    fn read_listing(&self, id: BackupId) -> io::Result<Listing> {
        format::decode_listing(&self.env.read(&self.meta_path(id))?)
    }

    fn next_backup_id(&self) -> Result<BackupId> {
        let last = self.backup_ids()?.last().map_or(0, |id| id.0);
        last.checked_add(1).map(BackupId).ok_or_else(|| {
            Error::corruption(format!(
                "backup {last} has the largest id there is, so no backup can follow it"
            ))
        })
    }
}

/// What [`BackupEngine::list_backups`] reports for a backup whose listing
/// reads. A listing whose sizes add up past `u64` is damaged: no backup
/// holds that many bytes.
fn summarize(id: BackupId, listing: &Listing) -> io::Result<BackupInfo> {
    let bytes = listing
        .objects
        .iter()
        .try_fold(0u64, |sum, &(_, size)| sum.checked_add(size))
        .ok_or_else(|| invalid_data(format!("backup {id}: its tables' sizes overflow")))?;
    Ok(BackupInfo {
        id,
        created_at_unix: listing.created_at_unix,
        file_count: listing.objects.len(),
        bytes,
    })
}

fn hash_file(env: &dyn Env, path: &Path) -> io::Result<u128> {
    let file = env.open_read(path)?;
    let mut cursor = ReadFileCursor::new(&*file)?;
    checksum::backup_shared_file(&mut cursor)
}

fn ensure_shared_file(
    env: &dyn Env,
    src: &Path,
    dst: &Path,
    expected_hash: u128,
    expected_size: u64,
) -> io::Result<()> {
    match verify_shared_file(env, dst, expected_hash, expected_size) {
        Ok(()) => return Ok(()),
        Err(e) if e.kind() == io::ErrorKind::NotFound => {}
        Err(e) if e.kind() == io::ErrorKind::InvalidData => {
            if env.is_dir(dst) {
                return Err(e);
            }
        }
        Err(e) => return Err(e),
    }

    copy_file_atomic(env, src, dst)?;
    verify_shared_file(env, dst, expected_hash, expected_size)
}

fn verify_shared_file(
    env: &dyn Env,
    path: &Path,
    expected_hash: u128,
    expected_size: u64,
) -> io::Result<()> {
    let meta = env.metadata(path)?;
    if meta.is_dir {
        return Err(invalid_data(format!(
            "backup shared object {} is not a regular file",
            path.display()
        )));
    }
    if meta.len != expected_size {
        return Err(invalid_data(format!(
            "backup shared object {} has size {}, expected {expected_size}",
            path.display(),
            meta.len
        )));
    }
    let actual_hash = hash_file(env, path)?;
    if actual_hash != expected_hash {
        return Err(invalid_data(format!(
            "backup shared object {} content id mismatch",
            path.display()
        )));
    }
    Ok(())
}

fn copy_file_atomic(env: &dyn Env, src: &Path, dst: &Path) -> io::Result<()> {
    let tmp = dst.with_extension("tmp");
    {
        let input = env.open_read(src)?;
        let mut output = env.open_write(&tmp, WriteMode::Truncate)?;
        // A fixed 64 KiB window, so a multi-gigabyte SSTable costs one
        // buffer rather than its own size in memory.
        let mut buf = vec![0u8; 64 * 1024];
        let mut offset = 0u64;
        let len = input.len()?;
        while offset < len {
            let want = (len - offset).min(buf.len() as u64) as usize;
            input.read_exact_at(offset, &mut buf[..want])?;
            output.write_all(&buf[..want])?;
            offset += want as u64;
        }
        output.sync_all()?;
    }
    env.rename(&tmp, dst)?;
    crate::env::sync_parent_dir(env, dst)?;
    Ok(())
}

fn atomic_write(env: &dyn Env, path: &Path, bytes: &[u8]) -> io::Result<()> {
    let tmp = path.with_extension("tmp");
    {
        let mut f = env.open_write(&tmp, WriteMode::Truncate)?;
        f.write_all(bytes)?;
        f.sync_all()?;
    }
    env.rename(&tmp, path)?;
    crate::env::sync_parent_dir(env, path)?;
    Ok(())
}

fn invalid_data(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}

fn shared_filename(hash: u128) -> String {
    format!("{:032x}.sst", hash)
}

fn backup_filename(id: BackupId) -> String {
    format!("{:06}.backup", id.0)
}

/// The content id a shared table's file name carries. Only the name
/// [`shared_filename`] writes parses, so a name and a content id map one to
/// one.
fn parse_shared_filename(name: &str) -> Option<u128> {
    let hash = u128::from_str_radix(name.strip_suffix(".sst")?, 16).ok()?;
    (shared_filename(hash) == name).then_some(hash)
}

/// The backup id a metadata file's name carries. Only the name
/// [`backup_filename`] writes parses: `7.backup` or `+7.backup` would name
/// a file the engine reads as `000007.backup`, a different file.
fn parse_backup_id(name: &str) -> Option<BackupId> {
    let id = BackupId(name.strip_suffix(".backup")?.parse::<u64>().ok()?);
    (backup_filename(id) == name).then_some(id)
}

/// Encode a restored backup as an engine MANIFEST, through the engine's own
/// encoder so a restored manifest cannot drift from the one it writes:
/// sealed under the keyring's current key when there is one.
///
/// Every write the backup holds is in its tables, so `min_wal_id` is the
/// backup's next file id: no log numbered below it is ever replayed into the
/// restored database, whatever the target's `wal/` holds (E30).
fn encode_engine_manifest(
    m: &BackupManifest,
    keyring: Option<&Arc<Keyring>>,
) -> io::Result<Vec<u8>> {
    crate::engine::manifest::encode_manifest_image(
        m.next_file_id,
        m.last_seq,
        m.next_file_id,
        m.files.iter().map(|f| {
            (
                f.level as usize,
                crate::engine::sstable::SsTableMeta {
                    file_id: f.file_id,
                    smallest_key: f.smallest_key.clone(),
                    largest_key: f.largest_key.clone(),
                    file_size: f.file_size,
                    num_entries: f.num_entries,
                    global_seq: f.global_seq,
                },
            )
        }),
        keyring,
    )
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod unreadable_tests;
