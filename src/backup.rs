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

/// Content-addressed backup repository for one or more databases.
///
/// Multiple [`BackupEngine`] instances should not share a backup
/// directory - there is no cross-process locking. A single process
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
    /// reuses.
    pub fn create_backup(&mut self, db: &Db) -> Result<BackupId> {
        let id = BackupId(self.next_backup_id()?);
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
        let manifest_path = self.meta_dir.join(backup_filename(id.0));
        atomic_write(&*self.env, &manifest_path, &bytes).map_err(Error::from)?;
        Ok(id)
    }

    /// Return a summary of every backup currently stored. Ordered
    /// by backup id (creation order).
    ///
    /// Needs no key: a sealed backup keeps its listing readable. A backup
    /// whose metadata cannot be read is left out.
    pub fn list_backups(&self) -> Vec<BackupInfo> {
        let mut out = Vec::new();
        let Ok(entries) = self.env.read_dir(&self.meta_dir) else {
            return out;
        };
        let mut ids: Vec<u64> = entries
            .iter()
            .filter_map(|e| parse_backup_id(&e.file_name()))
            .collect();
        ids.sort_unstable();
        for id in ids {
            let path = self.meta_dir.join(backup_filename(id));
            let Ok(bytes) = self.env.read(&path) else {
                continue;
            };
            let Ok(listing) = format::decode_listing(&bytes) else {
                continue;
            };
            out.push(BackupInfo {
                id: BackupId(id),
                created_at_unix: listing.created_at_unix,
                file_count: listing.objects.len(),
                bytes: listing.objects.iter().map(|&(_, size)| size).sum(),
            });
        }
        out
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

    /// Delete `backup_id`. Shared files whose reference count drops
    /// to zero are removed from disk.
    ///
    /// Needs no key. A shared file is removed only when every other
    /// backup's metadata was read and none lists it: when one cannot be
    /// read this fails, the backup gone and every shared file kept.
    pub fn delete_backup(&mut self, backup_id: BackupId) -> Result<()> {
        let path = self.meta_dir.join(backup_filename(backup_id.0));
        if !self.env.exists(&path) {
            return Ok(());
        }
        let listing = self.read_listing(backup_id)?;
        crate::env::remove_file_and_sync_parent(&*self.env, &path).map_err(Error::from)?;
        self.gc_shared(&listing)?;
        Ok(())
    }

    /// Delete every backup except the `keep` most recent.
    pub fn purge_old_backups(&mut self, keep: usize) -> Result<()> {
        let infos = self.list_backups();
        if infos.len() <= keep {
            return Ok(());
        }
        let to_remove = infos.len() - keep;
        for info in infos.into_iter().take(to_remove) {
            self.delete_backup(info.id)?;
        }
        Ok(())
    }

    /// Remove the shared files `removed` listed that no remaining backup
    /// lists. Every remaining backup counts, sealed or not, since each
    /// keeps its listing readable without a key; one whose listing cannot
    /// be read stops the collection before anything is removed, because
    /// leaving it out could remove a file it still needs.
    fn gc_shared(&self, removed: &Listing) -> Result<()> {
        let mut still_referenced = HashSet::new();
        for entry in self.env.read_dir(&self.meta_dir).map_err(Error::from)? {
            let Some(id) = parse_backup_id(&entry.file_name()) else {
                continue;
            };
            let listing = self
                .env
                .read(&entry.path)
                .and_then(|bytes| format::decode_listing(&bytes))
                .map_err(|e| {
                    io::Error::new(
                        e.kind(),
                        format!("backup {id} cannot be read, so no shared file was removed: {e}"),
                    )
                })?;
            still_referenced.extend(listing.objects.into_iter().map(|(hash, _)| hash));
        }
        for &(hash, _) in &removed.objects {
            if !still_referenced.contains(&hash) {
                let p = self.shared_dir.join(shared_filename(hash));
                match crate::env::remove_file_and_sync_parent(&*self.env, &p) {
                    Ok(()) => {}
                    Err(e) if e.kind() == io::ErrorKind::NotFound => {}
                    Err(e) => return Err(Error::from(e)),
                }
            }
        }
        Ok(())
    }

    fn read_manifest(&self, id: BackupId, keyring: Option<&Keyring>) -> Result<BackupManifest> {
        let path = self.meta_dir.join(backup_filename(id.0));
        let bytes = self.env.read(&path).map_err(Error::from)?;
        format::decode(&bytes, id, keyring).map_err(Error::from)
    }

    fn read_listing(&self, id: BackupId) -> Result<Listing> {
        let path = self.meta_dir.join(backup_filename(id.0));
        let bytes = self.env.read(&path).map_err(Error::from)?;
        format::decode_listing(&bytes).map_err(Error::from)
    }

    fn next_backup_id(&self) -> Result<u64> {
        let mut max_id = 0u64;
        for entry in self.env.read_dir(&self.meta_dir).map_err(Error::from)? {
            if let Some(id) = parse_backup_id(&entry.file_name())
                && id > max_id
            {
                max_id = id;
            }
        }
        Ok(max_id + 1)
    }
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

fn backup_filename(id: u64) -> String {
    format!("{:06}.backup", id)
}

fn parse_backup_id(name: &str) -> Option<u64> {
    let stem = name.strip_suffix(".backup")?;
    stem.parse::<u64>().ok()
}

/// Encode a restored backup as an engine MANIFEST, through the engine's own
/// encoder so a restored manifest cannot drift from the one it writes:
/// sealed under the keyring's current key when there is one.
fn encode_engine_manifest(
    m: &BackupManifest,
    keyring: Option<&Arc<Keyring>>,
) -> io::Result<Vec<u8>> {
    crate::engine::manifest::encode_manifest_image(
        m.next_file_id,
        m.last_seq,
        0,
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
