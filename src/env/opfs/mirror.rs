//! Mirror mode: the database resident in linear memory, written back to
//! OPFS whole-file.
//!
//! It exists because `createSyncAccessHandle` is worker-only, so a
//! database opened on the main thread has no synchronous path to storage
//! at all. `FileSystemWritableFileStream` is asynchronous but available
//! everywhere, so the engine runs against RAM and
//! [`super::OpfsEnv::persist`] pushes dirty files out.
//!
//! Two ceilings follow, and both are reported rather than hidden. The
//! whole database is resident, so [`super::OpfsOptions::max_resident_bytes`]
//! fails a write loudly instead of growing linear memory until the tab
//! dies (wasm pages are never returned to the host). And nothing is
//! durable until `persist()` resolves, so
//! [`crate::env::Capabilities::durable_sync`] is `false` here.
//!
//! # Physical naming
//!
//! OPFS directories are flat for regolith's purposes, so a logical path is
//! escaped into one filename: `%` becomes `%25`, then `/` becomes `%2F`
//! and `\` becomes `%5C`. Every mirror file carries the `.regolith-file-`
//! prefix so a mirror database and a slot pool can share one directory.

use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use kovan_map::HashMap;

use crate::env::mem_file::{Charge, MemFile};
use crate::env::persist_order::persist_rank;
use crate::portability::{AtomicU64, AtomicUsize, Ordering};
use wasm_bindgen::JsValue;

use super::js;

const FILE_PREFIX: &str = ".regolith-file-";

/// Buckets each map starts with; they grow on demand.
const BUCKETS: usize = 64;

/// Escape a logical path into a single OPFS entry name.
fn encode_name(path: &Path) -> String {
    let mut out = String::from(FILE_PREFIX);
    for ch in path.to_string_lossy().chars() {
        match ch {
            '%' => out.push_str("%25"),
            '/' => out.push_str("%2F"),
            '\\' => out.push_str("%5C"),
            other => out.push(other),
        }
    }
    out
}

/// Reverse [`encode_name`]. Returns `None` for an entry that is not a
/// mirror file or whose escapes are malformed.
fn decode_name(name: &str) -> Option<PathBuf> {
    let body = name.strip_prefix(FILE_PREFIX)?;
    let bytes = body.as_bytes();
    let mut out = String::with_capacity(body.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' {
            let code = body.get(i + 1..i + 3)?;
            match code {
                "25" => out.push('%'),
                "2F" => out.push('/'),
                "5C" => out.push('\\'),
                _ => return None,
            }
            i += 3;
        } else {
            let ch = body[i..].chars().next()?;
            out.push(ch);
            i += ch.len_utf8();
        }
    }
    Some(PathBuf::from(out))
}

/// One dirty file as `persist` will write it: the logical path, the
/// version that made it dirty, and the bytes to send.
type PendingWrite = (PathBuf, u64, Vec<u8>);

/// One mirrored file: its bytes, read without a lock, and the versions
/// that say whether `persist` still owes it a write.
struct Entry {
    data: MemFile,
    /// The version of the last mutation: every mutation takes a fresh one
    /// from [`MirrorFs::next_version`].
    version: AtomicU64,
    /// The newest version `persist` wrote out. The file is dirty while
    /// `version` is above it, so a mutation that lands during a persist's
    /// await keeps it dirty.
    persisted: AtomicU64,
}

impl Entry {
    fn new(data: MemFile, version: u64, persisted: u64) -> Arc<Self> {
        Arc::new(Self {
            data,
            version: AtomicU64::new(version),
            persisted: AtomicU64::new(persisted),
        })
    }

    fn touch(&self, version: u64) {
        self.version.fetch_max(version, Ordering::AcqRel);
    }

    fn is_dirty(&self) -> bool {
        self.version.load(Ordering::Acquire) > self.persisted.load(Ordering::Acquire)
    }
}

/// The in-memory mirror of an OPFS-backed database.
///
/// Every map is a lock-free kovan map and every file a lock-free
/// `MemFile`, so no call takes a lock. A browser module runs this on one
/// thread, where the persist's `await`s are the only interleaving; the
/// atomics keep it correct beyond that too.
pub(super) struct MirrorFs {
    files: HashMap<PathBuf, Arc<Entry>>,
    dirs: HashMap<PathBuf, ()>,
    /// Paths removed since the last persist, whose OPFS entries persist
    /// deletes after it writes the batch.
    deleted: HashMap<PathBuf, ()>,
    resident: Resident,
    next_version: AtomicU64,
    mount: super::sah::MountId,
}

/// The bytes the mirror holds, bounded by `max`.
struct Resident {
    bytes: AtomicUsize,
    max: usize,
}

impl Resident {
    fn quota_error(&self, want: usize) -> io::Error {
        io::Error::other(format!(
            "OPFS mirror mode holds the whole database in memory and this write \
             would reach {want} bytes, over the {} byte limit; raise \
             OpfsOptions::max_resident_bytes or open the database in a worker, \
             where OpfsMode::Sah streams to storage instead",
            self.max
        ))
    }
}

impl Charge for Resident {
    fn reserve(&self, bytes: u64) -> io::Result<()> {
        let bytes = usize::try_from(bytes).unwrap_or(usize::MAX);
        self.bytes
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |held| {
                held.checked_add(bytes).filter(|want| *want <= self.max)
            })
            .map(|_| ())
            .map_err(|held| self.quota_error(held.saturating_add(bytes)))
    }

    fn release(&self, bytes: u64) {
        let bytes = usize::try_from(bytes).unwrap_or(usize::MAX);
        let _ = self
            .bytes
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |held| {
                Some(held.saturating_sub(bytes))
            });
    }
}

impl Drop for MirrorFs {
    fn drop(&mut self) {
        super::sah::release_mount(self.mount);
    }
}

impl std::fmt::Debug for MirrorFs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MirrorFs")
            .field("files", &self.files.len())
            .field("resident_bytes", &self.resident_bytes())
            .field("max_resident_bytes", &self.resident.max)
            .finish()
    }
}

fn removed_while_open() -> io::Error {
    io::Error::new(io::ErrorKind::NotFound, "file was removed while open")
}

impl MirrorFs {
    /// Build a mirror from files already read out of OPFS.
    pub(super) fn new(
        mount: super::sah::MountId,
        loaded: Vec<(PathBuf, Vec<u8>)>,
        max_resident: usize,
    ) -> Self {
        let fs = Self {
            files: HashMap::with_capacity(BUCKETS.max(loaded.len())),
            dirs: HashMap::with_capacity(BUCKETS),
            deleted: HashMap::with_capacity(BUCKETS),
            resident: Resident {
                bytes: AtomicUsize::new(0),
                max: max_resident,
            },
            next_version: AtomicU64::new(1),
            mount,
        };
        for (path, data) in loaded {
            fs.resident.bytes.fetch_add(data.len(), Ordering::Relaxed);
            super::register_ancestors(&fs.dirs, &path);
            // Loaded from storage: persisted as it is.
            fs.files
                .insert(path, Entry::new(MemFile::from_vec(data), 0, 0));
        }
        fs
    }

    /// Read every mirror file out of an OPFS directory.
    pub(super) async fn load(directory: &JsValue) -> Result<Vec<(PathBuf, Vec<u8>)>, JsValue> {
        let entries = js::list_files(directory).await?;
        let mut loaded = Vec::new();
        for (name, handle) in entries {
            let Some(path) = decode_name(&name) else {
                continue;
            };
            loaded.push((path, js::read_whole_file(&handle).await?));
        }
        Ok(loaded)
    }

    pub(super) fn resident_bytes(&self) -> usize {
        self.resident.bytes.load(Ordering::Acquire)
    }

    pub(super) fn pending_bytes(&self) -> usize {
        self.files
            .values()
            .filter(|entry| entry.is_dirty())
            .map(|entry| entry.data.len() as usize)
            .sum()
    }

    fn version(&self) -> u64 {
        self.next_version.fetch_add(1, Ordering::AcqRel)
    }

    /// Snapshot the work `persist` has to do; nothing is held across any
    /// `await`. The writes come tables first and the MANIFEST last
    /// (`persist_order`, E20), and `persist` deletes only after writing, so
    /// a batch cut short never leaves a manifest naming a table it lost.
    fn take_persist_batch(&self) -> (Vec<PendingWrite>, Vec<PathBuf>) {
        let mut writes: Vec<PendingWrite> = self
            .files
            .iter()
            .filter(|(_, entry)| entry.is_dirty())
            .map(|(path, entry)| {
                // The version before the bytes: a mutation between the two
                // makes the bytes newer than the version, never older, so
                // the file stays dirty and is written again.
                let version = entry.version.load(Ordering::Acquire);
                (path, version, entry.data.to_vec())
            })
            .collect();
        writes.sort_by_key(|(path, _, _)| persist_rank(path));
        let deletes = self.deleted.keys().collect();
        (writes, deletes)
    }

    /// Record what `persist` actually wrote out. A file mutated while the
    /// write was in flight has a newer version and stays dirty.
    fn settle(&self, written: &[(PathBuf, u64)], deleted: &[PathBuf]) {
        for (path, version) in written {
            if let Some(entry) = self.files.get(path) {
                entry.persisted.fetch_max(*version, Ordering::AcqRel);
            }
        }
        for path in deleted {
            self.deleted.remove(path);
        }
    }

    /// Write every dirty file back to OPFS, tables first and the MANIFEST
    /// last, then drop the deleted ones.
    pub(super) async fn persist(&self) -> Result<(), JsValue> {
        let (writes, deletes) = self.take_persist_batch();
        if writes.is_empty() && deletes.is_empty() {
            return Ok(());
        }
        let directory = super::sah::mount_directory(self.mount)
            .map_err(|e| JsValue::from_str(&e.to_string()))?;

        let mut written = Vec::with_capacity(writes.len());
        for (path, version, data) in &writes {
            js::write_whole_file(&directory, &encode_name(path), data).await?;
            written.push((path.clone(), *version));
        }
        for path in &deletes {
            // A file deleted before it was ever persisted has no OPFS
            // entry; that is not an error.
            let _ = js::remove_entry(&directory, &encode_name(path)).await;
        }

        self.settle(&written, &deletes);
        Ok(())
    }

    fn entry(&self, path: &Path) -> io::Result<Arc<Entry>> {
        self.files.get(path).ok_or_else(removed_while_open)
    }

    pub(super) fn write_at(&self, path: &Path, at: u64, buf: &[u8]) -> io::Result<()> {
        let entry = self.entry(path)?;
        let version = self.version();
        entry.data.write_at(at, buf, &self.resident)?;
        entry.touch(version);
        Ok(())
    }

    pub(super) fn read_at(&self, path: &Path, at: u64, buf: &mut [u8]) -> io::Result<usize> {
        Ok(self.entry(path)?.data.read_at(at, buf))
    }

    pub(super) fn file_len(&self, path: &Path) -> io::Result<u64> {
        Ok(self.entry(path)?.data.len())
    }

    pub(super) fn set_len(&self, path: &Path, len: u64) -> io::Result<()> {
        let entry = self.entry(path)?;
        let version = self.version();
        entry.data.set_len(len, &self.resident)?;
        entry.touch(version);
        Ok(())
    }

    /// Create the file when absent, optionally emptying it first.
    /// Returns the resulting length.
    pub(super) fn create(&self, path: &Path, truncate: bool) -> io::Result<u64> {
        let version = self.version();
        let entry = match self.files.get(path) {
            Some(entry) => entry,
            None => self
                .files
                .get_or_insert(path.to_path_buf(), Entry::new(MemFile::new(), version, 0)),
        };
        if truncate {
            entry.data.set_len(0, &self.resident)?;
        }
        entry.touch(version);
        self.deleted.remove(path);
        super::register_ancestors(&self.dirs, path);
        Ok(entry.data.len())
    }

    pub(super) fn create_dir_all(&self, path: &Path) -> io::Result<()> {
        self.dirs.insert(path.to_path_buf(), ());
        super::register_ancestors(&self.dirs, path);
        Ok(())
    }

    pub(super) fn exists(&self, path: &Path) -> bool {
        self.files.contains_key(path) || self.dirs.contains_key(path)
    }

    pub(super) fn metadata(&self, path: &Path) -> io::Result<(u64, bool)> {
        if let Some(entry) = self.files.get(path) {
            return Ok((entry.data.len(), false));
        }
        if self.dirs.contains_key(path) {
            return Ok((0, true));
        }
        Err(super::not_found(path))
    }

    pub(super) fn read_dir(&self, path: &Path) -> io::Result<Vec<(PathBuf, bool)>> {
        if !self.dirs.contains_key(path) {
            return Err(super::not_found(path));
        }
        Ok(super::children(path, self.files.keys(), self.dirs.keys()))
    }

    pub(super) fn remove_file(&self, path: &Path) -> io::Result<()> {
        let entry = self
            .files
            .remove(path)
            .ok_or_else(|| super::not_found(path))?;
        self.resident.release(entry.data.len());
        self.deleted.insert(path.to_path_buf(), ());
        Ok(())
    }

    pub(super) fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        if from == to {
            return self.entry(from).map(|_| ());
        }
        let entry = self
            .files
            .remove(from)
            .ok_or_else(|| super::not_found(from))?;
        entry.touch(self.version());
        if let Some(replaced) = self.files.insert(to.to_path_buf(), entry) {
            self.resident.release(replaced.data.len());
        }
        self.deleted.insert(from.to_path_buf(), ());
        self.deleted.remove(to);
        super::register_ancestors(&self.dirs, to);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use wasm_bindgen_test::wasm_bindgen_test;

    #[wasm_bindgen_test]
    fn names_round_trip_through_the_escape() {
        for original in ["db/MANIFEST", "db/sst/000001.sst", "a%b/c\\d", "plain"] {
            let encoded = encode_name(Path::new(original));
            assert!(encoded.starts_with(FILE_PREFIX));
            assert!(!encoded[FILE_PREFIX.len()..].contains('/'));
            assert_eq!(decode_name(&encoded), Some(PathBuf::from(original)));
        }
    }

    #[wasm_bindgen_test]
    fn a_foreign_entry_is_not_decoded() {
        assert_eq!(decode_name(".regolith-sah-0000"), None);
        assert_eq!(decode_name("something-else"), None);
    }
}
