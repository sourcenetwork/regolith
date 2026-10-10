//! Bound how many SSTables hold an open file descriptor.
//!
//! A reader keeps its table's file open for as long as the table is
//! live, so a store needs one descriptor per live table. A large store,
//! or a process started with a low `RLIMIT_NOFILE` (256 under macOS
//! launchd), runs out, and every compaction then fails with EMFILE.
//!
//! [`OpenFileLimit`] wraps an [`Env`] and hands out SSTable files whose
//! descriptor it may close when more than `capacity` are open, reopening
//! on the next read. Eviction is CLOCK: a read sets a per-file bit without
//! taking any shared lock, and the sweep that runs when a descriptor is
//! opened skips a file whose bit is set (clearing it) and closes the first
//! that has none. Only SSTables are managed; every other file passes
//! through.
//!
//! # Deleted tables
//!
//! Compaction unlinks a table as soon as no current version names it, and
//! relies on open descriptors to keep it readable for older snapshots and
//! iterators. A descriptor this wrapper had closed could not be reopened
//! after the unlink, so [`Env::remove_file`] on a table that still has a
//! live handle first reopens that handle if needed and pins it: a pinned
//! descriptor is never evicted, and closes when the handle drops.
//!
//! The cap is soft. Pinned descriptors and reads in flight on an evicted
//! one can push the count past it briefly.

use std::io;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Weak};

use super::{
    Capabilities, DirEntry, Env, FileLock, FileMeta, JoinHandle, ReadFile, WriteFile, WriteMode,
};
use crate::portability::{AtomicBool, AtomicUsize, Ordering};
use crate::sync::internal::Mutex;

#[derive(Debug)]
pub(crate) struct OpenFileLimit {
    shared: Arc<Shared>,
}

#[derive(Debug)]
struct Shared {
    inner: Arc<dyn Env>,
    capacity: usize,
    open: AtomicUsize,
    clock: Mutex<Clock>,
}

#[derive(Debug, Default)]
struct Clock {
    slots: Vec<Weak<Slot>>,
    hand: usize,
    /// Prune retired slots once `slots` reaches this length. Without it a
    /// store that never exceeds the limit (so never sweeps) keeps a weak
    /// entry for every table it ever opened, and `remove_file` scans them
    /// all. Doubling keeps pruning amortized O(1) per open.
    prune_at: usize,
}

impl Clock {
    fn push(&mut self, slot: &Arc<Slot>) {
        self.slots.push(Arc::downgrade(slot));
        if self.slots.len() >= self.prune_at {
            self.slots.retain(|w| w.strong_count() > 0);
            self.hand = 0;
            self.prune_at = (2 * self.slots.len()).max(MIN_PRUNE_AT);
        }
    }
}

/// Slots below which pruning is not worth a pass.
const MIN_PRUNE_AT: usize = 64;

struct Slot {
    path: PathBuf,
    len: u64,
    file: Mutex<Option<Arc<dyn ReadFile>>>,
    referenced: AtomicBool,
    pinned: AtomicBool,
    shared: Arc<Shared>,
}

impl std::fmt::Debug for Slot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Slot")
            .field("path", &self.path)
            .finish_non_exhaustive()
    }
}

fn is_table(path: &Path) -> bool {
    path.extension().is_some_and(|ext| ext == "sst")
}

impl OpenFileLimit {
    pub(crate) fn new(inner: Arc<dyn Env>, capacity: usize) -> Self {
        Self {
            shared: Arc::new(Shared {
                inner,
                capacity: capacity.max(1),
                open: AtomicUsize::new(0),
                clock: Mutex::new(Clock::default()),
            }),
        }
    }

    /// SSTable descriptors currently open through this wrapper.
    #[cfg(test)]
    fn open_count(&self) -> usize {
        self.shared.open.load(Ordering::Relaxed)
    }
}

impl Shared {
    /// Close unreferenced descriptors until the count is within capacity,
    /// sparing `keep`. Gives up after two passes, so pinned and busy files
    /// can leave it over: the cap is soft.
    fn make_room(&self, keep: &Slot) {
        if self.open.load(Ordering::Relaxed) <= self.capacity {
            return;
        }
        let mut clock = self.clock.lock();
        clock.slots.retain(|w| w.strong_count() > 0);
        let len = clock.slots.len();
        let mut steps = 0;
        while self.open.load(Ordering::Relaxed) > self.capacity && steps < 2 * len {
            if clock.hand >= clock.slots.len() {
                clock.hand = 0;
            }
            let candidate = clock.slots[clock.hand].upgrade();
            clock.hand += 1;
            steps += 1;
            let Some(slot) = candidate else { continue };
            if std::ptr::eq(&*slot, keep)
                || slot.pinned.load(Ordering::Acquire)
                || slot.referenced.swap(false, Ordering::AcqRel)
            {
                continue;
            }
            // `try_lock`: a slot whose lock is held is mid-open or
            // mid-read; skip it rather than wait while holding the clock.
            if let Some(mut file) = slot.file.try_lock()
                && file.take().is_some()
            {
                self.open.fetch_sub(1, Ordering::Relaxed);
            }
        }
    }
}

impl Slot {
    fn handle(&self) -> io::Result<Arc<dyn ReadFile>> {
        let mut file = self.file.lock();
        if let Some(f) = &*file {
            return Ok(Arc::clone(f));
        }
        let opened: Arc<dyn ReadFile> = Arc::from(self.shared.inner.open_read(&self.path)?);
        self.shared.open.fetch_add(1, Ordering::Relaxed);
        *file = Some(Arc::clone(&opened));
        drop(file);
        self.shared.make_room(self);
        Ok(opened)
    }
}

impl Drop for Slot {
    fn drop(&mut self) {
        if self.file.get_mut().take().is_some() {
            self.shared.open.fetch_sub(1, Ordering::Relaxed);
        }
    }
}

/// The handle an SSTable reader holds in place of its file.
struct LimitedFile(Arc<Slot>);

impl ReadFile for LimitedFile {
    fn read_exact_at(&self, offset: u64, buf: &mut [u8]) -> io::Result<()> {
        let file = self.0.handle()?;
        self.0.referenced.store(true, Ordering::Release);
        file.read_exact_at(offset, buf)
    }

    fn len(&self) -> io::Result<u64> {
        Ok(self.0.len)
    }
}

impl Env for OpenFileLimit {
    fn open_read(&self, path: &Path) -> io::Result<Box<dyn ReadFile>> {
        if !is_table(path) {
            return self.shared.inner.open_read(path);
        }
        let file: Arc<dyn ReadFile> = Arc::from(self.shared.inner.open_read(path)?);
        let slot = Arc::new(Slot {
            path: path.to_path_buf(),
            len: file.len()?,
            file: Mutex::new(Some(file)),
            referenced: AtomicBool::new(true),
            pinned: AtomicBool::new(false),
            shared: Arc::clone(&self.shared),
        });
        self.shared.open.fetch_add(1, Ordering::Relaxed);
        self.shared.clock.lock().push(&slot);
        self.shared.make_room(&slot);
        Ok(Box::new(LimitedFile(slot)))
    }

    fn remove_file(&self, path: &Path) -> io::Result<()> {
        if is_table(path) {
            let live: Vec<Arc<Slot>> = self
                .shared
                .clock
                .lock()
                .slots
                .iter()
                .filter_map(Weak::upgrade)
                .filter(|slot| slot.path == path)
                .collect();
            for slot in live {
                slot.pinned.store(true, Ordering::Release);
                // Reopen before the unlink, while the name still resolves.
                slot.handle()?;
            }
        }
        self.shared.inner.remove_file(path)
    }

    fn create_dir_all(&self, path: &Path) -> io::Result<()> {
        self.shared.inner.create_dir_all(path)
    }
    fn read_dir(&self, path: &Path) -> io::Result<Vec<DirEntry>> {
        self.shared.inner.read_dir(path)
    }
    fn open_write(&self, path: &Path, mode: WriteMode) -> io::Result<Box<dyn WriteFile>> {
        self.shared.inner.open_write(path, mode)
    }
    fn metadata(&self, path: &Path) -> io::Result<FileMeta> {
        self.shared.inner.metadata(path)
    }
    fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        self.shared.inner.rename(from, to)
    }
    fn hard_link(&self, src: &Path, dst: &Path) -> io::Result<()> {
        self.shared.inner.hard_link(src, dst)
    }
    fn sync_dir(&self, path: &Path) -> io::Result<()> {
        self.shared.inner.sync_dir(path)
    }
    fn lock_file(&self, path: &Path, exclusive: bool) -> io::Result<Box<dyn FileLock>> {
        self.shared.inner.lock_file(path, exclusive)
    }
    fn capabilities(&self) -> Capabilities {
        self.shared.inner.capabilities()
    }
    fn now_micros(&self) -> Option<u64> {
        self.shared.inner.now_micros()
    }
    fn unix_secs(&self) -> Option<u64> {
        self.shared.inner.unix_secs()
    }
    fn spawn(
        &self,
        name: &str,
        body: Box<dyn FnOnce() + Send + 'static>,
    ) -> io::Result<Box<dyn JoinHandle>> {
        self.shared.inner.spawn(name, body)
    }
    fn drop_page_cache(&self, path: &Path) {
        self.shared.inner.drop_page_cache(path)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::std_env;

    fn write_tables(dir: &Path, n: usize) -> Vec<PathBuf> {
        (0..n)
            .map(|i| {
                let path = dir.join(format!("{i:06}.sst"));
                std::fs::write(&path, format!("table {i}").repeat(4)).unwrap();
                path
            })
            .collect()
    }

    fn read_all(file: &dyn ReadFile) -> Vec<u8> {
        let mut buf = vec![0u8; file.len().unwrap() as usize];
        file.read_exact_at(0, &mut buf).unwrap();
        buf
    }

    #[test]
    fn keeps_open_descriptors_near_capacity_and_reopens_on_read() {
        let dir = tempfile::tempdir().unwrap();
        let paths = write_tables(dir.path(), 10);
        let env = OpenFileLimit::new(std_env(), 3);
        let files: Vec<_> = paths.iter().map(|p| env.open_read(p).unwrap()).collect();
        assert!(env.open_count() <= 3, "{} open", env.open_count());

        for _ in 0..3 {
            for (i, file) in files.iter().enumerate() {
                assert_eq!(
                    read_all(&**file),
                    format!("table {i}").repeat(4).into_bytes()
                );
                assert!(env.open_count() <= 4, "{} open", env.open_count());
            }
        }
        drop(files);
        assert_eq!(env.open_count(), 0);
    }

    #[test]
    fn retired_slots_are_pruned_without_descriptor_pressure() {
        let dir = tempfile::tempdir().unwrap();
        let paths = write_tables(dir.path(), 1);
        // A limit that is never reached, so the eviction sweep never runs.
        let env = OpenFileLimit::new(std_env(), 1_000_000);
        for _ in 0..10_000 {
            drop(env.open_read(&paths[0]).unwrap());
        }
        let tracked = env.shared.clock.lock().slots.len();
        assert!(
            tracked <= 2 * MIN_PRUNE_AT,
            "{tracked} slots tracked for one live file"
        );
        assert_eq!(env.open_count(), 0);
    }

    #[test]
    fn files_that_are_not_tables_pass_through_unmanaged() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("MANIFEST");
        std::fs::write(&path, b"m").unwrap();
        let env = OpenFileLimit::new(std_env(), 1);
        let _file = env.open_read(&path).unwrap();
        assert_eq!(env.open_count(), 0);
    }

    #[cfg(unix)]
    #[test]
    fn a_table_removed_while_a_handle_lives_stays_readable() {
        let dir = tempfile::tempdir().unwrap();
        let paths = write_tables(dir.path(), 3);
        let env = OpenFileLimit::new(std_env(), 1);
        let first = env.open_read(&paths[0]).unwrap();
        // Opening the others evicts the first table's descriptor.
        let _rest: Vec<_> = paths[1..]
            .iter()
            .map(|p| env.open_read(p).unwrap())
            .collect();

        env.remove_file(&paths[0]).unwrap();
        assert!(!paths[0].exists());
        assert_eq!(read_all(&*first), b"table 0".repeat(4));

        // Pinned: more opens never close it again.
        let _more: Vec<_> = paths[1..]
            .iter()
            .map(|p| env.open_read(p).unwrap())
            .collect();
        assert_eq!(read_all(&*first), b"table 0".repeat(4));
    }
}
