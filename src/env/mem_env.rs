//! An entirely in-memory [`Env`].
//!
//! [`MemEnv`] exists to prove the seam. Every pre-existing test runs
//! through [`super::StdEnv`], so a leftover `std::fs` call inside the
//! engine would still pass; the same lifecycle run against `MemEnv`
//! fails loudly instead, because there is no filesystem behind it at
//! all.
//!
//! It is also the honest way to test the paths regolith takes when the
//! host is missing a capability: `MemEnv` has no hard links, no
//! directory fsync, and no threads, and it says so through
//! [`super::Capabilities`].
//!
//! # Shape
//!
//! Two lock-free maps (kovan): path to file, and the set of directories.
//! A file is a `MemFile` behind an `Arc`, so a reader and a writer hold
//! the same file without touching either map, and every read is a copy
//! out of the file with no lock at all. The clocks are atomics. No call
//! here takes a lock; the directory registry (`open_dirs`) is the only
//! exclusion, and it is taken only by `lock_file`.

use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;

use kovan_map::HashMap;

use crate::portability::{AtomicU64, Ordering};

use super::db_lock::DirectoryRegistry;
use super::mem_file::{Free, MemFile};
use super::{
    Capabilities, Env, FileLock, FileMeta, JoinHandle, ReadDir, ReadFile, WriteFile, WriteMode,
};

/// Buckets each map starts with; they grow on demand.
const BUCKETS: usize = 64;

/// A clock that is not there: `None` from `now_micros` or `unix_secs`.
const ABSENT: u64 = u64::MAX;

struct MemFs {
    files: HashMap<PathBuf, Arc<MemFile>>,
    dirs: HashMap<PathBuf, ()>,
}

impl Default for MemFs {
    fn default() -> Self {
        Self {
            files: HashMap::with_capacity(BUCKETS),
            dirs: HashMap::with_capacity(BUCKETS),
        }
    }
}

/// An [`Env`] whose filesystem is a map in memory.
///
/// Clones share one filesystem, so a `MemEnv` handed to
/// [`crate::Options::env`] can be kept by the caller and inspected
/// after the database closes.
///
/// Every call is lock-free. A read copies out of the file while appends,
/// overwrites and renames go on beside it, and sees every write that
/// returned before it began.
#[derive(Clone, Default)]
pub struct MemEnv {
    fs: Arc<MemFs>,
    clock: Arc<MemClock>,
    /// Exclusion between database handles on this filesystem. Scoped
    /// to the `MemEnv` rather than the process because two `MemEnv`s
    /// are two unrelated filesystems that may legitimately hold the
    /// same path.
    open_dirs: Arc<DirectoryRegistry>,
}

/// The two clocks, each [`ABSENT`] when removed. Present values saturate
/// one below it.
struct MemClock {
    micros: AtomicU64,
    unix_secs: AtomicU64,
}

impl Default for MemClock {
    fn default() -> Self {
        Self {
            micros: AtomicU64::new(0),
            unix_secs: AtomicU64::new(0),
        }
    }
}

fn clock_value(raw: u64) -> Option<u64> {
    (raw != ABSENT).then_some(raw)
}

/// Advance a present clock by `by`, saturating below [`ABSENT`].
fn advance(clock: &AtomicU64, by: u64) {
    let _ = clock.fetch_update(Ordering::AcqRel, Ordering::Acquire, |now| {
        (now != ABSENT).then(|| now.saturating_add(by).min(ABSENT - 1))
    });
}

impl std::fmt::Debug for MemEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MemEnv")
            .field("files", &self.fs.files.len())
            .field("dirs", &self.fs.dirs.len())
            .finish()
    }
}

impl MemEnv {
    /// An empty in-memory filesystem with a clock starting at zero.
    pub fn new() -> Self {
        Self::default()
    }

    /// Advance the monotonic clock by `micros` and the wall clock by
    /// the whole seconds that implies.
    ///
    /// Time in a `MemEnv` only moves when a test moves it, so a test
    /// that depends on elapsed time is deterministic instead of
    /// racing the machine it runs on.
    pub fn advance_micros(&self, micros: u64) {
        advance(&self.clock.micros, micros);
        advance(&self.clock.unix_secs, micros / 1_000_000);
    }

    /// Remove the monotonic clock, the wall clock, or both, to
    /// exercise what regolith does on a platform that has none.
    pub fn set_clocks(&self, micros: Option<u64>, unix_secs: Option<u64>) {
        let store = |clock: &AtomicU64, value: Option<u64>| {
            clock.store(
                value.map_or(ABSENT, |v| v.min(ABSENT - 1)),
                Ordering::Release,
            );
        };
        store(&self.clock.micros, micros);
        store(&self.clock.unix_secs, unix_secs);
    }

    /// Total bytes currently held across every file.
    pub fn total_bytes(&self) -> u64 {
        self.fs.files.values().map(|f| f.len()).sum()
    }

    /// Number of files currently present.
    pub fn file_count(&self) -> usize {
        self.fs.files.len()
    }

    fn lookup(&self, path: &Path) -> io::Result<Arc<MemFile>> {
        self.fs.files.get(path).ok_or_else(|| not_found(path))
    }
}

fn not_found(path: &Path) -> io::Error {
    io::Error::new(
        io::ErrorKind::NotFound,
        format!("no such file in MemEnv: {}", path.display()),
    )
}

impl Env for MemEnv {
    fn create_dir_all(&self, path: &Path) -> io::Result<()> {
        let mut cursor = Some(path);
        while let Some(dir) = cursor {
            if self.fs.files.contains_key(dir) {
                return Err(io::Error::new(
                    io::ErrorKind::AlreadyExists,
                    format!("{} exists and is not a directory", dir.display()),
                ));
            }
            self.fs.dirs.insert(dir.to_path_buf(), ());
            cursor = dir.parent().filter(|p| !p.as_os_str().is_empty());
        }
        Ok(())
    }

    fn read_dir(&self, path: &Path) -> io::Result<ReadDir<'_>> {
        if !self.fs.dirs.contains_key(path) {
            return Err(not_found(path));
        }
        // The namespace is flat, so the walk passes every path and keeps
        // the direct children, one bucket of each map at a time. Each map
        // walk pins a kovan guard until it ends (a node it passed is not
        // freed meanwhile) and takes no lock.
        Ok(super::flat_children(
            path,
            self.fs.files.keys(),
            self.fs.dirs.keys(),
        ))
    }

    fn open_read(&self, path: &Path) -> io::Result<Box<dyn ReadFile>> {
        Ok(Box::new(MemReadFile {
            data: self.lookup(path)?,
        }))
    }

    fn open_write(&self, path: &Path, mode: WriteMode) -> io::Result<Box<dyn WriteFile>> {
        if let Some(parent) = path.parent()
            && !parent.as_os_str().is_empty()
            && !self.fs.dirs.contains_key(parent)
        {
            return Err(not_found(parent));
        }
        let data = match self.fs.files.get(path) {
            Some(data) => data,
            None => self
                .fs
                .files
                .get_or_insert(path.to_path_buf(), Arc::new(MemFile::new())),
        };
        if mode == WriteMode::Truncate {
            data.set_len(0, &Free)?;
        }
        Ok(Box::new(MemWriteFile { data }))
    }

    fn metadata(&self, path: &Path) -> io::Result<FileMeta> {
        if let Some(file) = self.fs.files.get(path) {
            return Ok(FileMeta {
                len: file.len(),
                is_dir: false,
            });
        }
        if self.fs.dirs.contains_key(path) {
            return Ok(FileMeta {
                len: 0,
                is_dir: true,
            });
        }
        Err(not_found(path))
    }

    fn remove_file(&self, path: &Path) -> io::Result<()> {
        self.fs
            .files
            .remove(path)
            .map(|_| ())
            .ok_or_else(|| not_found(path))
    }

    fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        if from == to {
            return self.lookup(from).map(|_| ());
        }
        // The file is taken from `from` first, so two renames of one file
        // cannot both move it, then put at `to` in one map write, which
        // replaces whatever was there: `to` always names a whole file.
        let file = self.fs.files.remove(from).ok_or_else(|| not_found(from))?;
        self.fs.files.insert(to.to_path_buf(), file);
        Ok(())
    }

    fn hard_link(&self, _src: &Path, _dst: &Path) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "MemEnv has no hard links; see Capabilities::hard_link",
        ))
    }

    fn sync_dir(&self, _path: &Path) -> io::Result<()> {
        Ok(())
    }

    fn lock_file(&self, path: &Path, exclusive: bool) -> io::Result<Box<dyn FileLock>> {
        self.open_dirs.acquire(path, exclusive)
    }

    fn capabilities(&self) -> Capabilities {
        // Nothing here survives the process, so `durable_sync` is
        // false: a `sync_all` on a MemEnv file is a no-op and saying
        // otherwise would be a durability claim regolith cannot keep.
        Capabilities::none().with_atomic_rename(true)
    }

    fn now_micros(&self) -> Option<u64> {
        clock_value(self.clock.micros.load(Ordering::Acquire))
    }

    fn unix_secs(&self) -> Option<u64> {
        clock_value(self.clock.unix_secs.load(Ordering::Acquire))
    }

    fn spawn(
        &self,
        _name: &str,
        _body: Box<dyn FnOnce() + Send + 'static>,
    ) -> io::Result<Box<dyn JoinHandle>> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "MemEnv does not start threads; see Capabilities::threads",
        ))
    }

    fn sleep(&self, _dur: Duration) {}
}

struct MemReadFile {
    data: Arc<MemFile>,
}

impl ReadFile for MemReadFile {
    fn read_exact_at(&self, offset: u64, buf: &mut [u8]) -> io::Result<()> {
        self.data.read_exact_at(offset, buf)
    }

    fn len(&self) -> io::Result<u64> {
        Ok(self.data.len())
    }
}

struct MemWriteFile {
    data: Arc<MemFile>,
}

impl WriteFile for MemWriteFile {
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        self.write_all_vectored(&[buf])
    }

    /// One append for every slice: they land together, at the end.
    fn write_all_vectored(&mut self, slices: &[&[u8]]) -> io::Result<()> {
        self.data.append(slices, &Free).map(|_| ())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }

    fn sync_all(&mut self) -> io::Result<()> {
        Ok(())
    }

    fn set_len(&mut self, len: u64) -> io::Result<()> {
        self.data.set_len(len, &Free).map(|_| ())
    }

    fn len(&self) -> io::Result<u64> {
        Ok(self.data.len())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::DirEntry;

    fn env() -> MemEnv {
        let env = MemEnv::new();
        env.create_dir_all(Path::new("/db")).unwrap();
        env
    }

    /// The names under `dir`, sorted: a walk's order is unspecified.
    fn names(env: &MemEnv, dir: &str) -> Vec<String> {
        let mut names: Vec<String> = env
            .read_dir(Path::new(dir))
            .unwrap()
            .map(|e| e.unwrap().file_name())
            .collect();
        names.sort();
        names
    }

    #[test]
    fn write_read_round_trips() {
        let env = env();
        let path = Path::new("/db/file");
        env.write(path, b"payload").unwrap();
        assert_eq!(env.read(path).unwrap(), b"payload");
        assert_eq!(env.metadata(path).unwrap().len, 7);
        assert_eq!(env.file_count(), 1);
        assert_eq!(env.total_bytes(), 7);
    }

    #[test]
    fn writing_into_a_missing_directory_fails() {
        let env = env();
        let err = env
            .open_write(Path::new("/nowhere/file"), WriteMode::Truncate)
            .map(|_| ())
            .unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::NotFound);
    }

    #[test]
    fn truncate_discards_and_append_keeps() {
        let env = env();
        let path = Path::new("/db/f");
        env.write(path, b"0123456789").unwrap();
        {
            let mut w = env.open_write(path, WriteMode::Append).unwrap();
            w.write_all(b"ab").unwrap();
        }
        assert_eq!(env.read(path).unwrap(), b"0123456789ab");
        env.write(path, b"z").unwrap();
        assert_eq!(env.read(path).unwrap(), b"z");
    }

    #[test]
    fn read_dir_lists_only_direct_children() {
        let env = env();
        env.create_dir_all(Path::new("/db/sst")).unwrap();
        env.write(Path::new("/db/MANIFEST"), b"m").unwrap();
        env.write(Path::new("/db/sst/1.sst"), b"s").unwrap();

        assert_eq!(names(&env, "/db"), vec!["MANIFEST", "sst"]);
        let entries: Vec<DirEntry> = env
            .read_dir(Path::new("/db"))
            .unwrap()
            .map(Result::unwrap)
            .collect();
        assert!(entries.iter().any(|e| e.file_name() == "sst" && e.is_dir));
        assert!(
            entries
                .iter()
                .any(|e| e.file_name() == "MANIFEST" && !e.is_dir)
        );
    }

    #[test]
    fn a_walk_of_a_missing_directory_is_not_found() {
        let err = env()
            .read_dir(Path::new("/nowhere"))
            .map(|_| ())
            .unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::NotFound);
    }

    /// A directory far larger than one map bucket is walked whole, each
    /// entry once, while the walker removes every entry it was handed and
    /// files elsewhere in the namespace come and go.
    #[test]
    fn a_large_walk_yields_each_entry_once_while_the_walker_removes_them() {
        const FILES: usize = 5_000;
        let env = env();
        env.create_dir_all(Path::new("/other")).unwrap();
        for i in 0..FILES {
            env.write(Path::new(&format!("/db/{i:06}.sst")), b"x")
                .unwrap();
        }
        let mut seen = std::collections::HashSet::new();
        for (n, entry) in env.read_dir(Path::new("/db")).unwrap().enumerate() {
            let entry = entry.unwrap();
            assert!(seen.insert(entry.path.clone()), "{:?} twice", entry.path);
            env.remove_file(&entry.path).unwrap();
            // Churn outside the walked directory, which a flat namespace
            // shares with it.
            let other = PathBuf::from(format!("/other/{n}"));
            env.write(&other, b"y").unwrap();
            if n % 2 == 0 {
                env.remove_file(&other).unwrap();
            }
        }
        assert_eq!(seen.len(), FILES);
        assert!(names(&env, "/db").is_empty());
    }

    #[test]
    fn rename_moves_content_and_clears_the_source() {
        let env = env();
        env.write(Path::new("/db/tmp"), b"new").unwrap();
        env.write(Path::new("/db/live"), b"old").unwrap();
        env.rename(Path::new("/db/tmp"), Path::new("/db/live"))
            .unwrap();
        assert_eq!(env.read(Path::new("/db/live")).unwrap(), b"new");
        assert!(!env.exists(Path::new("/db/tmp")));
    }

    #[test]
    fn positional_reads_are_independent() {
        let env = env();
        let path = Path::new("/db/pos");
        env.write(path, b"0123456789").unwrap();
        let f = env.open_read(path).unwrap();
        let mut a = [0u8; 2];
        let mut b = [0u8; 2];
        f.read_exact_at(8, &mut a).unwrap();
        f.read_exact_at(0, &mut b).unwrap();
        assert_eq!(&a, b"89");
        assert_eq!(&b, b"01");
        assert_eq!(
            f.read_exact_at(9, &mut a).unwrap_err().kind(),
            io::ErrorKind::UnexpectedEof
        );
    }

    #[test]
    fn missing_capabilities_are_declared_and_enforced() {
        let env = env();
        let caps = env.capabilities();
        assert!(!caps.hard_link);
        assert!(!caps.sync_dir);
        assert!(!caps.threads);
        assert!(!caps.file_lock);
        assert!(!caps.durable_sync);
        assert!(caps.atomic_rename);

        assert_eq!(
            env.hard_link(Path::new("/db/a"), Path::new("/db/b"))
                .unwrap_err()
                .kind(),
            io::ErrorKind::Unsupported
        );
        assert_eq!(
            env.spawn("x", Box::new(|| {}))
                .map(|_| ())
                .unwrap_err()
                .kind(),
            io::ErrorKind::Unsupported
        );
    }

    #[test]
    fn the_clock_only_moves_when_a_test_moves_it() {
        let env = MemEnv::new();
        assert_eq!(env.now_micros(), Some(0));
        assert_eq!(env.unix_secs(), Some(0));
        env.advance_micros(2_500_000);
        assert_eq!(env.now_micros(), Some(2_500_000));
        assert_eq!(env.unix_secs(), Some(2));
        env.set_clocks(None, None);
        assert!(env.now_micros().is_none());
        assert!(env.unix_secs().is_none());
    }

    #[test]
    fn set_len_truncates_and_extends_with_zeroes() {
        let env = env();
        let path = Path::new("/db/sized");
        env.write(path, b"abcdef").unwrap();
        let mut w = env.open_write(path, WriteMode::Append).unwrap();
        w.set_len(3).unwrap();
        assert_eq!(w.len().unwrap(), 3);
        w.set_len(5).unwrap();
        drop(w);
        assert_eq!(env.read(path).unwrap(), b"abc\0\0");
    }

    #[test]
    fn clones_share_one_filesystem() {
        let env = env();
        let twin = env.clone();
        env.write(Path::new("/db/shared"), b"x").unwrap();
        assert!(twin.exists(Path::new("/db/shared")));
    }

    #[test]
    fn a_lock_on_a_mem_env_excludes_a_second_holder_and_creates_no_file() {
        let env = env();
        let first = env.lock_file(Path::new("/db"), true).unwrap();
        assert!(
            env.lock_file(Path::new("/db"), true).is_err(),
            "a second read-write handle on one directory must be refused"
        );
        drop(first);
        let again = env.lock_file(Path::new("/db"), true);
        assert!(again.is_ok(), "the directory must be free again after drop");
        drop(again);
        assert_eq!(env.file_count(), 0, "no LOCK file is ever created");
    }

    #[test]
    fn two_mem_envs_do_not_exclude_each_other() {
        let one = env();
        let two = env();
        let _held = one.lock_file(Path::new("/db"), true).unwrap();
        assert!(
            two.lock_file(Path::new("/db"), true).is_ok(),
            "two MemEnvs are two filesystems and must not share exclusion"
        );
    }

    #[test]
    fn a_removed_clock_stays_removed_and_a_present_one_saturates() {
        let env = MemEnv::new();
        env.set_clocks(Some(u64::MAX - 5), None);
        env.advance_micros(100);
        assert_eq!(env.now_micros(), Some(u64::MAX - 1));
        assert_eq!(env.unix_secs(), None);
    }

    /// Writers append to their own files, rename them into place and remove
    /// the old ones, while readers read every file that exists. Each read
    /// is a prefix of what its writer wrote, and the final filesystem holds
    /// exactly the renamed files, whole.
    #[test]
    fn concurrent_file_operations_never_tear_a_read() {
        const WRITERS: usize = 6;
        const ROUNDS: usize = 200;
        let env = env();
        let stop = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let readers: Vec<_> = (0..3)
            .map(|_| {
                let (env, stop) = (env.clone(), std::sync::Arc::clone(&stop));
                std::thread::spawn(move || {
                    while !stop.load(std::sync::atomic::Ordering::Acquire) {
                        for entry in env.read_dir(Path::new("/db")).unwrap() {
                            let Ok(file) = env.open_read(&entry.unwrap().path) else {
                                continue;
                            };
                            let mut bytes = vec![0u8; file.len().unwrap() as usize];
                            file.read_exact_at(0, &mut bytes).unwrap();
                            // Every byte a writer writes is its own number.
                            assert!(bytes.windows(2).all(|w| w[0] == w[1]), "{bytes:?}");
                        }
                    }
                })
            })
            .collect();
        let writers: Vec<_> = (0..WRITERS)
            .map(|w| {
                let env = env.clone();
                std::thread::spawn(move || {
                    for round in 0..ROUNDS {
                        let tmp = PathBuf::from(format!("/db/w{w}.tmp"));
                        let live = PathBuf::from(format!("/db/w{w}"));
                        let mut file = env.open_write(&tmp, WriteMode::Truncate).unwrap();
                        for _ in 0..=round % 7 {
                            file.write_all(&[w as u8; 16]).unwrap();
                        }
                        drop(file);
                        env.rename(&tmp, &live).unwrap();
                        if round % 5 == 0 {
                            env.remove_file(&live).unwrap();
                        }
                    }
                })
            })
            .collect();
        for writer in writers {
            writer.join().unwrap();
        }
        stop.store(true, std::sync::atomic::Ordering::Release);
        for reader in readers {
            reader.join().unwrap();
        }
        let want: Vec<String> = (0..WRITERS).map(|w| format!("w{w}")).collect();
        assert_eq!(names(&env, "/db"), want);
        for w in 0..WRITERS {
            let bytes = env.read(Path::new(&format!("/db/w{w}"))).unwrap();
            assert_eq!(bytes, vec![w as u8; 16 * ((ROUNDS - 1) % 7 + 1)]);
        }
    }

    mod model {
        use super::*;
        use proptest::prelude::*;
        use std::collections::BTreeMap;

        #[derive(Clone, Debug)]
        enum Op {
            Write(u8, Vec<u8>, bool),
            Remove(u8),
            Rename(u8, u8),
            Read(u8),
        }

        fn op() -> impl Strategy<Value = Op> {
            prop_oneof![
                (
                    0u8..4,
                    prop::collection::vec(any::<u8>(), 0..40),
                    any::<bool>()
                )
                    .prop_map(|(f, b, t)| Op::Write(f, b, t)),
                (0u8..4).prop_map(Op::Remove),
                (0u8..4, 0u8..4).prop_map(|(a, b)| Op::Rename(a, b)),
                (0u8..4).prop_map(Op::Read),
            ]
        }

        proptest! {
            /// The filesystem's files and their contents follow a
            /// `BTreeMap` through writes, removes, renames and reads.
            #[test]
            fn the_env_follows_a_map(ops in prop::collection::vec(op(), 1..60)) {
                let env = env();
                let path = |f: u8| PathBuf::from(format!("/db/f{f}"));
                let mut model: BTreeMap<u8, Vec<u8>> = BTreeMap::new();
                for op in ops {
                    match op {
                        Op::Write(f, bytes, truncate) => {
                            let mode = if truncate { WriteMode::Truncate } else { WriteMode::Append };
                            env.open_write(&path(f), mode).unwrap().write_all(&bytes).unwrap();
                            let file = model.entry(f).or_default();
                            if truncate {
                                file.clear();
                            }
                            file.extend_from_slice(&bytes);
                        }
                        Op::Remove(f) => {
                            prop_assert_eq!(env.remove_file(&path(f)).is_ok(), model.remove(&f).is_some());
                        }
                        Op::Rename(a, b) => {
                            let got = env.rename(&path(a), &path(b));
                            match model.remove(&a) {
                                Some(bytes) => {
                                    prop_assert!(got.is_ok());
                                    model.insert(b, bytes);
                                }
                                None => prop_assert!(got.is_err()),
                            }
                        }
                        Op::Read(f) => match (env.read(&path(f)), model.get(&f)) {
                            (Ok(bytes), Some(want)) => prop_assert_eq!(&bytes, want),
                            (Err(e), None) => prop_assert_eq!(e.kind(), io::ErrorKind::NotFound),
                            (got, want) => prop_assert!(false, "{got:?} vs {want:?}"),
                        },
                    }
                    let want: Vec<String> = model.keys().map(|f| format!("f{f}")).collect();
                    prop_assert_eq!(names(&env, "/db"), want);
                    prop_assert_eq!(env.total_bytes(), model.values().map(|b| b.len() as u64).sum::<u64>());
                }
            }
        }
    }
}
