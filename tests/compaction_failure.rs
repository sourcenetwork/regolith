//! How the engine behaves when compaction keeps failing.
//!
//! A failed compaction must not leave its outputs on disk: nothing
//! references them, so a compaction that kept failing (out of file
//! descriptors, say) used to leak a full set on every retry until the disk
//! filled. A background worker must also back off between failed passes
//! and report them through `regolith.background-errors`.

use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

use regolith::env::{
    Capabilities, DirEntry, Env, FileLock, FileMeta, JoinHandle, ReadFile, StdEnv, WriteFile,
    WriteMode,
};
use regolith::{Db, Options};

/// Delegates to [`StdEnv`], but once armed lets only `budget` more
/// SSTables be created and fails the rest the way an exhausted file
/// descriptor table does.
#[derive(Debug)]
struct SstBudgetEnv {
    inner: StdEnv,
    remaining: AtomicUsize,
    refused: AtomicUsize,
}

const UNLIMITED: usize = usize::MAX;

impl SstBudgetEnv {
    fn new() -> Self {
        Self {
            inner: StdEnv::new(),
            remaining: AtomicUsize::new(UNLIMITED),
            refused: AtomicUsize::new(0),
        }
    }

    fn allow_ssts(&self, budget: usize) {
        self.remaining.store(budget, Ordering::SeqCst);
    }

    fn take_sst(&self) -> bool {
        let mut n = self.remaining.load(Ordering::SeqCst);
        loop {
            let next = match n {
                UNLIMITED => return true,
                0 => return false,
                n => n - 1,
            };
            match self
                .remaining
                .compare_exchange(n, next, Ordering::SeqCst, Ordering::SeqCst)
            {
                Ok(_) => return true,
                Err(current) => n = current,
            }
        }
    }
}

fn is_sst(path: &Path) -> bool {
    path.extension().is_some_and(|ext| ext == "sst")
}

impl Env for SstBudgetEnv {
    fn create_dir_all(&self, path: &Path) -> io::Result<()> {
        self.inner.create_dir_all(path)
    }
    fn read_dir(&self, path: &Path) -> io::Result<Vec<DirEntry>> {
        self.inner.read_dir(path)
    }
    fn open_read(&self, path: &Path) -> io::Result<Box<dyn ReadFile>> {
        self.inner.open_read(path)
    }
    fn open_write(&self, path: &Path, mode: WriteMode) -> io::Result<Box<dyn WriteFile>> {
        if is_sst(path) && !self.take_sst() {
            self.refused.fetch_add(1, Ordering::SeqCst);
            return Err(io::Error::other("Too many open files (os error 24)"));
        }
        self.inner.open_write(path, mode)
    }
    fn metadata(&self, path: &Path) -> io::Result<FileMeta> {
        self.inner.metadata(path)
    }
    fn remove_file(&self, path: &Path) -> io::Result<()> {
        self.inner.remove_file(path)
    }
    fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        self.inner.rename(from, to)
    }
    fn hard_link(&self, src: &Path, dst: &Path) -> io::Result<()> {
        self.inner.hard_link(src, dst)
    }
    fn sync_dir(&self, path: &Path) -> io::Result<()> {
        self.inner.sync_dir(path)
    }
    fn lock_file(&self, path: &Path, exclusive: bool) -> io::Result<Box<dyn FileLock>> {
        self.inner.lock_file(path, exclusive)
    }
    fn capabilities(&self) -> Capabilities {
        self.inner.capabilities()
    }
    fn now_micros(&self) -> Option<u64> {
        self.inner.now_micros()
    }
    fn unix_secs(&self) -> Option<u64> {
        self.inner.unix_secs()
    }
    fn spawn(
        &self,
        name: &str,
        body: Box<dyn FnOnce() + Send + 'static>,
    ) -> io::Result<Box<dyn JoinHandle>> {
        self.inner.spawn(name, body)
    }
    fn sleep(&self, dur: Duration) {
        self.inner.sleep(dur)
    }
}

fn sst_files(dir: &Path) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir.join("sst"))
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| is_sst(p))
        .collect();
    files.sort();
    files
}

fn key(i: u32) -> Vec<u8> {
    format!("key{i:08}").into_bytes()
}

#[test]
fn a_compaction_that_fails_midway_leaves_no_outputs_behind() {
    let dir = tempfile::tempdir().unwrap();
    let env = Arc::new(SstBudgetEnv::new());
    let opts = Options {
        env: Arc::clone(&env) as Arc<dyn Env>,
        max_background_compactions: 0,
        target_file_size: 16 * 1024,
        ..Options::default()
    };
    let db = Db::open(dir.path(), opts).unwrap();

    for batch in 0..4u32 {
        for i in 0..2_000u32 {
            db.put(&key(batch * 2_000 + i), &[batch as u8; 64]).unwrap();
        }
        db.flush().unwrap();
    }
    let live_before = sst_files(dir.path());
    assert!(live_before.len() >= 4, "setup must leave several L0 tables");

    // Room for one output, so the failure lands after a finished file.
    env.allow_ssts(1);
    for _ in 0..5 {
        assert!(db.compact_range(None, None).is_err());
        assert_eq!(
            sst_files(dir.path()),
            live_before,
            "a failed compaction must leave exactly the live tables on disk"
        );
    }

    env.allow_ssts(UNLIMITED);
    db.compact_range(None, None).unwrap();
    for i in 0..8_000u32 {
        assert!(db.get(&key(i)).unwrap().is_some(), "key {i} lost");
    }
}

#[test]
fn a_failing_background_worker_backs_off_and_counts_its_failures() {
    let dir = tempfile::tempdir().unwrap();
    let env = Arc::new(SstBudgetEnv::new());
    let opts = |l0_compaction_trigger| Options {
        env: Arc::clone(&env) as Arc<dyn Env>,
        l0_compaction_trigger,
        ..Options::default()
    };

    let db = Db::open(dir.path(), opts(1_000)).unwrap();
    for batch in 0..6u32 {
        for i in 0..500u32 {
            db.put(&key(batch * 500 + i), &[batch as u8; 64]).unwrap();
        }
        db.flush().unwrap();
    }
    db.close().unwrap();
    drop(db);

    env.allow_ssts(0);
    let db = Db::open(dir.path(), opts(2)).unwrap();
    std::thread::sleep(Duration::from_secs(7));

    let failures = db.get_int_property("regolith.background-errors").unwrap();
    let attempts = env.refused.load(Ordering::SeqCst);
    assert!(failures >= 2, "expected repeated failures, saw {failures}");
    assert_eq!(failures as usize, attempts, "every failed pass is counted");
    // Unpaced, the worker retries on every one-second poll: about 7
    // attempts here. Backing off 1 s, 2 s, 4 s allows at most 4.
    assert!(attempts <= 4, "worker retried {attempts} times in 7 s");

    env.allow_ssts(UNLIMITED);
    for i in 0..3_000u32 {
        assert!(db.get(&key(i)).unwrap().is_some(), "key {i} lost");
    }
}
