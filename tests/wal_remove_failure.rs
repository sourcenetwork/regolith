//! A write-ahead log a flush could not remove (E30).
//!
//! A flush puts its memtable in a table and then removes the log that held
//! those writes. When the removal fails the log stays on disk, and recovery
//! must not replay it: its versions would land in the memtable, which a
//! read consults before any table, so a key rewritten since, by a later
//! flush or an ingest, would read back as its older value. The failure is
//! reported, with a warn line and `regolith.wal.remove_failed`, and the log
//! is removed again by the next flush or the next open.

use std::io;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use regolith::env::{
    Capabilities, DirEntry, Env, FileLock, FileMeta, JoinHandle, ReadFile, StdEnv, WriteFile,
    WriteMode,
};
use regolith::{Db, IngestOptions, Options, SstFileWriter, Statistics, Ticker};
use tempfile::TempDir;

/// Which log removals [`LogRemoveFails`] refuses.
#[derive(Debug, Default, Clone)]
enum Refuse {
    #[default]
    Nothing,
    /// Every write-ahead log.
    EveryLog,
    /// This log only.
    Log(PathBuf),
}

/// Delegates to [`StdEnv`], but refuses the removals it is armed for, the
/// way a file another process holds open is refused on Windows.
#[derive(Debug, Default)]
struct LogRemoveFails {
    inner: StdEnv,
    refuse: Mutex<Refuse>,
    refused: AtomicUsize,
}

impl LogRemoveFails {
    fn arm(&self, refuse: Refuse) {
        *self.refuse.lock().unwrap() = refuse;
    }

    fn refuses(&self, path: &Path) -> bool {
        match &*self.refuse.lock().unwrap() {
            Refuse::Nothing => false,
            Refuse::EveryLog => is_log(path),
            Refuse::Log(log) => path == log,
        }
    }
}

fn is_log(path: &Path) -> bool {
    path.extension().is_some_and(|ext| ext == "log")
}

impl Env for LogRemoveFails {
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
        self.inner.open_write(path, mode)
    }
    fn metadata(&self, path: &Path) -> io::Result<FileMeta> {
        self.inner.metadata(path)
    }
    fn remove_file(&self, path: &Path) -> io::Result<()> {
        if self.refuses(path) {
            self.refused.fetch_add(1, Ordering::SeqCst);
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "the log is held open elsewhere",
            ));
        }
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

struct Fixture {
    dir: TempDir,
    env: Arc<LogRemoveFails>,
    stats: Arc<Statistics>,
}

impl Fixture {
    fn new() -> Self {
        Self {
            dir: TempDir::new().unwrap(),
            env: Arc::new(LogRemoveFails::default()),
            stats: Arc::new(Statistics::new()),
        }
    }

    fn open(&self) -> Db {
        Db::open(
            self.dir.path(),
            Options::default()
                .env(Arc::clone(&self.env) as Arc<dyn Env>)
                .statistics(Some(Arc::clone(&self.stats)))
                .max_background_compactions(0),
        )
        .unwrap()
    }

    fn logs(&self) -> Vec<PathBuf> {
        let mut logs: Vec<PathBuf> = std::fs::read_dir(self.dir.path().join("wal"))
            .unwrap()
            .map(|e| e.unwrap().path())
            .filter(|p| is_log(p))
            .collect();
        logs.sort();
        logs
    }

    fn remove_failures(&self) -> u64 {
        self.stats.get_ticker(Ticker::WalRemoveFailed)
    }

    /// Write `key = old` and flush it while the removal of the log that
    /// held the write fails, so the log outlives its flush. Returns the
    /// leftover log; its removal stays refused until the caller disarms.
    fn flush_leaving_its_log(&self, db: &Db, key: &[u8]) -> PathBuf {
        db.put(key, b"old").unwrap();
        let sealed = self.logs();
        assert_eq!(sealed.len(), 1, "one active log before the flush");
        self.env.arm(Refuse::Log(sealed[0].clone()));
        db.flush().unwrap();
        assert!(
            self.env.refused.load(Ordering::SeqCst) > 0,
            "the flush tried to remove its log"
        );
        assert!(sealed[0].exists(), "the flushed log outlived its flush");
        sealed[0].clone()
    }
}

#[test]
fn a_log_a_flush_left_behind_is_not_replayed_above_a_newer_table() {
    let f = Fixture::new();
    let leftover = {
        let db = f.open();
        let leftover = f.flush_leaving_its_log(&db, b"k");
        db.put(b"k", b"new").unwrap();
        // The newer table's flush retries the leftover's removal, which
        // still fails, so the leftover is there at the reopen.
        db.flush().unwrap();
        db.close().unwrap();
        leftover
    };
    f.env.arm(Refuse::Nothing);
    assert!(leftover.exists(), "the leftover survives to the reopen");
    let db = f.open();
    assert_eq!(
        db.get(b"k").unwrap().as_deref(),
        Some(&b"new"[..]),
        "recovery replayed a flushed log above the newer table"
    );
}

#[test]
fn a_log_a_flush_left_behind_is_not_replayed_above_an_ingested_table() {
    let f = Fixture::new();
    {
        let db = f.open();
        f.flush_leaving_its_log(&db, b"k");
        let source = f.dir.path().with_extension("ingest.sst");
        let mut writer = SstFileWriter::create(&source, &Options::default()).unwrap();
        writer.put(b"k", b"new").unwrap();
        writer.finish().unwrap();
        db.ingest_external_files(&[source], IngestOptions::default())
            .unwrap();
        assert_eq!(db.get(b"k").unwrap().as_deref(), Some(&b"new"[..]));
        db.close().unwrap();
    }
    f.env.arm(Refuse::Nothing);
    let db = f.open();
    assert_eq!(
        db.get(b"k").unwrap().as_deref(),
        Some(&b"new"[..]),
        "recovery replayed a flushed log above the ingested table"
    );
}

#[test]
fn a_failed_removal_is_counted_and_retried_by_the_next_flush() {
    let f = Fixture::new();
    let db = f.open();
    let leftover = f.flush_leaving_its_log(&db, b"k");
    f.env.arm(Refuse::Nothing);
    assert_eq!(f.remove_failures(), 1, "the failed removal is counted once");

    db.put(b"j", b"v").unwrap();
    db.flush().unwrap();
    assert!(
        !leftover.exists(),
        "the next flush removes the log the earlier one left"
    );
    assert_eq!(f.logs().len(), 1, "only the active log remains");
    assert_eq!(f.remove_failures(), 1, "the retry succeeded");
}

#[test]
fn a_failed_removal_is_retried_by_the_next_open() {
    let f = Fixture::new();
    let leftover = {
        let db = f.open();
        let leftover = f.flush_leaving_its_log(&db, b"k");
        db.close().unwrap();
        leftover
    };
    f.env.arm(Refuse::Nothing);
    assert!(leftover.exists());

    let db = f.open();
    assert!(
        !leftover.exists(),
        "the open removes the log the flush left"
    );
    assert_eq!(f.logs().len(), 1, "only the active log remains");
    assert_eq!(db.get(b"k").unwrap().as_deref(), Some(&b"old"[..]));
}

#[test]
fn an_open_that_cannot_remove_a_log_reports_it_and_still_opens() {
    let f = Fixture::new();
    {
        let db = f.open();
        db.put(b"k", b"v").unwrap();
        db.close().unwrap();
    }
    f.env.arm(Refuse::EveryLog);
    let db = f.open();
    f.env.arm(Refuse::Nothing);
    assert!(f.remove_failures() >= 1, "the failed removal is counted");
    assert_eq!(db.get(b"k").unwrap().as_deref(), Some(&b"v"[..]));
    drop(db);

    let db = f.open();
    assert_eq!(
        f.logs().len(),
        1,
        "the next open removes what the last one could not"
    );
    assert_eq!(db.get(b"k").unwrap().as_deref(), Some(&b"v"[..]));
}
