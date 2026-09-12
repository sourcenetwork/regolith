//! Deterministic proof that an ingest orders itself like a flush, and
//! that ordering it so never makes a write wait for it.
//!
//! `Db::ingest_external_files` allocates its sequence number and holds
//! the flush exclusion (`flushing`) from that allocation through its
//! manifest apply, so a flush of a memtable sealed before the ingest's
//! critical section always installs before the ingested file, and one
//! sealed after it always installs after: a memtable that fills while
//! the ingest writes its table is sealed without a flush, and the ingest
//! flushes it once its file is installed. Each test forces one
//! interleaving, named in its doc, with a seam that pauses or fails a
//! real background write mid-flight, then checks the read that
//! interleaving gets wrong, the writes that must not wait, and the
//! reopened sequence counter that the manifest's raised-maximum rule
//! protects on its own.
#![cfg(not(target_arch = "wasm32"))]

use std::io;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread::JoinHandle as StdJoinHandle;
use std::time::{Duration, Instant};

use regolith::env::{
    Capabilities, DirEntry, Env, FileLock, FileMeta, JoinHandle, ReadFile, StdEnv, WriteFile,
    WriteMode,
};
use regolith::{
    Db, Error, IngestOptions, Options, Priority, RateLimiter, SstFileWriter, WriteBatch,
    WriteOptions,
};
use tempfile::TempDir;

/// How long a test lets the fixed engine prove the losing side of the
/// race did not finish on its own before the paused party is released.
/// After the fix the paused party is what the other thread is blocked
/// on, so nothing can finish first regardless of this value; the
/// deadline only bounds how long a broken engine gets to hide the bug.
const RELEASE_DEADLINE: Duration = Duration::from_secs(3);

/// How long a write that must not wait for a paused ingest gets to
/// return. Generous, because a correct engine makes it wait on nothing:
/// only this test's thread can release the ingest, so the bound is what
/// turns a write stuck behind it into a failure instead of a hang.
const WRITE_DEADLINE: Duration = Duration::from_secs(10);

/// Polls `done` with a bounded backoff (1 ms doubling to a 50 ms cap,
/// never a fixed sleep in a loop) until it returns true or `deadline`
/// passes. Returns whether it did.
fn wait_until(deadline: Duration, mut done: impl FnMut() -> bool) -> bool {
    let start = Instant::now();
    let mut backoff = Duration::from_millis(1);
    while !done() {
        if start.elapsed() >= deadline {
            return false;
        }
        std::thread::sleep(backoff);
        backoff = (backoff * 2).min(Duration::from_millis(50));
    }
    true
}

/// Whether `handle`'s thread finished within `deadline`.
fn wait_finished<T>(handle: &StdJoinHandle<T>, deadline: Duration) -> bool {
    wait_until(deadline, || handle.is_finished())
}

/// Waits for `handle` as [`wait_finished`] does, then calls `release`.
/// Every assertion in the tests that use it holds regardless of which
/// way the wait resolves.
fn release_when_finished_or_after<T>(
    handle: &StdJoinHandle<T>,
    deadline: Duration,
    release: impl FnOnce(),
) {
    wait_finished(handle, deadline);
    release();
}

/// Bytes held by frozen memtables: sealed, and not yet flushed.
fn frozen_bytes(db: &Db) -> u64 {
    let all = db
        .get_int_property("regolith.cur-size-all-mem-tables")
        .unwrap();
    let active = db
        .get_int_property("regolith.cur-size-active-mem-table")
        .unwrap();
    all - active
}

/// Writes eight 1 KiB values under `prefix`. With a 4 KiB write buffer
/// that fills the active memtable and rotates it at least once, whatever
/// it already held.
fn write_past_one_rotation(db: &Db, prefix: &str) -> regolith::Result<()> {
    for i in 0..8 {
        db.put(format!("{prefix}{i}").as_bytes(), &[0u8; 1024])?;
    }
    Ok(())
}

/// Pauses the first `Priority::Low` [`RateLimiter::request`] after
/// [`arm`](Self::arm), until [`release`](Self::release) is called.
/// The flush path is the only caller reachable in the test that arms it
/// (compaction is the other): `Options::default()` sets
/// `l0_compaction_trigger` to 4 and that test holds at most two L0
/// files, so no compaction runs and none requests the limiter. So
/// arming this before a `db.flush()` catches the flush after its table
/// is written and before its manifest apply.
struct PauseFirstLowRequest {
    // (armed, paused, released)
    state: Mutex<(bool, bool, bool)>,
    cv: Condvar,
}

impl PauseFirstLowRequest {
    fn new() -> Arc<Self> {
        Arc::new(Self {
            state: Mutex::new((false, false, false)),
            cv: Condvar::new(),
        })
    }

    fn arm(&self) {
        self.state.lock().unwrap().0 = true;
    }

    /// Blocks until the armed request has paused. Panics with a plain
    /// message if `deadline` passes first: an honest failure, never a
    /// hang, if the engine never reaches the paused call.
    fn wait_paused(&self, deadline: Duration) {
        let state = self.state.lock().unwrap();
        let (_state, result) = self
            .cv
            .wait_timeout_while(state, deadline, |s| !s.1)
            .unwrap();
        if result.timed_out() {
            panic!("flush never reached its rate-limited write within {deadline:?}");
        }
    }

    fn release(&self) {
        self.state.lock().unwrap().2 = true;
        self.cv.notify_all();
    }
}

impl RateLimiter for PauseFirstLowRequest {
    fn request(&self, _bytes: u64, pri: Priority) {
        if pri == Priority::High {
            return;
        }
        let mut state = self.state.lock().unwrap();
        if !state.0 {
            return;
        }
        state.0 = false;
        state.1 = true;
        self.cv.notify_all();
        while !state.2 {
            state = self.cv.wait(state).unwrap();
        }
    }

    fn set_bytes_per_second(&self, _bytes_per_second: u64) {}

    fn get_bytes_per_second(&self) -> u64 {
        u64::MAX
    }

    fn get_total_bytes_through(&self, _pri: Priority) -> u64 {
        0
    }
}

/// Wraps [`StdEnv`] and counts the calls to `open_write` whose parent
/// directory is the database's `sst` directory (SST file writes; WAL
/// and MANIFEST writes live elsewhere and are not counted). The
/// `pause_nth` call blocks until [`release`](Self::release) is called,
/// and the `fail_nth` call returns an injected error instead of opening
/// the file, after its pause when both name the same call. `0` matches
/// no call.
#[derive(Debug)]
struct NthSstOpen {
    inner: StdEnv,
    sst_dir: PathBuf,
    pause_nth: usize,
    fail_nth: usize,
    count: AtomicUsize,
    // (paused, released)
    state: Mutex<(bool, bool)>,
    cv: Condvar,
}

impl NthSstOpen {
    fn new(db_dir: &Path, pause_nth: usize, fail_nth: usize) -> Arc<Self> {
        Arc::new(Self {
            inner: StdEnv,
            sst_dir: db_dir.join("sst"),
            pause_nth,
            fail_nth,
            count: AtomicUsize::new(0),
            state: Mutex::new((false, false)),
            cv: Condvar::new(),
        })
    }

    /// Blocks until the `pause_nth` open has paused. Panics with a plain
    /// message if `deadline` passes first.
    fn wait_paused(&self, deadline: Duration) {
        let state = self.state.lock().unwrap();
        let (_state, result) = self
            .cv
            .wait_timeout_while(state, deadline, |s| !s.0)
            .unwrap();
        if result.timed_out() {
            panic!(
                "sst open never reached call {} within {deadline:?}",
                self.pause_nth
            );
        }
    }

    fn release(&self) {
        self.state.lock().unwrap().1 = true;
        self.cv.notify_all();
    }
}

impl Env for NthSstOpen {
    fn open_write(&self, path: &Path, mode: WriteMode) -> io::Result<Box<dyn WriteFile>> {
        if path.parent() == Some(self.sst_dir.as_path()) {
            let n = self.count.fetch_add(1, Ordering::AcqRel) + 1;
            if n == self.pause_nth {
                let mut state = self.state.lock().unwrap();
                state.0 = true;
                self.cv.notify_all();
                while !state.1 {
                    state = self.cv.wait(state).unwrap();
                }
            }
            if n == self.fail_nth {
                return Err(io::Error::other("injected table open failure"));
            }
        }
        self.inner.open_write(path, mode)
    }
    fn create_dir_all(&self, p: &Path) -> io::Result<()> {
        self.inner.create_dir_all(p)
    }
    fn read_dir(&self, p: &Path) -> io::Result<Vec<DirEntry>> {
        self.inner.read_dir(p)
    }
    fn open_read(&self, p: &Path) -> io::Result<Box<dyn ReadFile>> {
        self.inner.open_read(p)
    }
    fn metadata(&self, p: &Path) -> io::Result<FileMeta> {
        self.inner.metadata(p)
    }
    fn remove_file(&self, p: &Path) -> io::Result<()> {
        self.inner.remove_file(p)
    }
    fn rename(&self, a: &Path, b: &Path) -> io::Result<()> {
        self.inner.rename(a, b)
    }
    fn hard_link(&self, a: &Path, b: &Path) -> io::Result<()> {
        self.inner.hard_link(a, b)
    }
    fn sync_dir(&self, p: &Path) -> io::Result<()> {
        self.inner.sync_dir(p)
    }
    fn lock_file(&self, p: &Path, ex: bool) -> io::Result<Box<dyn FileLock>> {
        self.inner.lock_file(p, ex)
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
        f: Box<dyn FnOnce() + Send + 'static>,
    ) -> io::Result<Box<dyn JoinHandle>> {
        self.inner.spawn(name, f)
    }
    fn sleep(&self, d: Duration) {
        self.inner.sleep(d)
    }
}

/// Build a one-entry external SSTable ready for `ingest_external_files`.
fn build_ingest_file(dir: &Path, opts: &Options, key: &[u8], value: &[u8]) -> PathBuf {
    let path = dir.join("ingest.sst");
    let mut writer = SstFileWriter::create(&path, opts).unwrap();
    writer.put(key, value).unwrap();
    writer.finish().unwrap();
    path
}

/// Interleaving (a): a flush seals a memtable, releases the pipeline,
/// and is slow writing its table while an ingest for the same key
/// allocates a higher sequence and installs first.
#[test]
fn an_ingest_waits_for_a_flush_of_a_memtable_sealed_before_it() {
    let dir = TempDir::new().unwrap();
    let staging = TempDir::new().unwrap();
    let limiter = PauseFirstLowRequest::new();
    let opts = Options {
        rate_limiter: Some(limiter.clone()),
        ..Options::default()
    };
    let db = Arc::new(Db::open(dir.path(), opts.clone()).unwrap());

    db.put(b"k", b"old").unwrap();
    limiter.arm();

    let a = {
        let db = Arc::clone(&db);
        std::thread::spawn(move || db.flush())
    };
    limiter.wait_paused(Duration::from_secs(60));

    let ingest_path = build_ingest_file(staging.path(), &opts, b"k", b"new");
    let b = {
        let db = Arc::clone(&db);
        std::thread::spawn(move || {
            db.ingest_external_files(&[ingest_path], IngestOptions::default())
        })
    };

    release_when_finished_or_after(&b, RELEASE_DEADLINE, || limiter.release());
    a.join().unwrap().unwrap();
    b.join().unwrap().unwrap();

    // The ingested version is the newest and must win. Before the fix,
    // L0 holds the flush's file above the ingested one (or the
    // ingested file sits at the deepest level under it) and this reads
    // "old".
    assert_eq!(db.get(b"k").unwrap(), Some(b"new".to_vec()));

    let before = db.latest_sequence();
    drop(db);

    let reopen_limiter = PauseFirstLowRequest::new();
    let reopen_opts = Options {
        rate_limiter: Some(reopen_limiter),
        ..opts
    };
    let db = Db::open(dir.path(), reopen_opts).unwrap();

    // Before the fix, `last_seq` was lowered to the flush's sealed
    // sequence and the flushed WAL had already been removed, so the
    // reopened counter restarted below the ingested sequence.
    let mut batch = WriteBatch::new();
    batch.put(b"z", b"v");
    let seq = db.write_sequenced(batch).unwrap();
    assert!(
        seq > before,
        "reopened sequence {seq} did not exceed {before}"
    );

    // Before the fix the horizon restarted below the ingested
    // sequence and the ingested entries were hidden after reopen.
    assert_eq!(db.get(b"k").unwrap(), Some(b"new".to_vec()));
}

/// Interleaving (b): an ingest allocates its sequence and is slow
/// writing its table while a writer commits above it and a flush of
/// that write races to install first.
#[test]
fn a_flush_sealed_after_an_ingest_lands_above_the_ingested_file() {
    let dir = TempDir::new().unwrap();
    let staging = TempDir::new().unwrap();
    let env = NthSstOpen::new(dir.path(), 2, 0);
    let opts = Options {
        env: env.clone(),
        ..Options::default()
    };
    let db = Arc::new(Db::open(dir.path(), opts.clone()).unwrap());

    db.put(b"k", b"old").unwrap();

    let ingest_path = build_ingest_file(staging.path(), &opts, b"k", b"new");
    let b = {
        let db = Arc::clone(&db);
        std::thread::spawn(move || {
            db.ingest_external_files(&[ingest_path], IngestOptions::default())
        })
    };
    env.wait_paused(Duration::from_secs(60));

    // A commit that does not fill the memtable goes through while the
    // ingest is paused: the ingest holds `flushing`, not the pipeline.
    let put = {
        let db = Arc::clone(&db);
        std::thread::spawn(move || db.put(b"k", b"v2"))
    };
    if !wait_finished(&put, WRITE_DEADLINE) {
        // Unpaused first, so the threads this test started can finish
        // and the failure is reported instead of a hang.
        env.release();
        let _ = b.join();
        let _ = put.join();
        panic!("a commit did not complete while the ingest was paused");
    }
    put.join().unwrap().unwrap();

    let a = {
        let db = Arc::clone(&db);
        std::thread::spawn(move || db.flush())
    };

    release_when_finished_or_after(&a, RELEASE_DEADLINE, || env.release());
    a.join().unwrap().unwrap();
    b.join().unwrap().unwrap();

    // The write acknowledged after the ingest is the newest. Before
    // the fix, A installs first and the ingested file (overlapping, so
    // at L0) is installed above it, and this reads "new".
    assert_eq!(db.get(b"k").unwrap(), Some(b"v2".to_vec()));

    let before = db.latest_sequence();
    drop(db);

    let reopen_env = NthSstOpen::new(dir.path(), 0, 0);
    let reopen_opts = Options {
        env: reopen_env,
        ..opts
    };
    let db = Db::open(dir.path(), reopen_opts).unwrap();

    // Before the fix the ingest's stamp was applied after the flush's
    // higher one, so the reopened counter restarted below `before`.
    let mut batch = WriteBatch::new();
    batch.put(b"z", b"v");
    let seq = db.write_sequenced(batch).unwrap();
    assert!(
        seq > before,
        "reopened sequence {seq} did not exceed {before}"
    );

    assert_eq!(db.get(b"k").unwrap(), Some(b"v2".to_vec()));
    assert_eq!(db.get(b"z").unwrap(), Some(b"v".to_vec()));
}

/// Interleaving (a) with no flush in progress: a flush that failed
/// leaves its memtable frozen, and nothing is writing it when the
/// ingest allocates. The ingest must install that memtable before its
/// own file, or the older value, still in the frozen list, answers the
/// read.
///
/// Deterministic: it runs on one thread. `Db::open` opens no SST, so
/// the first SST open is M1's flush, which fails. The ingest's drain
/// retries that flush (the second open) before it allocates: M1 lands
/// at L0, the ingest overlaps it and lands above it, and the read
/// returns "new". Without the drain the ingest lands at the deepest
/// level while M1 stays frozen, and the read returns "old" from the
/// frozen list.
#[test]
fn an_ingest_drains_a_memtable_left_frozen_by_a_failed_flush() {
    let dir = TempDir::new().unwrap();
    let staging = TempDir::new().unwrap();
    let opts = Options {
        env: NthSstOpen::new(dir.path(), 0, 1),
        ..Options::default()
    };
    let db = Db::open(dir.path(), opts.clone()).unwrap();

    db.put(b"k", b"old").unwrap();
    assert!(
        db.flush().is_err(),
        "the injected table open failure must fail the flush"
    );

    let ingest_path = build_ingest_file(staging.path(), &opts, b"k", b"new");
    db.ingest_external_files(&[ingest_path], IngestOptions::default())
        .unwrap();

    // Without the drain, the ingest lands at the deepest level (the
    // version does not hold M1) and M1, still frozen, answers the
    // read: "old".
    assert_eq!(db.get(b"k").unwrap(), Some(b"new".to_vec()));

    let before = db.latest_sequence();
    drop(db);

    let db = Db::open(
        dir.path(),
        Options {
            env: NthSstOpen::new(dir.path(), 0, 0),
            ..opts
        },
    )
    .unwrap();

    // Without the maximum rule, M1's later stamp would lower
    // `last_seq` below the ingest's, and the reopened counter would
    // restart below `before`.
    let mut batch = WriteBatch::new();
    batch.put(b"z", b"v");
    let seq = db.write_sequenced(batch).unwrap();
    assert!(
        seq > before,
        "reopened sequence {seq} did not exceed {before}"
    );
    assert_eq!(db.get(b"k").unwrap(), Some(b"new".to_vec()));
}

/// A write that fills the memtable while an ingest writes its table
/// seals the memtable and returns: the ingest flushes that memtable
/// once it has installed its own file, so it lands above the file.
/// Before, the write waited for the flush exclusion while holding the
/// commit pipeline, and every other write waited behind it until the
/// ingest installed.
#[test]
fn a_write_that_fills_the_memtable_does_not_wait_for_an_ingest() {
    let dir = TempDir::new().unwrap();
    let staging = TempDir::new().unwrap();
    // The first SST open is the flush of `old` below; the second is the
    // ingest's table.
    let env = NthSstOpen::new(dir.path(), 2, 0);
    let opts = Options {
        env: env.clone(),
        write_buffer_size: 4 * 1024,
        ..Options::default()
    };
    let db = Arc::new(Db::open(dir.path(), opts.clone()).unwrap());

    // An L0 file holding `k`: the ingested file overlaps it, so it lands
    // at L0 as well, where install order decides which version a read
    // sees.
    db.put(b"k", b"old").unwrap();
    db.flush().unwrap();

    let ingest_path = build_ingest_file(staging.path(), &opts, b"k", b"new");
    let ingest = {
        let db = Arc::clone(&db);
        std::thread::spawn(move || {
            db.ingest_external_files(&[ingest_path], IngestOptions::default())
        })
    };
    env.wait_paused(Duration::from_secs(60));

    // `k = v2` goes into the memtable that the 1 KiB values then fill
    // and rotate.
    let writer = {
        let db = Arc::clone(&db);
        std::thread::spawn(move || {
            db.put(b"k", b"v2")?;
            write_past_one_rotation(&db, "f")
        })
    };
    let writer_done = wait_finished(&writer, WRITE_DEADLINE);
    let frozen_while_paused = frozen_bytes(&db);
    env.release();
    let ingested = ingest.join().unwrap();
    let written = writer.join().unwrap();

    assert!(
        writer_done,
        "a write that filled the memtable did not return while an ingest was writing its table"
    );
    written.unwrap();
    ingested.unwrap();
    assert!(
        frozen_while_paused > 0,
        "the writes never rotated the memtable, so nothing here was exercised"
    );

    // The ingest flushed that memtable after installing its file:
    // nothing is left frozen, and `v2`, written after the ingest began,
    // is the newest version of `k`.
    assert_eq!(
        frozen_bytes(&db),
        0,
        "the ingest returned with a memtable sealed during it still unflushed"
    );
    assert_eq!(db.get(b"k").unwrap(), Some(b"v2".to_vec()));

    // With the ingest done, a rotation flushes its own memtable again.
    write_past_one_rotation(&db, "g").unwrap();
    assert_eq!(
        frozen_bytes(&db),
        0,
        "a rotation after the ingest left its memtable unflushed"
    );

    let before = db.latest_sequence();
    drop(db);

    let db = Db::open(
        dir.path(),
        Options {
            env: NthSstOpen::new(dir.path(), 0, 0),
            ..opts
        },
    )
    .unwrap();
    let mut batch = WriteBatch::new();
    batch.put(b"z", b"v");
    let seq = db.write_sequenced(batch).unwrap();
    assert!(
        seq > before,
        "reopened sequence {seq} did not exceed {before}"
    );
    assert_eq!(db.get(b"k").unwrap(), Some(b"v2".to_vec()));
}

/// Memtables sealed while an ingest writes its table wait for that
/// ingest to flush them, and they count toward
/// `max_write_buffer_number` like any memtable waiting on a flush:
/// writes slow and then stop at the limit rather than grow memory for
/// as long as the ingest runs. With `no_slowdown`, the first write the
/// limit would slow fails with `Error::Busy` instead.
#[test]
fn memtables_sealed_during_an_ingest_count_toward_the_write_limit() {
    let dir = TempDir::new().unwrap();
    let staging = TempDir::new().unwrap();
    // Nothing is flushed before the ingest, so its table is the first
    // SST open.
    let env = NthSstOpen::new(dir.path(), 1, 0);
    let opts = Options {
        env: env.clone(),
        write_buffer_size: 4 * 1024,
        max_write_buffer_number: 2,
        ..Options::default()
    };
    let db = Arc::new(Db::open(dir.path(), opts.clone()).unwrap());

    let ingest_path = build_ingest_file(staging.path(), &opts, b"k", b"new");
    let ingest = {
        let db = Arc::clone(&db);
        std::thread::spawn(move || {
            db.ingest_external_files(&[ingest_path], IngestOptions::default())
        })
    };
    env.wait_paused(Duration::from_secs(60));

    let writer = {
        let db = Arc::clone(&db);
        std::thread::spawn(move || {
            let no_slowdown = WriteOptions {
                no_slowdown: true,
                ..WriteOptions::default()
            };
            for i in 0..64 {
                match db.put_opt(&no_slowdown, format!("f{i:02}").as_bytes(), &[0u8; 1024]) {
                    Ok(()) => {}
                    Err(Error::Busy(reason)) => return Ok(Some(reason)),
                    Err(e) => return Err(e),
                }
            }
            Ok(None)
        })
    };
    let writer_done = wait_finished(&writer, WRITE_DEADLINE);
    let frozen_while_paused = frozen_bytes(&db);
    env.release();
    let ingested = ingest.join().unwrap();
    let refused = writer.join().unwrap();

    assert!(
        writer_done,
        "a write with no_slowdown did not return while an ingest was writing its table"
    );
    ingested.unwrap();
    let Some(reason) = refused.unwrap() else {
        panic!(
            "64 writes into 4 KiB memtables were all accepted while an ingest held their \
             flushes: nothing bounded the memtables it held"
        );
    };
    assert!(
        reason.contains("memtables"),
        "the write was refused for {reason:?}, not for the memtable limit"
    );
    assert!(
        frozen_while_paused > 0,
        "no memtable was held for the ingest, so nothing here was exercised"
    );

    // The ingest flushed what it held, and the limit is gone with it.
    assert_eq!(
        frozen_bytes(&db),
        0,
        "the ingest returned with memtables sealed during it still unflushed"
    );
    let no_slowdown = WriteOptions {
        no_slowdown: true,
        ..WriteOptions::default()
    };
    db.put_opt(&no_slowdown, b"after", b"v").unwrap();
}

/// An ingest that fails after it allocated its sequence still flushes
/// the memtables sealed while it ran, and a rotation after it flushes
/// its own memtable again: the failure neither strands those writes in
/// memory nor leaves later rotations waiting for an ingest that is gone.
#[test]
fn an_ingest_that_fails_still_flushes_the_memtables_sealed_while_it_ran() {
    let dir = TempDir::new().unwrap();
    let staging = TempDir::new().unwrap();
    // The ingest's table is the first SST open: it pauses, then fails.
    let env = NthSstOpen::new(dir.path(), 1, 1);
    let opts = Options {
        env: env.clone(),
        write_buffer_size: 4 * 1024,
        ..Options::default()
    };
    let db = Arc::new(Db::open(dir.path(), opts.clone()).unwrap());

    let ingest_path = build_ingest_file(staging.path(), &opts, b"k", b"new");
    let ingest = {
        let db = Arc::clone(&db);
        std::thread::spawn(move || {
            db.ingest_external_files(&[ingest_path], IngestOptions::default())
        })
    };
    env.wait_paused(Duration::from_secs(60));

    let writer = {
        let db = Arc::clone(&db);
        std::thread::spawn(move || {
            db.put(b"k", b"v2")?;
            write_past_one_rotation(&db, "f")
        })
    };
    let writer_done = wait_finished(&writer, WRITE_DEADLINE);
    let frozen_while_paused = frozen_bytes(&db);
    env.release();
    let ingested = ingest.join().unwrap();
    let written = writer.join().unwrap();

    assert!(
        writer_done,
        "a write that filled the memtable did not return while an ingest was writing its table"
    );
    written.unwrap();
    assert!(
        frozen_while_paused > 0,
        "the writes never rotated the memtable, so nothing here was exercised"
    );
    let err = ingested.unwrap_err();
    assert!(
        err.to_string().contains("injected table open failure"),
        "unexpected ingest error: {err}"
    );

    assert_eq!(
        frozen_bytes(&db),
        0,
        "a failed ingest left a memtable sealed during it unflushed"
    );
    assert_eq!(db.get(b"k").unwrap(), Some(b"v2".to_vec()));

    write_past_one_rotation(&db, "g").unwrap();
    assert_eq!(
        frozen_bytes(&db),
        0,
        "a rotation after a failed ingest left its memtable unflushed"
    );

    drop(db);
    let db = Db::open(
        dir.path(),
        Options {
            env: NthSstOpen::new(dir.path(), 0, 0),
            ..opts
        },
    )
    .unwrap();
    assert_eq!(db.get(b"k").unwrap(), Some(b"v2".to_vec()));
    assert_eq!(db.get(b"f0").unwrap(), Some(vec![0u8; 1024]));
}

/// If the ingest installs its file but flushing the memtables sealed
/// while it ran fails, the call reports that failure, the file stays
/// ingested, and those memtables stay frozen and readable until a later
/// flush writes them. Nothing is lost.
#[test]
fn a_failed_flush_after_an_ingest_installs_keeps_those_memtables_readable() {
    let dir = TempDir::new().unwrap();
    let staging = TempDir::new().unwrap();
    // The ingest's table is the first SST open and pauses; the second
    // is its flush of the memtable sealed meanwhile, and fails.
    let env = NthSstOpen::new(dir.path(), 1, 2);
    let opts = Options {
        env: env.clone(),
        write_buffer_size: 4 * 1024,
        ..Options::default()
    };
    let db = Arc::new(Db::open(dir.path(), opts.clone()).unwrap());

    let ingest_path = build_ingest_file(staging.path(), &opts, b"k", b"new");
    let ingest = {
        let db = Arc::clone(&db);
        std::thread::spawn(move || {
            db.ingest_external_files(&[ingest_path], IngestOptions::default())
        })
    };
    env.wait_paused(Duration::from_secs(60));

    let writer = {
        let db = Arc::clone(&db);
        std::thread::spawn(move || write_past_one_rotation(&db, "f"))
    };
    let writer_done = wait_finished(&writer, WRITE_DEADLINE);
    let frozen_while_paused = frozen_bytes(&db);
    env.release();
    let ingested = ingest.join().unwrap();
    let written = writer.join().unwrap();

    assert!(
        writer_done,
        "a write that filled the memtable did not return while an ingest was writing its table"
    );
    written.unwrap();
    assert!(
        frozen_while_paused > 0,
        "the writes never rotated the memtable, so nothing here was exercised"
    );
    let err = ingested.unwrap_err();
    assert!(
        err.to_string().contains("injected table open failure"),
        "unexpected ingest error: {err}"
    );

    assert_eq!(
        db.get(b"k").unwrap(),
        Some(b"new".to_vec()),
        "the ingested file must stay installed"
    );
    assert!(
        frozen_bytes(&db) > 0,
        "the memtable whose flush failed must stay frozen"
    );
    assert_eq!(db.get(b"f0").unwrap(), Some(vec![0u8; 1024]));

    db.flush().unwrap();
    assert_eq!(frozen_bytes(&db), 0);

    let before = db.latest_sequence();
    drop(db);
    let db = Db::open(
        dir.path(),
        Options {
            env: NthSstOpen::new(dir.path(), 0, 0),
            ..opts
        },
    )
    .unwrap();
    let mut batch = WriteBatch::new();
    batch.put(b"z", b"v");
    let seq = db.write_sequenced(batch).unwrap();
    assert!(
        seq > before,
        "reopened sequence {seq} did not exceed {before}"
    );
    assert_eq!(db.get(b"k").unwrap(), Some(b"new".to_vec()));
    assert_eq!(db.get(b"f0").unwrap(), Some(vec![0u8; 1024]));
}

/// `compact_range` during an ingest waits for it, then flushes its own
/// memtable and reports that flush's failure. It takes the compaction
/// gate, which an ingest holds for its whole call, before it seals
/// anything, so it never leaves its memtable to an ingest's flush whose
/// failure it would not see.
#[test]
fn compact_range_during_an_ingest_reports_a_failed_flush_of_its_memtable() {
    let dir = TempDir::new().unwrap();
    let staging = TempDir::new().unwrap();
    // The ingest's table is the first SST open and pauses; the second
    // fails.
    let env = NthSstOpen::new(dir.path(), 1, 2);
    let opts = Options {
        env: env.clone(),
        ..Options::default()
    };
    let db = Arc::new(Db::open(dir.path(), opts.clone()).unwrap());

    let ingest_path = build_ingest_file(staging.path(), &opts, b"k", b"new");
    let ingest = {
        let db = Arc::clone(&db);
        std::thread::spawn(move || {
            db.ingest_external_files(&[ingest_path], IngestOptions::default())
        })
    };
    env.wait_paused(Duration::from_secs(60));

    // A write during the ingest, so `compact_range` has a memtable to
    // flush.
    let put = {
        let db = Arc::clone(&db);
        std::thread::spawn(move || db.put(b"k", b"v2"))
    };
    if !wait_finished(&put, WRITE_DEADLINE) {
        env.release();
        let _ = ingest.join();
        let _ = put.join();
        panic!("a commit did not complete while the ingest was paused");
    }
    put.join().unwrap().unwrap();

    let compact = {
        let db = Arc::clone(&db);
        std::thread::spawn(move || db.compact_range(None, None))
    };
    // A `compact_range` that sealed before taking the gate would show
    // its memtable in the frozen list here: give it the time to.
    wait_until(RELEASE_DEADLINE, || frozen_bytes(&db) > 0);
    env.release();
    let ingested = ingest.join().unwrap();
    let compacted = compact.join().unwrap();

    ingested.unwrap();
    let err = compacted.unwrap_err();
    assert!(
        err.to_string().contains("injected table open failure"),
        "unexpected compact_range error: {err}"
    );

    // The memtable whose flush failed is still frozen, and still read.
    assert_eq!(db.get(b"k").unwrap(), Some(b"v2".to_vec()));
    db.flush().unwrap();
    assert_eq!(frozen_bytes(&db), 0);
    assert_eq!(db.get(b"k").unwrap(), Some(b"v2".to_vec()));
}
