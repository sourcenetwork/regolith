//! A write a stall stopped is told when the engine fails (E35).
//!
//! With a worker, a stopped write waits for the worker to relieve the stop
//! (`wait_for_write_capacity_slow`, `wait_out_stop`). An engine that latched
//! a log failure takes no write again, so a write waiting for the stop to
//! clear waits for nothing, and for ever where the worker cannot clear it.
//! So the latch wakes the waiters and the wait reads the latch on every
//! wake: the stopped write gets the error a fresh write gets. Background
//! work that starts failing reaches a waiting write the same way: the failed
//! pass wakes the waiters, and each returns that failure.
//!
//! Each test stops a write first and fails the engine second, and none
//! sleeps: a stopped write is seen through its registration on the stall
//! signal, a compaction is held at its start by a listener, and a blocked
//! thread is watched through a channel with a deadline.

use std::io;
use std::path::Path;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, mpsc};
use std::time::{Duration, Instant};

use tempfile::TempDir;

use crate::column_family::{DEFAULT_CF_ID, prefix_key};
use crate::engine::wal_rotation_tests::SyncFault;
use crate::engine::{DurabilityMode, EngineOptions, RegolithEngine};
use crate::env::{
    Capabilities, DirEntry, Env, FileLock, FileMeta, JoinHandle, ReadFile, StdEnv, WriteFile,
    WriteMode,
};
use crate::event_listener::{CompactionJobInfo, EventListener};
use crate::{Error, WriteBatchOp};

/// How long a test waits for another thread before it calls the wait a hang.
const DEADLINE: Duration = Duration::from_secs(60);

/// One 1 KiB put, applied below the stall admission as an admitted write is.
fn fill(engine: &RegolithEngine, key: &[u8]) -> io::Result<u64> {
    let ops = vec![WriteBatchOp::Put {
        key: prefix_key(DEFAULT_CF_ID, key),
        value: vec![7u8; 1024],
    }];
    engine.apply_batch(ops, DurabilityMode::Eventual, false)
}

/// Poll `done` with a deadline and bounded backoff.
fn wait_until(what: &str, mut done: impl FnMut() -> bool) {
    let deadline = Instant::now() + DEADLINE;
    let mut backoff = Duration::from_micros(100);
    while !done() {
        assert!(Instant::now() < deadline, "timed out waiting for {what}");
        std::thread::sleep(backoff);
        backoff = (backoff * 2).min(Duration::from_millis(10));
    }
}

/// Run a write's admission on another thread; the channel says what it is
/// told, whenever that is.
fn admission(engine: &Arc<RegolithEngine>) -> mpsc::Receiver<Result<u64, Error>> {
    let (told, when_told) = mpsc::channel();
    let writer = Arc::clone(engine);
    std::thread::spawn(move || {
        let _ = told.send(writer.wait_for_write_capacity(false));
    });
    when_told
}

/// A write the stall stops now: its admission runs on another thread, and
/// this returns once that thread waits in the stall.
fn stopped_write(engine: &Arc<RegolithEngine>) -> mpsc::Receiver<Result<u64, Error>> {
    // A registration an earlier wait left behind would pass for this one.
    engine.stall_signal.notify_all();
    assert!(engine.stall_signal.waiters.is_empty());
    let when_told = admission(engine);
    wait_until("the write to wait in the stall", || {
        !engine.stall_signal.waiters.is_empty()
    });
    when_told
}

/// What a write that arrives now is told at its admission, which must not
/// take a wait to say.
fn fresh_admission_error(engine: &Arc<RegolithEngine>) -> String {
    admission(engine)
        .recv_timeout(DEADLINE)
        .expect("a write that arrived at a failed engine waited in the stall")
        .expect_err("a failed engine admits no write")
        .to_string()
}

/// A worker, one L0 table at the stop, and a compaction trigger the worker
/// never reaches: stopped writes wait for a relief that does not come.
fn stopped_engine_with_a_worker() -> (TempDir, Arc<RegolithEngine>) {
    let dir = TempDir::new().unwrap();
    let engine = RegolithEngine::open(
        dir.path(),
        EngineOptions {
            max_background_compactions: 1,
            level0_stop_writes_trigger: 1,
            l0_compaction_trigger: 100,
            ..EngineOptions::default()
        },
    )
    .unwrap();
    fill(&engine, b"k").unwrap();
    engine.flush_active_memtable().unwrap();
    assert!(
        matches!(engine.stall_state(), Some((_, true))),
        "setup: one L0 table stops writes"
    );
    (dir, engine)
}

/// Latch the engine as a flush whose log cannot be synced does.
fn latch_through_a_flush(dir: &TempDir, engine: &RegolithEngine) -> SyncFault {
    fill(engine, b"unflushed").unwrap();
    let fault = SyncFault::arm(dir);
    let err = engine
        .flush_active_memtable()
        .expect_err("the flush seals a log it cannot sync");
    assert!(
        err.to_string().contains("injected WAL sync failure"),
        "{err}"
    );
    fault
}

/// What a write is told once it is past the admission of a latched engine.
fn latched_write_error(engine: &RegolithEngine) -> String {
    let told = Error::from(fill(engine, b"fresh").expect_err("a latched engine takes no write"))
        .to_string();
    assert!(told.contains("unknown state"), "{told}");
    told
}

/// A write waits for the worker to relieve the stop, the engine latches,
/// and the write is told the latch at once, not when the stop clears, which
/// here is never.
#[test]
fn a_latched_engine_tells_the_write_waiting_for_the_worker() {
    let (dir, engine) = stopped_engine_with_a_worker();
    let stopped = stopped_write(&engine);
    let _fault = latch_through_a_flush(&dir, &engine);
    let told = stopped
        .recv_timeout(DEADLINE)
        .expect("the engine latched and the stopped write still waits")
        .expect_err("a latched engine admits no write")
        .to_string();
    assert_eq!(told, latched_write_error(&engine));
}

/// A write that arrives at an engine both stopped and latched is refused at
/// its admission: it does not wait for a stop whose end would only show it
/// the latch.
#[test]
fn a_write_that_arrives_at_a_latched_and_stopped_engine_does_not_wait() {
    let (dir, engine) = stopped_engine_with_a_worker();
    let _fault = latch_through_a_flush(&dir, &engine);
    assert_eq!(fresh_admission_error(&engine), latched_write_error(&engine));
}

/// The engine latches for a second reason, a panic in a caller's callback
/// inside the commit's ordered step, and that goes through the same latch:
/// a write waiting for the worker is told that one too, as a fresh write is.
#[test]
fn a_callback_panic_latch_tells_the_write_waiting_for_the_worker() {
    let (_dir, engine) = stopped_engine_with_a_worker();
    let stopped = stopped_write(&engine);
    engine.latch_callback_panic("MergeOperator");
    let told = stopped
        .recv_timeout(DEADLINE)
        .expect("the engine latched and the stopped write still waits")
        .expect_err("a latched engine admits no write");
    assert!(
        matches!(
            told,
            Error::CallbackPanicked {
                callback: "MergeOperator",
                latched: true
            }
        ),
        "{told:?}"
    );
    let fresh = Error::from(fill(&engine, b"fresh").expect_err("a latched engine takes no write"));
    assert_eq!(told.to_string(), fresh.to_string());
    assert_eq!(told.to_string(), fresh_admission_error(&engine));
}

/// Delegates to the standard `Env`, and refuses to create a table once told
/// to.
#[derive(Debug, Default)]
struct RefusingTables {
    inner: StdEnv,
    refuse: AtomicBool,
}

impl Env for RefusingTables {
    fn open_write(&self, path: &Path, mode: WriteMode) -> io::Result<Box<dyn WriteFile>> {
        if self.refuse.load(Ordering::Acquire) && path.extension().is_some_and(|ext| ext == "sst") {
            return Err(io::Error::other("injected table creation failure"));
        }
        self.inner.open_write(path, mode)
    }
    fn create_dir_all(&self, path: &Path) -> io::Result<()> {
        self.inner.create_dir_all(path)
    }
    fn read_dir(&self, path: &Path) -> io::Result<Vec<DirEntry>> {
        self.inner.read_dir(path)
    }
    fn open_read(&self, path: &Path) -> io::Result<Box<dyn ReadFile>> {
        self.inner.open_read(path)
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
    fn hard_link(&self, from: &Path, to: &Path) -> io::Result<()> {
        self.inner.hard_link(from, to)
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
    fn sleep(&self, duration: Duration) {
        self.inner.sleep(duration)
    }
}

/// Holds the first compaction at its start until told to go on, and says
/// when it began.
struct HeldCompaction {
    held: AtomicBool,
    began: Mutex<mpsc::Sender<()>>,
    go_on: Mutex<mpsc::Receiver<()>>,
}

impl EventListener for HeldCompaction {
    fn on_compaction_begin(&self, _: &CompactionJobInfo) {
        if !self.held.swap(true, Ordering::AcqRel) {
            let _ = self.began.lock().unwrap().send(());
            // Bounded: a test that never says go on fails on its own wait.
            let _ = self.go_on.lock().unwrap().recv_timeout(DEADLINE);
        }
    }
}

/// Background work that fails, where the latch tests have an engine that
/// failed: a write waits for the worker's compaction to relieve the stop,
/// that compaction fails, and the waiting write is told the failure a write
/// arriving afterwards is told, not left to wait for a retry.
#[test]
fn a_compaction_that_fails_tells_the_write_waiting_for_it() {
    let dir = TempDir::new().unwrap();
    let env = Arc::new(RefusingTables::default());
    let (began, when_began) = mpsc::channel();
    let (go_on, when_go_on) = mpsc::channel();
    let engine = RegolithEngine::open(
        dir.path(),
        EngineOptions {
            env: Arc::clone(&env) as Arc<dyn Env>,
            max_background_compactions: 1,
            level0_stop_writes_trigger: 2,
            l0_compaction_trigger: 2,
            listeners: vec![Arc::new(HeldCompaction {
                held: AtomicBool::new(false),
                began: Mutex::new(began),
                go_on: Mutex::new(when_go_on),
            })],
            ..EngineOptions::default()
        },
    )
    .unwrap();
    // Two L0 tables: the stop, and the compaction that would relieve it.
    for key in [&b"a"[..], b"b"] {
        fill(&engine, key).unwrap();
        engine.flush_active_memtable().unwrap();
    }
    when_began
        .recv_timeout(DEADLINE)
        .expect("the worker began the compaction two L0 tables call for");
    assert!(
        matches!(engine.stall_state(), Some((_, true))),
        "setup: two L0 tables stop writes while the compaction is held"
    );

    let stopped = stopped_write(&engine);
    env.refuse.store(true, Ordering::Release);
    go_on.send(()).unwrap();

    let told = stopped
        .recv_timeout(DEADLINE)
        .expect("the compaction failed and the stopped write still waits");
    match &told {
        Err(Error::BackgroundFailed { job, .. }) => assert_eq!(*job, "compaction"),
        other => panic!("expected the compaction's failure, got {other:?}"),
    }
    assert_eq!(
        told.unwrap_err().to_string(),
        fresh_admission_error(&engine)
    );
}
