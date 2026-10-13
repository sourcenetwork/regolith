//! The log writeback lane: kicks while one is asked for coalesce into one,
//! a kick after it runs asks again, shutdown joins the thread, and a
//! database with a worker hands its active log to the host's writeback as
//! it fills (E46).

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, mpsc};
use std::time::{Duration, Instant};

use tempfile::TempDir;

use super::LogWritebackLane;
use crate::env::std_env;
use crate::{Db, Options};

/// Wait, with a deadline and a bounded backoff, until `done` holds.
fn eventually(what: &str, done: impl Fn() -> bool) {
    let deadline = Instant::now() + Duration::from_secs(20);
    let mut pause = Duration::from_micros(50);
    while !done() {
        assert!(Instant::now() < deadline, "{what} did not happen in 20 s");
        std::thread::sleep(pause);
        pause = (pause * 2).min(Duration::from_millis(20));
    }
}

/// A lane whose hook counts its runs and waits for a release each time.
fn held_lane() -> (LogWritebackLane, Arc<AtomicUsize>, mpsc::Sender<()>) {
    let lane = LogWritebackLane::start(&*std_env()).unwrap();
    let runs = Arc::new(AtomicUsize::new(0));
    let (release, released) = mpsc::channel::<()>();
    let released = Mutex::new(released);
    let counted = Arc::clone(&runs);
    lane.set_hook(Box::new(move || {
        counted.fetch_add(1, Ordering::SeqCst);
        released.lock().unwrap().recv().unwrap();
    }));
    (lane, runs, release)
}

/// Kicks while one is asked for and not begun send nothing more: the run
/// that comes next covers them all.
#[test]
fn kicks_while_one_is_asked_for_coalesce() {
    let (lane, runs, release) = held_lane();
    let kick = lane.kicker();
    kick();
    eventually("the first run", || runs.load(Ordering::SeqCst) == 1);
    // The lane is inside the first run: the first of these asks again, the
    // rest find it asked.
    for _ in 0..100 {
        kick();
    }
    release.send(()).unwrap();
    eventually("the second run", || runs.load(Ordering::SeqCst) == 2);
    release.send(()).unwrap();
    eventually("the lane to take no more", || {
        !lane.asked.load(Ordering::SeqCst)
    });
    lane.shutdown();
    assert_eq!(runs.load(Ordering::SeqCst), 2, "100 kicks made one run");
}

/// Shutdown waits for a run under way, and a kick after it does nothing.
#[test]
fn shutdown_joins_the_lane_and_later_kicks_do_nothing() {
    let (lane, runs, release) = held_lane();
    let kick = lane.kicker();
    kick();
    eventually("the run", || runs.load(Ordering::SeqCst) == 1);
    release.send(()).unwrap();
    lane.shutdown();
    kick();
    lane.shutdown();
    assert_eq!(runs.load(Ordering::SeqCst), 1);
}

/// How far `db`'s active log was handed to the host's writeback.
fn handed(db: &Db) -> u64 {
    db.engine()
        .pipeline_state()
        .expect("a read-write database has a pipeline")
        .after
        .log
        .handed()
}

/// With a worker, the lane hands the active log to the host's writeback a
/// multiple of an eighth of the write buffer at a time, and never more
/// than the records written.
#[cfg(target_os = "linux")]
#[test]
fn a_database_with_a_worker_hands_its_log_over_as_it_fills() {
    let dir = TempDir::new().unwrap();
    let options = Options::default()
        .write_buffer_size(8 << 20)
        .max_background_compactions(1);
    let db = Db::open(dir.path(), options).unwrap();
    // About 3.2 MiB of log, past three multiples of 1 MiB.
    for i in 0..3_000u32 {
        db.put(&i.to_be_bytes(), &[9; 1100]).unwrap();
    }
    eventually("the lane's hand-over", || handed(&db) == 3 << 20);
    db.close().unwrap();
}

/// A database with no worker starts no lane, and its log is handed over to
/// nobody: the seal syncs it whole, as before.
#[test]
fn a_database_with_no_worker_starts_no_lane() {
    let dir = TempDir::new().unwrap();
    let options = Options::default()
        .write_buffer_size(8 << 20)
        .max_background_compactions(0);
    let db = Db::open(dir.path(), options).unwrap();
    assert!(db.engine().log_writeback.is_none());
    for i in 0..3_000u32 {
        db.put(&i.to_be_bytes(), &[9; 1100]).unwrap();
    }
    assert_eq!(handed(&db), 0);
    db.close().unwrap();
}
