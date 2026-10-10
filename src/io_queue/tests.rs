//! What the unit table holds: a unit lives only while some queue owes its
//! read, so a finished read, a close and a dropped queue each leave the table
//! empty. A unit whose reopen found no open-file slot stays in it, parked,
//! until a freed slot sends it back to run (D60).

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::task::{Wake, Waker};

use crate::engine::block_cache::BlockCache;
use crate::engine::io::scope;
use crate::engine::io::unit::{Ran, UnitKey, Work};
use crate::env::open_file_limit::slots::SlotWaiter;
use crate::{Db, Error, IoBudget, IoWait, Options, ReadMode, WouldBlock};

/// A database whose keys all live in tables, reopened with a cold cache.
fn cold() -> (tempfile::TempDir, Db) {
    let dir = tempfile::TempDir::new().unwrap();
    let opts = || Options::default().block_size(256);
    {
        let db = Db::open(dir.path(), opts()).unwrap();
        for i in 0..2_000u32 {
            db.put(&key(i), format!("value-{i}").as_bytes()).unwrap();
        }
        db.flush().unwrap();
        db.close().unwrap();
    }
    let db = Db::open(dir.path(), opts()).unwrap();
    (dir, db)
}

fn key(i: u32) -> Vec<u8> {
    format!("k{i:05}").into_bytes()
}

fn missed(read: crate::Result<Option<Vec<u8>>>) {
    assert!(
        matches!(read, Err(Error::WouldBlock(WouldBlock::Io(_)))),
        "{read:?}"
    );
}

#[test]
fn a_finished_read_leaves_no_unit_behind() {
    let (_dir, db) = cold();
    let mut queue = db.io_queue();
    let snapshot = db
        .snapshot()
        .with_read_mode(ReadMode::CacheOnly(queue.id()));
    missed(snapshot.get(&key(700)));
    missed(snapshot.get(&key(1_300)));
    assert_eq!(queue.runtime().units_in_flight(), 2);
    queue.poll(IoBudget::ALL);
    assert_eq!(queue.runtime().units_in_flight(), 0);
    assert_eq!(queue.pending_bytes(), 0);
}

#[test]
fn close_leaves_no_unit_behind() {
    let (_dir, db) = cold();
    let mut queue = db.io_queue();
    let snapshot = db
        .snapshot()
        .with_read_mode(ReadMode::CacheOnly(queue.id()));
    missed(snapshot.get(&key(700)));
    queue.poll(IoBudget::units(0));
    missed(snapshot.get(&key(1_300)));
    db.close().unwrap();
    assert_eq!(queue.runtime().units_in_flight(), 0);
    queue.poll(IoBudget::ALL);
    assert_eq!(queue.pending_bytes(), 0);
}

#[test]
fn a_dropped_queue_leaves_no_unit_behind() {
    let (_dir, db) = cold();
    let watcher = db.io_queue();
    let queue = db.io_queue();
    let snapshot = db
        .snapshot()
        .with_read_mode(ReadMode::CacheOnly(queue.id()));
    missed(snapshot.get(&key(700)));
    let mut queue = queue;
    queue.poll(IoBudget::units(0));
    missed(snapshot.get(&key(1_300)));
    drop(queue);
    assert_eq!(watcher.runtime().units_in_flight(), 0);
}

/// A read that checked the database open before close and misses after it,
/// the window the close gate shuts, answers `Closed` and leaves no unit; a
/// close that failed reopens the table to misses.
#[test]
fn a_miss_after_close_answers_closed_and_leaves_no_unit() {
    use crate::engine::io::unit::{UnitKey, Work};

    let (_dir, db) = cold();
    let queue = db.io_queue();
    let runtime = queue.runtime();
    let key = UnitKey {
        file_id: 1,
        offset: 0,
        guard: None,
    };
    let work =
        || -> std::io::Result<Work> { Ok(Box::new(|_| Err(std::io::Error::other("never read")))) };
    runtime.close();
    let Err(err) = runtime.miss(queue.id(), key, 1, work) else {
        panic!("a closed table answered a miss");
    };
    assert!(matches!(Error::from(err), Error::Closed));
    assert_eq!(runtime.units_in_flight(), 0);
    runtime.reopen();
    let Err(err) = runtime.miss(queue.id(), key, 1, work) else {
        panic!("a miss answered without a read");
    };
    assert!(matches!(Error::from(err), Error::WouldBlock(_)));
    assert_eq!(runtime.units_in_flight(), 1);
}

const PARKING_KEY: UnitKey = UnitKey {
    file_id: 1,
    offset: 0,
    guard: None,
};

/// A unit whose first run finds no open-file slot and parks, and whose
/// later runs read (and fail, which completes the read all the same),
/// counting its runs.
fn parking_work(runs: &Arc<AtomicUsize>) -> impl Fn() -> std::io::Result<Work> + '_ {
    move || {
        let runs = Arc::clone(runs);
        Ok(Box::new(move |_| {
            if runs.fetch_add(1, Ordering::SeqCst) == 0 {
                scope::note_parked();
                Err(std::io::Error::new(
                    std::io::ErrorKind::ResourceBusy,
                    "no open-file slot",
                ))
            } else {
                Err(std::io::Error::other("the device read"))
            }
        }))
    }
}

fn would_block(err: std::io::Error) -> IoWait {
    match Error::from(err) {
        Error::WouldBlock(WouldBlock::Io(wait)) => wait,
        other => panic!("expected WouldBlock, got {other:?}"),
    }
}

struct Wakes(AtomicUsize);

impl Wake for Wakes {
    fn wake(self: Arc<Self>) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}

/// A parked unit stays in the table and is not run again, however often
/// its owner polls, and an idle owner is not woken for it, until a slot
/// frees: that wakes the idle owner once, and its next poll runs the unit
/// and completes the read.
#[test]
fn a_parked_unit_runs_again_only_once_a_slot_frees() {
    let (_dir, db) = cold();
    let mut queue = db.io_queue();
    let runs = Arc::new(AtomicUsize::new(0));
    let Err(err) = queue
        .runtime()
        .miss(queue.id(), PARKING_KEY, 1, parking_work(&runs))
    else {
        panic!("a miss answered without a read");
    };
    let wait = would_block(err);
    let progress = queue.poll(IoBudget::ALL);
    assert_eq!(progress.completed, 0);
    assert!(progress.more_pending);
    assert!(!wait.is_ready());
    assert_eq!(runs.load(Ordering::SeqCst), 1);
    let unit = queue
        .runtime()
        .unit(&PARKING_KEY)
        .expect("a parked unit stays in the table");
    assert!(unit.is_parked());
    queue.poll(IoBudget::ALL);
    assert_eq!(
        runs.load(Ordering::SeqCst),
        1,
        "a parked unit waits for a slot"
    );
    let wakes = Arc::new(Wakes(AtomicUsize::new(0)));
    queue.idle_waker(&Waker::from(Arc::clone(&wakes)));
    assert_eq!(
        wakes.0.load(Ordering::SeqCst),
        0,
        "nothing to run: the owner idles"
    );

    queue.shared().slot_freed();
    assert_eq!(
        wakes.0.load(Ordering::SeqCst),
        1,
        "the freed slot woke the idle owner"
    );
    let progress = queue.poll(IoBudget::ALL);
    assert_eq!(progress.completed, 1);
    assert!(!progress.more_pending);
    assert!(wait.is_ready());
    assert_eq!(runs.load(Ordering::SeqCst), 2);
    assert_eq!(queue.runtime().units_in_flight(), 0);
    assert_eq!(queue.pending_bytes(), 0);
}

/// Close sweeps the table while a poll holds a unit claimed; the poll's run
/// then parks it. The run sees close's mark and lets the unit go itself, so
/// no parked unit outlives close.
#[test]
fn a_park_that_lands_after_close_swept_is_released_by_its_run() {
    let (_dir, db) = cold();
    let mut queue = db.io_queue();
    let runs = Arc::new(AtomicUsize::new(0));
    let Err(err) = queue
        .runtime()
        .miss(queue.id(), PARKING_KEY, 1, parking_work(&runs))
    else {
        panic!("a miss answered without a read");
    };
    let wait = would_block(err);
    {
        let runtime = queue.runtime();
        let unit = runtime.unit(&PARKING_KEY).unwrap();
        assert!(unit.claim(), "a poll claimed it before close swept");
        runtime.close();
        assert_eq!(
            runtime.units_in_flight(),
            1,
            "the sweep leaves a claimed unit to its runner"
        );
        let ran = runtime.run(&unit, queue.shared(), &BlockCache::new(0));
        assert_eq!(
            ran,
            Ran::Finished,
            "the run parked after close, and let the unit go"
        );
        assert!(unit.is_done());
        assert_eq!(runtime.units_in_flight(), 0);
    }
    assert_eq!(queue.poll(IoBudget::ALL).completed, 1);
    assert!(wait.is_ready());
    queue.runtime().reopen();
}
