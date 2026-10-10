//! What the unit table holds: a unit lives only while some queue owes its
//! read, so a finished read, a close and a dropped queue each leave the table
//! empty.

use crate::{Db, Error, IoBudget, Options, ReadMode, WouldBlock};

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

/// A job a queue owns is listed until it lands, run or settled: the step a
/// write leaves owing is on the table until the queue's owner polls.
#[test]
fn a_job_a_queue_owns_is_listed_until_it_lands() {
    let dir = tempfile::TempDir::new().unwrap();
    let db = Db::open(
        dir.path(),
        Options::default()
            .max_background_compactions(0)
            .write_buffer_size(4 * 1024),
    )
    .unwrap();
    let mut queue = db.io_queue();
    let runtime = queue.runtime();
    let mut seen = false;
    for i in 0..64u32 {
        db.put(&key(i), &[7u8; 512]).unwrap();
        seen |= runtime.jobs_in_flight() == 1;
    }
    assert!(
        seen,
        "a write that sealed a memtable left its flush on the queue"
    );
    assert!(
        runtime.jobs_in_flight() <= 1,
        "one owed job waits at a time"
    );
    while queue.poll(IoBudget::ALL).more_pending {}
    assert_eq!(queue.runtime().jobs_in_flight(), 0);
}

/// Close settles every job a queue owns before that queue polls again: the
/// job leaves the table at close, unrun, and the poll after it only delivers
/// the `Closed` the close decided.
#[test]
fn close_settles_a_job_a_queue_owns_before_its_poll() {
    let dir = tempfile::TempDir::new().unwrap();
    let db = Db::open(dir.path(), Options::default().max_background_compactions(0)).unwrap();
    db.put(b"a", b"1").unwrap();
    db.flush().unwrap();
    db.put(b"b", b"2").unwrap();
    db.flush().unwrap();
    let mut queue = db.io_queue();
    let runtime = queue.runtime();
    let job = db.compact_range(None, None);
    assert_eq!(runtime.jobs_in_flight(), 1, "the job waits for the poll");
    db.close().unwrap();
    assert_eq!(runtime.jobs_in_flight(), 0, "close settled it");
    assert!(!job.is_ready(), "the poll delivers it");
    queue.poll(IoBudget::ALL);
    assert!(matches!(job.wait(), Err(Error::Closed)));
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
