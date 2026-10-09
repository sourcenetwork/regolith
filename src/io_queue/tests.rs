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
