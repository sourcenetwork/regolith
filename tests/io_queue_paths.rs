//! Every read path through a `CacheOnly` handle (plan 4.10, D53).
//!
//! On a cold block cache each one returns `WouldBlock` without touching the
//! device: no SSTable read and no SSTable open, counted at the `Env`. Once
//! its owner polls the queue the wait names, the read run again returns
//! exactly what a `Blocking` read returns. Each layout below moves a
//! different read onto the device: data blocks, cached indexes and filters,
//! partitioned index leaves, files reopened under `max_open_files`, and a
//! disabled block cache, where only what landed for the queue carries the
//! read.
#![cfg(not(target_arch = "wasm32"))]

mod common;

use std::sync::Arc;

use common::device_env::{Device, DeviceEnv};
use common::parted::{self, Parted};
use regolith::{
    Db, Error, IoBudget, IoQueue, IsolationLevel, OptimisticTransactionDb, Options, ReadMode,
    Snapshot, TransactionError, TxnOptions, WouldBlock,
};
use tempfile::TempDir;

/// Keys written, `k000`..`k399`. Opening a database reads the first block of
/// every table (the column-family registry sorts first), so the reads below
/// stay among the keys in the middle, which no open has cached.
const KEYS: usize = 400;
/// The key the fill deletes, and merges nothing into after.
const DELETED: usize = 157;
/// More `WouldBlock`s than any one read here can meet: a read past it never
/// finished, which fails the test rather than spinning.
const MOST_WAITS: usize = 10_000;

#[derive(Clone, Copy, Debug)]
enum Layout {
    /// Pinned indexes and filters: only data blocks are read.
    Pinned,
    /// Flat indexes and filters through the block cache.
    CachedMeta,
    /// Partitioned indexes, leaves through the block cache.
    Partitioned,
    /// One descriptor kept open, so reads reopen files.
    FewFiles,
    /// No block cache: a read finds its block only where it landed.
    NoCache,
}

const LAYOUTS: [Layout; 5] = [
    Layout::Pinned,
    Layout::CachedMeta,
    Layout::Partitioned,
    Layout::FewFiles,
    Layout::NoCache,
];

fn options(layout: Layout, env: Arc<DeviceEnv>) -> Options {
    let base = Options::default()
        .env(env)
        .block_size(256)
        .metadata_block_size(256)
        .merge_operator(Some(Arc::new(Parted)));
    match layout {
        Layout::Pinned => base,
        Layout::CachedMeta => base.cache_index_and_filter_blocks(true),
        Layout::Partitioned => base
            .partitioned_index(true)
            .cache_index_and_filter_blocks(true),
        Layout::FewFiles => base.max_open_files(1),
        Layout::NoCache => base.block_cache_size(0),
    }
}

/// [`options`] with no merge operator.
fn options_without_merges(layout: Layout, env: Arc<DeviceEnv>) -> Options {
    let base = Options::default()
        .env(env)
        .block_size(256)
        .metadata_block_size(256);
    match layout {
        Layout::Pinned => base,
        Layout::CachedMeta => base.cache_index_and_filter_blocks(true),
        Layout::Partitioned => base
            .partitioned_index(true)
            .cache_index_and_filter_blocks(true),
        Layout::FewFiles => base.max_open_files(1),
        Layout::NoCache => base.block_cache_size(0),
    }
}

fn key(i: usize) -> Vec<u8> {
    format!("k{i:03}").into_bytes()
}

/// Write every key into tables: several tables, merge operands in newer
/// tables over bases in older ones, and a deleted key.
fn fill(db: &Db) {
    for i in 0..KEYS {
        db.put(&key(i), &parted::value([i as u64, 0, 0])).unwrap();
    }
    db.flush().unwrap();
    for i in (0..KEYS).step_by(3) {
        db.merge(&key(i), &parted::add(1, 7)).unwrap();
    }
    db.delete(&key(DELETED)).unwrap();
    db.flush().unwrap();
    for i in (0..KEYS).step_by(5) {
        db.merge(&key(i), &parted::add(2, 1)).unwrap();
    }
    db.flush().unwrap();
}

/// A filled database reopened so the block cache is cold.
fn cold(layout: Layout) -> (TempDir, OptimisticTransactionDb, Arc<Device>) {
    let dir = TempDir::new().unwrap();
    let (env, device) = DeviceEnv::new();
    {
        let db =
            OptimisticTransactionDb::open(dir.path(), options(layout, Arc::clone(&env))).unwrap();
        fill(db.db());
        db.db().close().unwrap();
    }
    let db = OptimisticTransactionDb::open(dir.path(), options(layout, env)).unwrap();
    (dir, db, device)
}

/// Run `read` until it stops returning `WouldBlock`, polling `queue` after
/// each wait. Asserts the read never touched the device itself, and returns
/// its answer and how many times it waited.
fn drive<T>(
    device: &Device,
    queue: &mut IoQueue,
    mut read: impl FnMut() -> Result<T, Error>,
) -> (T, usize) {
    let mut waits = 0;
    loop {
        let before = device.touches();
        let outcome = read();
        assert_eq!(
            device.touches(),
            before,
            "a CacheOnly read touched the device itself"
        );
        match outcome {
            Ok(answer) => return (answer, waits),
            Err(Error::WouldBlock(WouldBlock::Io(wait))) => {
                waits += 1;
                assert!(waits < MOST_WAITS, "the read never finished");
                assert_eq!(wait.queue(), queue.id(), "a miss went to another queue");
                assert!(!wait.is_ready());
                queue.poll(IoBudget::ALL);
                assert!(wait.is_ready(), "the owner's poll completes its wait");
            }
            Err(other) => panic!("the read failed: {other}"),
        }
    }
}

/// A transaction's error as a plain one, so [`drive`] serves both.
fn plain(err: TransactionError) -> Error {
    match err {
        TransactionError::WouldBlock(wait) => Error::WouldBlock(wait),
        TransactionError::Engine(err) => err,
        other => panic!("the read failed: {other}"),
    }
}

type SnapshotRead = fn(&Db, &Snapshot) -> Result<String, Error>;

/// Every point and range read a snapshot offers, each answer rendered for
/// comparison.
fn snapshot_reads() -> Vec<(&'static str, SnapshotRead)> {
    vec![
        ("get", |_, s| s.get(&key(109)).map(|v| format!("{v:?}"))),
        ("get of a merged key", |_, s| {
            s.get(&key(115)).map(|v| format!("{v:?}"))
        }),
        ("get of a deleted key", |_, s| {
            s.get(&key(DELETED)).map(|v| format!("{v:?}"))
        }),
        ("get_slice", |_, s| {
            s.get_slice(&key(140))
                .map(|v| format!("{:?}", v.map(|v| v.to_vec())))
        }),
        ("get_slice_cf", |db, s| {
            s.get_slice_cf(&db.default_cf(), &key(141))
                .map(|v| format!("{:?}", v.map(|v| v.to_vec())))
        }),
        ("has", |_, s| s.has(&key(177)).map(|v| format!("{v:?}"))),
        ("has_cf", |db, s| {
            s.has_cf(&db.default_cf(), &key(178))
                .map(|v| format!("{v:?}"))
        }),
        ("get_size", |_, s| {
            s.get_size(&key(180)).map(|v| format!("{v:?}"))
        }),
        ("get_size_cf", |db, s| {
            s.get_size_cf(&db.default_cf(), &key(182))
                .map(|v| format!("{v:?}"))
        }),
        ("multi_get", |_, s| {
            s.multi_get(&[&key(101), &key(160), &key(DELETED), &key(219)])
                .map(|v| format!("{v:?}"))
        }),
        ("multi_get_cf", |db, s| {
            s.multi_get_cf(&db.default_cf(), &[&key(102), &key(161)])
                .map(|v| format!("{v:?}"))
        }),
        ("scan", |_, s| {
            s.scan(Some(&key(110)), Some(&key(170)))
                .map(|v| format!("{v:?}"))
        }),
        ("scan_cf", |db, s| {
            s.scan_cf(&db.default_cf(), None, None)
                .map(|v| format!("{v:?}"))
        }),
        ("scan_page", |_, s| {
            s.scan_page(Some(&key(130)), None, 25)
                .map(|v| format!("{v:?}"))
        }),
        ("scan_page_cf", |db, s| {
            s.scan_page_cf(&db.default_cf(), None, Some(&key(190)), 40)
                .map(|v| format!("{v:?}"))
        }),
    ]
}

#[test]
fn every_snapshot_read_waits_on_a_cold_cache_then_answers_as_blocking() {
    for layout in LAYOUTS {
        for (name, read) in snapshot_reads() {
            let (_dir, db, device) = cold(layout);
            let db = db.db();
            let mut queue = db.io_queue();
            let snapshot = db
                .snapshot()
                .with_read_mode(ReadMode::CacheOnly(queue.id()));
            let (answer, waits) = drive(&device, &mut queue, || read(db, &snapshot));
            assert!(waits > 0, "{layout:?} {name}: a cold read must wait");
            assert_eq!(
                answer,
                read(db, &db.snapshot()).unwrap(),
                "{layout:?} {name}"
            );
        }
    }
}

/// A filled database with no merge operator, which a size guard refuses,
/// reopened cold.
fn cold_plain(layout: Layout) -> (TempDir, Db, Arc<Device>) {
    let dir = TempDir::new().unwrap();
    let (env, device) = DeviceEnv::new();
    {
        let db = Db::open(dir.path(), options_without_merges(layout, Arc::clone(&env))).unwrap();
        for i in 0..KEYS {
            db.put(&key(i), &parted::value([i as u64, 0, 0])).unwrap();
        }
        db.flush().unwrap();
        db.close().unwrap();
    }
    let db = Db::open(dir.path(), options_without_merges(layout, env)).unwrap();
    (dir, db, device)
}

#[test]
fn a_size_guard_answers_through_the_queue_as_it_does_blocking() {
    for layout in LAYOUTS {
        let (_dir, db, device) = cold_plain(layout);
        let mut queue = db.io_queue();
        let snapshot = db
            .snapshot()
            .with_read_mode(ReadMode::CacheOnly(queue.id()));
        let (fits, waits) = drive(&device, &mut queue, || {
            snapshot.get_size_with_limit(&key(133), 1 << 20)
        });
        assert!(waits > 0, "{layout:?}");
        assert_eq!(fits, db.snapshot().get_size(&key(133)).unwrap());

        // Too small for any block: the read the queue ran refused it, and the
        // read run again reports that refusal.
        let (_dir, db, device) = cold_plain(layout);
        let mut queue = db.io_queue();
        let snapshot = db
            .snapshot()
            .with_read_mode(ReadMode::CacheOnly(queue.id()));
        let mut outcome = None;
        for _ in 0..MOST_WAITS {
            let before = device.touches();
            let read = snapshot.get_size_with_limit(&key(133), 8);
            assert_eq!(device.touches(), before);
            match read {
                Err(Error::WouldBlock(_)) => {
                    queue.poll(IoBudget::ALL);
                }
                other => {
                    outcome = Some(other);
                    break;
                }
            }
        }
        assert!(
            matches!(outcome, Some(Err(Error::DataBlockLimitExceeded { .. }))),
            "{layout:?}: {outcome:?}"
        );
        assert!(matches!(
            db.snapshot().get_size_with_limit(&key(133), 8),
            Err(Error::DataBlockLimitExceeded { .. })
        ));
    }
}

type TxnRead = fn(&regolith::Transaction) -> Result<String, TransactionError>;

fn transaction_reads() -> Vec<(&'static str, TxnRead)> {
    vec![
        ("get", |t| t.get(&key(112)).map(|v| format!("{v:?}"))),
        ("get_slice", |t| {
            t.get_slice(&key(145))
                .map(|v| format!("{:?}", v.map(|v| v.to_vec())))
        }),
        ("get_for_update", |t| {
            t.get_for_update(&key(130)).map(|v| format!("{v:?}"))
        }),
        ("get_parts", |t| {
            t.get_parts(&key(160), &[1])
                .map(|v| format!("{:?}", v.map(|v| v.to_vec())))
        }),
        ("get of a key the transaction merged into", |t| {
            t.get(&key(121)).map(|v| format!("{v:?}"))
        }),
    ]
}

#[test]
fn every_transaction_read_waits_then_answers_as_blocking() {
    for layout in LAYOUTS {
        for (name, read) in transaction_reads() {
            let (_dir, db, device) = cold(layout);
            let mut queue = db.db().io_queue();
            let opts = TxnOptions::new()
                .isolation(IsolationLevel::DefraLevel)
                .read_mode(ReadMode::CacheOnly(queue.id()));
            let txn = db.begin(&opts);
            assert_eq!(txn.read_mode(), ReadMode::CacheOnly(queue.id()));
            assert_eq!(txn.io_queue(), Some(queue.id()));
            txn.merge(&key(121), &parted::add(0, 100)).unwrap();
            let (answer, waits) = drive(&device, &mut queue, || read(&txn).map_err(plain));
            assert!(waits > 0, "{layout:?} {name}: a cold read must wait");
            let blocking = db.begin(&TxnOptions::new().isolation(IsolationLevel::DefraLevel));
            blocking.merge(&key(121), &parted::add(0, 100)).unwrap();
            assert_eq!(answer, read(&blocking).unwrap(), "{layout:?} {name}");
        }
    }
}

#[test]
fn a_blocking_handle_reads_the_device_as_before() {
    let (_dir, db, device) = cold(Layout::Pinned);
    let db = db.db();
    let before = device.reads();
    assert!(db.snapshot().get(&key(103)).unwrap().is_some());
    assert!(
        device.reads() > before,
        "a Blocking read reads the device itself"
    );
    let _queue = db.io_queue();
    let before = device.reads();
    assert!(db.snapshot().get(&key(170)).unwrap().is_some());
    assert!(
        device.reads() > before,
        "opening a queue leaves Blocking reads alone"
    );
}

#[test]
fn reads_inside_commit_read_the_device_and_prepare_can_wait() {
    let (_dir, db, device) = cold(Layout::Pinned);
    let mut queue = db.db().io_queue();
    let opts = TxnOptions::new().read_mode(ReadMode::CacheOnly(queue.id()));

    // `prepare` runs the callback in the transaction's mode: it waits.
    let mut txn = db.begin(&opts);
    txn.before_commit(|txn| {
        let found = txn.get(&key(222))?;
        txn.put(b"seen", &[u8::from(found.is_some())])
    });
    let before = device.touches();
    assert!(matches!(
        txn.prepare(),
        Err(TransactionError::WouldBlock(_))
    ));
    assert_eq!(device.touches(), before);
    // A callback that waited runs again from the start at the next prepare.
    let (_, waits) = drive(&device, &mut queue, || txn.prepare().map_err(plain));
    assert!(waits > 0);
    txn.commit().unwrap();
    assert_eq!(db.db().get(b"seen").unwrap(), Some(vec![1]));

    // `commit` does its own I/O: the callback's read blocks.
    let mut txn = db.begin(&opts);
    txn.before_commit(|txn| {
        let found = txn.get(&key(333))?;
        txn.put(b"seen", &[2 + u8::from(found.is_some())])
    });
    let before = device.reads();
    txn.commit().unwrap();
    assert!(
        device.reads() > before,
        "the read inside commit read the device"
    );
    assert_eq!(db.db().get(b"seen").unwrap(), Some(vec![3]));
}

#[test]
fn a_read_naming_a_dropped_queue_fails_loud() {
    let (_dir, db, _device) = cold(Layout::Pinned);
    let db = db.db();
    let queue = db.io_queue();
    let snapshot = db
        .snapshot()
        .with_read_mode(ReadMode::CacheOnly(queue.id()));
    drop(queue);
    assert!(matches!(
        snapshot.get(&key(201)),
        Err(Error::InvalidArgument(_))
    ));
}

#[test]
fn a_read_naming_another_databases_queue_fails_loud() {
    let (_dir, db, _device) = cold(Layout::Pinned);
    let (_other_dir, other, _) = cold(Layout::Pinned);
    let foreign = other.db().io_queue();
    let snapshot = db
        .db()
        .snapshot()
        .with_read_mode(ReadMode::CacheOnly(foreign.id()));
    assert!(matches!(
        snapshot.get(&key(201)),
        Err(Error::InvalidArgument(_))
    ));
}
