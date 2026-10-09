//! Where the Phase 6 packages meet, tested across them.
//!
//! - **Log retirement on every flush path** (#268 x #265). Group commit moved
//!   the flush off the commit path: the compaction worker flushes, a writer
//!   with no worker flushes after its commit returns, and a writer stopped by
//!   a stall flushes inside its bounded step. Each of them must record
//!   `min_wal_id` in the table's batch and retire the log through
//!   `RetiredLogs`, so a log whose removal failed is reported, retried, and
//!   never replayed above a newer table.
//! - **A restore and the retired logs** (#266's sealed backups x #268). A
//!   restored database holds what its backup holds: its MANIFEST records
//!   every log below the backup's next file id as in tables, so no log the
//!   restore target held is replayed into it.

mod common;

use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::Ordering;
use std::time::{Duration, Instant};

use common::faulty_env::{FaultyEnv, Refuse, logs};
use regolith::env::Env;
use regolith::{BackupEngine, Db, Options, Statistics, Ticker};
use tempfile::TempDir;

/// Bytes of filler each write carries, so a few writes fill a memtable.
const FILLER: usize = 1024;
/// The write buffer the flush tests run with.
const WRITE_BUFFER: usize = 8 * 1024;

/// The three threads that flush a sealed memtable.
#[derive(Clone, Copy, Debug)]
enum FlushPath {
    /// The compaction worker, woken by the seal.
    Worker,
    /// The writer whose commit sealed it, once that commit returned, on a
    /// database with no worker.
    AfterCommit,
    /// A writer stopped by a stall, inside the bounded step it runs before
    /// its own write, on a database with no worker.
    StallStep,
}

struct Fixture {
    dir: TempDir,
    env: Arc<FaultyEnv>,
    stats: Arc<Statistics>,
    path: FlushPath,
    filler: usize,
}

impl Fixture {
    fn new(path: FlushPath) -> Self {
        Self {
            dir: TempDir::new().unwrap(),
            env: Arc::new(FaultyEnv::default()),
            stats: Arc::new(Statistics::new()),
            path,
            filler: 0,
        }
    }

    fn options(&self) -> Options {
        let options = Options::default()
            .env(Arc::clone(&self.env) as Arc<dyn Env>)
            .statistics(Some(Arc::clone(&self.stats)))
            .write_buffer_size(WRITE_BUFFER);
        match self.path {
            FlushPath::Worker => options.max_background_compactions(1),
            FlushPath::AfterCommit => options.max_background_compactions(0),
            // With one table at L0 every write is slowed down, and a slowed
            // write with no worker first runs one bounded step: the flush of
            // the oldest frozen memtable when there is one. The compaction
            // trigger is out of reach, so the steps between flushes find
            // nothing to compact.
            FlushPath::StallStep => options
                .max_background_compactions(0)
                .level0_slowdown_writes_trigger(1)
                .l0_compaction_trigger(64),
        }
    }

    fn open(&self) -> Db {
        Db::open(self.dir.path(), self.options()).unwrap()
    }

    fn ticker(&self, ticker: Ticker) -> u64 {
        self.stats.get_ticker(ticker)
    }

    fn frozen_bytes(db: &Db) -> u64 {
        db.get_int_property("regolith.num-entries-imm-mem-tables")
            .unwrap()
    }

    fn fill(&mut self, db: &Db) {
        let key = format!("filler/{:06}", self.filler);
        self.filler += 1;
        db.put(key.as_bytes(), &[b'f'; FILLER]).unwrap();
    }

    /// Put `key = value`, then have this fixture's path flush the memtable
    /// holding it. Returns once that flush has run.
    fn put_and_flush(&mut self, db: &Db, key: &[u8], value: &[u8]) {
        let flushes = self.ticker(Ticker::FlushCount);
        db.put(key, value).unwrap();
        match self.path {
            FlushPath::Worker => {
                // Write until the memtable seals, then stop: a second seal
                // would have the rotation flush inline instead.
                while Self::frozen_bytes(db) == 0 && self.ticker(Ticker::FlushCount) == flushes {
                    self.fill(db);
                }
                wait_until("the worker flushes the sealed memtable", || {
                    self.ticker(Ticker::FlushCount) > flushes
                });
            }
            FlushPath::AfterCommit => {
                while self.ticker(Ticker::FlushCount) == flushes {
                    self.fill(db);
                }
            }
            FlushPath::StallStep => {
                // The flush the sealing writer owes fails, so the memtable is
                // still frozen when the next write runs its stall step.
                self.env.fail_tables(true);
                while Self::frozen_bytes(db) == 0 {
                    self.fill(db);
                }
                self.env.fail_tables(false);
                assert!(self.env.tables_refused.load(Ordering::SeqCst) > 0);
                assert_eq!(self.ticker(Ticker::FlushCount), flushes);
                self.fill(db);
                assert_eq!(
                    Self::frozen_bytes(db),
                    0,
                    "the stall step flushed the frozen memtable"
                );
            }
        }
        assert_eq!(
            self.ticker(Ticker::FlushCount),
            flushes + 1,
            "{:?}: exactly one flush ran",
            self.path
        );
    }
}

/// Poll `done` with a deadline and bounded backoff.
fn wait_until(what: &str, mut done: impl FnMut() -> bool) {
    let deadline = Instant::now() + Duration::from_secs(30);
    let mut backoff = Duration::from_micros(100);
    while !done() {
        assert!(Instant::now() < deadline, "timed out waiting until {what}");
        std::thread::sleep(backoff);
        backoff = (backoff * 2).min(Duration::from_millis(10));
    }
}

/// The one log in the database now: the active one.
fn active_log(db: &Path) -> PathBuf {
    let logs = logs(db);
    assert_eq!(logs.len(), 1, "one log before the flush: {logs:?}");
    logs[0].clone()
}

/// On `path`: the flush of `k = old` cannot remove its log, the flush of
/// `k = new` retries that removal and fails again, and the reopen reads
/// `new`. Each failure is counted, and the reopen removes the leftover.
fn a_log_left_behind_is_counted_and_never_replayed(path: FlushPath) {
    let mut f = Fixture::new(path);
    let leftover = {
        let db = f.open();
        if let FlushPath::StallStep = path {
            // The table that turns the slowdown on.
            db.put(b"seed", b"v").unwrap();
            db.flush().unwrap();
        }
        let leftover = active_log(f.dir.path());
        f.env.arm(Refuse::Log(leftover.clone()));
        f.put_and_flush(&db, b"k", b"old");
        assert_eq!(
            f.ticker(Ticker::WalRemoveFailed),
            1,
            "{path:?}: the flush reported the log it could not remove"
        );
        assert!(leftover.exists(), "{path:?}: the log outlived its flush");

        f.put_and_flush(&db, b"k", b"new");
        assert_eq!(
            f.ticker(Ticker::WalRemoveFailed),
            2,
            "{path:?}: the next flush retried the removal"
        );
        assert_eq!(db.get(b"k").unwrap().as_deref(), Some(&b"new"[..]));
        db.close().unwrap();
        leftover
    };
    f.env.arm(Refuse::Nothing);
    assert!(leftover.exists(), "{path:?}: the leftover reaches the reopen");

    let db = f.open();
    assert_eq!(
        db.get(b"k").unwrap().as_deref(),
        Some(&b"new"[..]),
        "{path:?}: recovery replayed a flushed log above the newer table"
    );
    assert!(!leftover.exists(), "{path:?}: the open removed the leftover");
}

#[test]
fn the_worker_flush_retires_its_log_and_records_it_flushed() {
    a_log_left_behind_is_counted_and_never_replayed(FlushPath::Worker);
}

#[test]
fn the_flush_after_a_commit_retires_its_log_and_records_it_flushed() {
    a_log_left_behind_is_counted_and_never_replayed(FlushPath::AfterCommit);
}

#[test]
fn the_stall_step_flush_retires_its_log_and_records_it_flushed() {
    a_log_left_behind_is_counted_and_never_replayed(FlushPath::StallStep);
}

#[test]
fn a_restored_database_replays_no_log_its_target_held() {
    let source = TempDir::new().unwrap();
    let db = Db::open(source.path(), Options::default()).unwrap();
    db.put(b"k", b"backed-up").unwrap();
    let backups = TempDir::new().unwrap();
    let mut engine = BackupEngine::open(backups.path()).unwrap();
    let id = engine.create_backup(&db).unwrap();
    // Writes after the backup, held only by the log the backup's flush
    // started, whose number is below the backup's next file id.
    db.put(b"k", b"after").unwrap();
    db.put(b"only-in-a-log", b"v").unwrap();
    let log = logs(source.path()).pop().expect("the source's active log");
    drop(db);

    let root = TempDir::new().unwrap();
    let target = root.path().join("restored");
    std::fs::create_dir_all(target.join("wal")).unwrap();
    let stray = target.join("wal").join(log.file_name().unwrap());
    std::fs::copy(&log, &stray).unwrap();
    engine.restore(id, &target, None).unwrap();

    let restored = Db::open(&target, Options::default()).unwrap();
    assert_eq!(
        restored.get(b"k").unwrap().as_deref(),
        Some(&b"backed-up"[..]),
        "the restored database replayed a log its backup does not hold"
    );
    assert_eq!(restored.get(b"only-in-a-log").unwrap(), None);
    assert!(!stray.exists(), "the open removed the log below min_wal_id");
}
