//! Power cuts where the Phase 6 packages meet.
//!
//! - **Every flush path** (#268 x #265). The compaction worker, a writer after
//!   its commit, and a writer stopped by a stall each flush; a cut at any
//!   manifest sync, before or after it, or inside a table, keeps every
//!   acknowledged write and reads no key older than its last acknowledged
//!   version. A flush that unlinked its log before its table's batch was
//!   durable loses acknowledged writes here. (A flush that records no
//!   `min_wal_id` shows only once an unlink fails: `phase6_integration.rs`.)
//!
//! Each write of the workload overwrites one of a few keys and puts a key of
//! its own, in one batch, each value carrying the index of the write, at
//! Immediate durability, so every acknowledged write is durable when it is
//! acknowledged.
//!
//! # Linux only
//!
//! `LD_PRELOAD` interposition is a glibc mechanism; the file is compiled out
//! elsewhere. See `power_loss.rs` for what the shim does and does not prove.
#![cfg(target_os = "linux")]

mod common;

use std::fs::OpenOptions;
use std::io::Write;
use std::path::Path;
use std::sync::Arc;
use std::time::Duration;

use common::fault::{
    self, ChildOutcome, ChildSpec, CrashRun, CutPoint, DieKind, Phase, PowerLossOptions, TearMode,
    Trigger,
};
use common::faulty_env::FaultyEnv;
use regolith::env::Env;
use regolith::{Db, DurabilityMode, Options, WriteBatch};
use tempfile::TempDir;

/// Keys the workload overwrites.
const KEYS: usize = 8;
/// Writes per run: enough for a few dozen flushes at the write buffer below.
const OPS: usize = 600;
const VALUE_LEN: usize = 128;
const WRITE_BUFFER: usize = 4 * 1024;
const CHILD_TIMEOUT: Duration = Duration::from_secs(180);

/// The thread that flushes a sealed memtable.
#[derive(Clone, Copy, Debug)]
enum FlushPath {
    /// The compaction worker, woken by the seal.
    Worker,
    /// The writer whose commit sealed it, once that commit returned.
    AfterCommit,
    /// A writer stopped by a stall, inside the bounded step it runs first.
    StallStep,
}

impl FlushPath {
    fn phase(self) -> Phase {
        Phase::Custom(
            match self {
                FlushPath::Worker => "overwrite_worker",
                FlushPath::AfterCommit => "overwrite_after_commit",
                FlushPath::StallStep => "overwrite_stall_step",
            }
            .to_string(),
        )
    }

    fn of(phase: &Phase) -> Option<FlushPath> {
        [
            FlushPath::Worker,
            FlushPath::AfterCommit,
            FlushPath::StallStep,
        ]
        .into_iter()
        .find(|path| &path.phase() == phase)
    }

    /// The child's options: the spec's, with this path's flushing thread.
    fn options(self, spec: &ChildSpec, env: Arc<FaultyEnv>) -> Options {
        let options = spec.options().env(env as Arc<dyn Env>);
        match self {
            FlushPath::Worker => options.max_background_compactions(1),
            FlushPath::AfterCommit => options.max_background_compactions(0),
            // One table at L0 slows every write down, and a slowed write with
            // no worker first runs one bounded step. The compaction trigger is
            // out of reach and the stop trigger off, so the steps between
            // flushes find nothing to do.
            FlushPath::StallStep => options
                .max_background_compactions(0)
                .level0_slowdown_writes_trigger(1)
                .level0_stop_writes_trigger(0)
                .l0_compaction_trigger(1000),
        }
    }
}

#[test]
fn crash_child() {
    fault::child_entrypoint(dispatch);
}

fn dispatch(spec: &ChildSpec) {
    match FlushPath::of(&spec.phase) {
        Some(path) => overwrite(spec, path),
        None => fault::builtin_workload(spec),
    }
}

fn key(i: usize) -> Vec<u8> {
    format!("key/{:02}", i % KEYS).into_bytes()
}

/// The key only write `i` writes: an overwrite hides a lost older version,
/// this one cannot.
fn own_key(i: usize) -> Vec<u8> {
    format!("own/{i:06}").into_bytes()
}

/// The value write `i` puts: its index, then padding.
fn value(i: usize) -> Vec<u8> {
    let mut v = format!("{i:08}#").into_bytes();
    v.resize(VALUE_LEN, b'v');
    v
}

fn frozen_bytes(db: &Db) -> u64 {
    db.get_int_property("regolith.num-entries-imm-mem-tables")
        .unwrap()
}

/// The child: overwrite the keys, acknowledging each write once it returns.
fn overwrite(spec: &ChildSpec, path: FlushPath) {
    let env = Arc::new(FaultyEnv::default());
    let db = Db::open(&spec.db_path, path.options(spec, Arc::clone(&env))).expect("child: open");
    // One unbuffered write per acknowledgement, so a kill a microsecond
    // later cannot lose the record of what was told.
    let mut acks = OpenOptions::new()
        .create(true)
        .append(true)
        .open(&spec.ack_path)
        .unwrap();
    if let FlushPath::StallStep = path {
        // The table that turns the slowdown on.
        db.put(b"seed", b"v").expect("child: seed");
        db.flush().expect("child: seed flush");
    }
    for i in 0..spec.ops {
        if let FlushPath::StallStep = path {
            // While nothing is frozen, a seal's own flush fails, so the
            // memtable is still frozen when the next write's stall step
            // flushes it: every flush here is a stall step's.
            env.fail_tables(frozen_bytes(&db) == 0);
        }
        let mut batch = WriteBatch::new();
        batch.put(&key(i), &value(i));
        batch.put(&own_key(i), &value(i));
        db.write(batch).expect("child: write");
        acks.write_all(format!("{i}\n").as_bytes()).unwrap();
    }
    env.fail_tables(false);
    db.close().expect("child: close");
}

/// Check the reopened database against what the child was told: every
/// acknowledged write's own key is there, and every overwritten key reads
/// its last acknowledged version or a later one, never an older one.
fn check_overwrites(db: &Db, out: &ChildOutcome, what: &str) {
    for &i in &out.acked {
        assert_eq!(
            db.get(&own_key(i)).unwrap(),
            Some(value(i)),
            "{what}: acknowledged write {i} was lost"
        );
    }
    let mut last_acked = [None; KEYS];
    for &i in &out.acked {
        last_acked[i % KEYS] = Some(last_acked[i % KEYS].map_or(i, |was: usize| was.max(i)));
    }
    for (k, acked) in last_acked.iter().enumerate() {
        let read = db.get(&key(k)).unwrap();
        let Some(read) = read else {
            assert!(acked.is_none(), "{what}: key {k} lost its acknowledged write {acked:?}");
            continue;
        };
        let index: usize = std::str::from_utf8(&read[..8]).unwrap().parse().unwrap();
        assert_eq!(index % KEYS, k, "{what}: key {k} reads another key's value");
        assert!(index < out.spec.ops, "{what}: key {k} reads a write never made");
        if let Some(acked) = acked {
            assert!(
                index >= *acked,
                "{what}: key {k} reads write {index}, older than its acknowledged write {acked}"
            );
        }
    }
}

fn spec(path: FlushPath, db: &Path) -> ChildSpec {
    ChildSpec::new(path.phase(), db)
        .ops(OPS)
        .value_len(VALUE_LEN)
        .write_buffer_size(WRITE_BUFFER)
        .durability(DurabilityMode::Immediate)
}

fn manifest_sync(nth: u64, before: bool) -> Trigger {
    Trigger::Syscall {
        kind: DieKind::Fsync,
        path_contains: "MANIFEST".to_string(),
        nth,
        before,
    }
}

/// Cut `path`'s run at `trigger`, tear what was never synced with `tear`,
/// reopen and check every key.
fn cut(path: FlushPath, trigger: Trigger, tear: TearMode) {
    let tmp = TempDir::new().unwrap();
    let db = tmp.path().join("db");
    let out = CrashRun::new(spec(path, &db))
        .trigger(trigger.clone())
        .timeout(CHILD_TIMEOUT)
        .run();
    out.assert_killed();
    assert!(out.acked_count() > 0, "{path:?}: no write was acknowledged");
    let report = fault::simulate_power_loss_with(
        &db,
        &out.journal,
        CutPoint::End,
        &PowerLossOptions::default().tear(tear),
    );
    let what = format!("{path:?}, {trigger:?}, {tear:?}");
    let reopened = Db::open(&db, Options::default()).unwrap_or_else(|e| {
        panic!(
            "{what}: the database refuses to open: {e}\n{}",
            report.summary()
        )
    });
    check_overwrites(&reopened, &out, &what);
}

const TEARS: [TearMode; 2] = [TearMode::Truncate, TearMode::TornSector];

fn cut_everywhere(path: FlushPath) {
    // The manifest's first sync is its creation's; the stall path's seed
    // table takes the next one.
    let first = match path {
        FlushPath::StallStep => 3,
        FlushPath::Worker | FlushPath::AfterCommit => 2,
    };
    let triggers = [
        // The path's first flush: its batch written, its sync not yet made.
        manifest_sync(first, true),
        // A flush's batch durable, its log not yet retired.
        manifest_sync(first + 1, false),
        manifest_sync(first + 4, true),
        manifest_sync(first + 7, false),
        // Inside a table: its batch not yet written.
        Trigger::sst_write(4),
    ];
    for trigger in triggers {
        for tear in TEARS {
            cut(path, trigger.clone(), tear);
        }
    }
}

#[test]
fn a_power_cut_around_a_worker_flush_keeps_every_acknowledged_write() {
    cut_everywhere(FlushPath::Worker);
}

#[test]
fn a_power_cut_around_a_flush_after_a_commit_keeps_every_acknowledged_write() {
    cut_everywhere(FlushPath::AfterCommit);
}

#[test]
fn a_power_cut_around_a_stall_step_flush_keeps_every_acknowledged_write() {
    cut_everywhere(FlushPath::StallStep);
}
