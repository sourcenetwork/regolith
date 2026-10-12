//! The open that moves an overlapping level, across a power cut at each of
//! its I/O calls (E14).
//!
//! The child opens a copy of `tests/fixtures/v0_1_9_overlap`, the database
//! the 0.1.9 release left with an overlapping bottom level, records that
//! the open returned and dies without closing. It runs under the
//! `LD_PRELOAD` shim. One run to the end gives the open's write and sync
//! calls in order; then, for each of them, a fresh child is killed before
//! that call and another after it, the directory is rebuilt as the
//! filesystem would have left it, every byte never synced discarded, and
//! the database is reopened. Whatever the cut:
//!
//! - the database opens;
//! - every read returns the newest version, the key the moved table's
//!   range tombstone deletes included. That holds only if the log carrying
//!   the moved tables' range tombstones is durable before the manifest
//!   records the move: a move recorded without them would bring that key
//!   back;
//! - the move is either still to make, and the reopen makes it again, or
//!   recorded, and once a cut finds it recorded every later cut does;
//! - an open that returned recorded it;
//! - the open after the reopen has nothing to move.
//!
//! The plain runs also discard every file whose directory entry was never
//! synced, so the new log has to be durable by name, not only by content,
//! before the manifest records the move. The run that turns encryption on
//! cannot be held to that here: it renames the rewritten manifest into the
//! database directory, and the shim records nothing about that directory
//! itself (its filter is the directory's path with a separator after it),
//! so the rename could never be seen made durable.
//!
//! # Linux only
//!
//! `LD_PRELOAD` interposition is a glibc mechanism; the file is compiled out
//! elsewhere. See `power_loss.rs` for what the shim does and does not prove.
#![cfg(target_os = "linux")]

mod common;

use std::path::{Path, PathBuf};
use std::time::Duration;

use common::fault::{
    self, ChildSpec, CrashRun, CutPoint, DieKind, OpKind, Phase, PowerLossOptions, TearMode,
    Trigger,
};
use common::keys::Keys;
use common::overlap_fixture::{self as fixture, MOVED, assert_db_reads, moved};
use regolith::{Db, Options};
use tempfile::TempDir;

const UPGRADE: &str = "open_an_overlapping_database";

#[test]
fn crash_child() {
    fault::child_entrypoint(dispatch);
}

fn dispatch(spec: &ChildSpec) {
    match &spec.phase {
        Phase::Custom(name) if name == UPGRADE => upgrade(spec),
        _ => fault::builtin_workload(spec),
    }
}

/// Beside the database directory, so the shim records none of it.
fn opened_marker(db: &Path) -> PathBuf {
    db.with_extension("opened")
}

fn upgrade(spec: &ChildSpec) {
    let db = Db::open(&spec.db_path, fixture::with_operator(spec.options())).expect("child: open");
    let marker = opened_marker(&spec.db_path);
    std::fs::write(&marker, b"1").expect("child: marker");
    std::fs::File::open(&marker)
        .and_then(|f| f.sync_all())
        .expect("child: sync marker");
    // Killed with the handle alive: nothing is flushed, nothing is closed.
    std::mem::forget(db);
    fault::kill_self();
}

fn reopen_options(encrypted: bool) -> Options {
    let options = fixture::with_operator(Options::default());
    if encrypted {
        options.key_provider(Keys::new(&[1]))
    } else {
        options
    }
}

/// Run the child over a fresh copy of the fixture and kill it at `trigger`.
fn run(trigger: Trigger, encrypted: bool) -> (TempDir, PathBuf, fault::ChildOutcome) {
    let tmp = TempDir::new().unwrap();
    let db_path = tmp.path().join("db");
    fixture::copy_to(&db_path);
    let spec = ChildSpec::new(Phase::Custom(UPGRADE.to_string()), &db_path).encrypted(encrypted);
    let out = CrashRun::new(spec)
        .trigger(trigger)
        .timeout(Duration::from_secs(120))
        .run();
    out.assert_killed();
    (tmp, db_path, out)
}

/// One write or sync call of the open: the kind, the file and which call
/// of that kind on that file it is.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Step {
    kind: DieKindOf,
    file: String,
    nth: u64,
}

/// [`DieKind`] is not comparable; this is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DieKindOf {
    Write,
    Fsync,
}

impl Step {
    fn trigger(&self, before: bool) -> Trigger {
        Trigger::Syscall {
            kind: match self.kind {
                DieKindOf::Write => DieKind::Write,
                DieKindOf::Fsync => DieKind::Fsync,
            },
            path_contains: self.file.clone(),
            nth: self.nth,
            before,
        }
    }
}

/// Every write and sync the open made, in order, from one run to the end.
fn steps_of_the_open(encrypted: bool) -> Vec<Step> {
    let (_tmp, db_path, out) = run(Trigger::Workload, encrypted);
    assert!(
        opened_marker(&db_path).exists(),
        "the reference run did not finish its open"
    );
    let mut steps: Vec<Step> = Vec::new();
    for record in &out.journal.records {
        let kind = match record.kind {
            OpKind::Write => DieKindOf::Write,
            OpKind::Sync => DieKindOf::Fsync,
            _ => continue,
        };
        if !record.succeeded() {
            continue;
        }
        // The path below the database directory names the file wherever
        // the directory is; a directory's own sync is named by its path.
        let file = record
            .path
            .strip_prefix(&db_path)
            .map(|rest| format!("/db/{}", rest.to_string_lossy()))
            .unwrap_or_else(|_| record.path.to_string_lossy().into_owned());
        let file = file.trim_end_matches('/').to_string();
        // The shim counts every call of the kind whose path contains the
        // name, so a directory's sync counts the syncs of the files in it.
        let nth = 1 + steps
            .iter()
            .filter(|s| s.kind == kind && s.file.contains(&file))
            .count() as u64;
        steps.push(Step { kind, file, nth });
    }
    steps
}

/// What a cut left: whether the reopen still had the move to make.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Move {
    MadeAgain,
    Recorded,
}

fn cut(trigger: Trigger, tear: TearMode, encrypted: bool) -> Move {
    let (_tmp, db_path, out) = run(trigger.clone(), encrypted);
    let lost = PowerLossOptions::default().tear(tear);
    // See the module docs for why only the plain runs are strict.
    let lost = if encrypted {
        lost
    } else {
        lost.strict_creates()
    };
    let report = fault::simulate_power_loss_with(&db_path, &out.journal, CutPoint::End, &lost);
    let returned = opened_marker(&db_path).exists();
    let expected = fixture::state();
    let what = format!("{trigger:?}, {tear:?}, encrypted: {encrypted}");

    let db = Db::open(&db_path, reopen_options(encrypted)).unwrap_or_else(|e| {
        panic!(
            "{what}: the database refuses to open after a power cut during the open that \
             moves its overlapping level: {e}\n{}",
            report.summary()
        )
    });
    let outcome = match moved(&db) {
        0 => Move::Recorded,
        MOVED => Move::MadeAgain,
        n => panic!("{what}: {n} tables moved, neither none nor all {MOVED}"),
    };
    if returned {
        assert_eq!(
            outcome,
            Move::Recorded,
            "{what}: the open returned, yet the move was not durable"
        );
    }
    assert_db_reads(&what, &db, &expected);
    db.close().unwrap();
    drop(db);

    let db = Db::open(&db_path, reopen_options(encrypted)).unwrap();
    assert_eq!(moved(&db), 0, "{what}: the move was made twice");
    assert_db_reads(&format!("{what}, second reopen"), &db, &expected);
    outcome
}

/// Cut before and after every write and sync of the open, in order.
fn sweep(tear: TearMode, encrypted: bool) {
    let steps = steps_of_the_open(encrypted);
    assert!(
        steps
            .iter()
            .any(|s| s.file.ends_with("MANIFEST") && s.kind == DieKindOf::Fsync),
        "the open never synced the manifest: {steps:?}"
    );
    assert!(
        steps
            .iter()
            .any(|s| s.file.contains("/wal/") && s.kind == DieKindOf::Fsync),
        "the open never synced a log: {steps:?}"
    );
    let mut recorded_since: Option<String> = None;
    let mut outcomes = Vec::new();
    for step in &steps {
        for before in [true, false] {
            let outcome = cut(step.trigger(before), tear, encrypted);
            let at = format!("{} {step:?}", if before { "before" } else { "after" });
            if let Some(first) = &recorded_since {
                assert_eq!(
                    outcome,
                    Move::Recorded,
                    "the move was recorded by a cut {first}, and not by a later one, {at}"
                );
            } else if outcome == Move::Recorded {
                recorded_since = Some(at.clone());
            }
            outcomes.push((at, outcome));
        }
    }
    assert_eq!(
        outcomes.first().map(|(_, outcome)| *outcome),
        Some(Move::MadeAgain),
        "a cut before the open's first write found the move recorded"
    );
    assert_eq!(
        cut(Trigger::Workload, tear, encrypted),
        Move::Recorded,
        "an open that returned did not record the move"
    );
    let first = recorded_since.expect("no cut inside the open found the move recorded");
    assert!(
        first.contains("MANIFEST"),
        "the move became durable at a call that is not on the manifest: {first}\n{outcomes:#?}"
    );
}

#[test]
fn a_power_cut_at_any_call_of_the_open_leaves_every_read_right() {
    sweep(TearMode::Truncate, false);
}

#[test]
fn a_power_cut_that_tears_a_sector_at_any_call_of_the_open_leaves_every_read_right() {
    sweep(TearMode::TornSector, false);
}

/// The same when the open that moves the tables is the first with a key
/// provider, which also rewrites the manifest sealed.
#[test]
fn a_power_cut_at_any_call_of_the_open_that_also_turns_encryption_on_leaves_every_read_right() {
    sweep(TearMode::Truncate, true);
}
