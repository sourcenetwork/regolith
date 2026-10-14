//! A database regolith 0.1.9 wrote opens on this version, replays its
//! format 1 write-ahead log, and once it writes, logs in format 2 and
//! reopens (plan 4.3: the upgrade is one-way).
//!
//! `tests/fixtures/v0_1_9` was written by the release tagged `v0.1.9`, with
//! `Immediate` durability and a concatenating merge operator named
//! `concat`:
//!
//! 1. with a 64 KiB write buffer, `put a00000..a01999`, each value
//!    `format!("{i:05}")` repeated 20 times, then `close`, which left two
//!    tables;
//! 2. reopened with a 64 MiB write buffer: `put k000..k049 = v{i}`,
//!    `delete k007`, `delete_range [k010, k015)`, one batch of `put b1 = x`,
//!    `put b2 = y`, `delete k020`, `merge m 1`, `merge m 2`, and
//!    `put a00003 = overwritten`; then the process exited without closing,
//!    so every write of step 2 is only in the format 1 log.

// Native-only, like every test that touches the filesystem.
#![cfg(not(target_arch = "wasm32"))]

mod common;

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use common::wal_format::{self, TailReports};
use regolith::{Db, EventListener, MergeOperator, Options, WriteBatch};
use tempfile::TempDir;

struct Concat;

impl MergeOperator for Concat {
    fn full_merge(&self, _key: &[u8], base: Option<&[u8]>, operands: &[&[u8]]) -> Option<Vec<u8>> {
        let mut out = base.map(<[u8]>::to_vec).unwrap_or_default();
        for op in operands {
            out.extend_from_slice(op);
        }
        Some(out)
    }

    fn name(&self) -> &'static str {
        "concat"
    }
}

fn opts() -> Options {
    Options::default()
        .write_buffer_size(64 * 1024 * 1024)
        .merge_operator(Some(Arc::new(Concat)))
}

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/v0_1_9")
}

fn copy_tree(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap();
    for entry in fs::read_dir(from).unwrap().flatten() {
        let target = to.join(entry.file_name());
        if entry.path().is_dir() {
            copy_tree(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), &target).unwrap();
        }
    }
}

fn wal_files(db: &Path) -> Vec<PathBuf> {
    let mut wals: Vec<PathBuf> = fs::read_dir(db.join("wal"))
        .unwrap()
        .flatten()
        .map(|e| e.path())
        .collect();
    wals.sort();
    wals
}

/// The state 0.1.9 left: step 1, then step 2.
fn fixture_state() -> BTreeMap<Vec<u8>, Vec<u8>> {
    let mut state = BTreeMap::new();
    for i in 0..2000u32 {
        state.insert(
            format!("a{i:05}").into_bytes(),
            format!("{i:05}").repeat(20).into_bytes(),
        );
    }
    for i in 0..50u32 {
        state.insert(
            format!("k{i:03}").into_bytes(),
            format!("v{i}").into_bytes(),
        );
    }
    state.remove(b"k007".as_slice());
    for i in 10..15u32 {
        state.remove(format!("k{i:03}").as_bytes());
    }
    state.insert(b"b1".to_vec(), b"x".to_vec());
    state.insert(b"b2".to_vec(), b"y".to_vec());
    state.remove(b"k020".as_slice());
    state.insert(b"m".to_vec(), b"12".to_vec());
    state.insert(b"a00003".to_vec(), b"overwritten".to_vec());
    state
}

fn read_all(db: &Db) -> BTreeMap<Vec<u8>, Vec<u8>> {
    db.scan(None, None).unwrap().into_iter().collect()
}

fn format_of(log: &Path) -> u16 {
    let bytes = fs::read(log).unwrap();
    assert_eq!(
        &bytes[0..4],
        b"REGO",
        "{} is not a stamped log",
        log.display()
    );
    u16::from_le_bytes([bytes[4], bytes[5]])
}

/// The headline: open the 0.1.9 database, write, close, reopen.
#[test]
fn a_0_1_9_database_opens_writes_closes_and_reopens() {
    let tmp = TempDir::new().unwrap();
    let db_dir = tmp.path().join("db");
    copy_tree(&fixture_dir(), &db_dir);
    let old_logs = wal_files(&db_dir);
    assert_eq!(old_logs.len(), 1);
    assert_eq!(
        format_of(&old_logs[0]),
        1,
        "the fixture holds a format 1 log"
    );

    let mut expected = fixture_state();
    {
        let db = Db::open(&db_dir, opts()).expect("a 0.1.9 database opens");
        assert_eq!(read_all(&db), expected, "the format 1 log replayed");

        for i in 0..100u32 {
            db.put(format!("n{i:03}").as_bytes(), b"new").unwrap();
            expected.insert(format!("n{i:03}").into_bytes(), b"new".to_vec());
        }
        db.delete(b"b1").unwrap();
        expected.remove(b"b1".as_slice());
        let mut batch = WriteBatch::new();
        batch.put(b"after", b"upgrade");
        batch.merge(b"m", b"3");
        db.write(batch).unwrap();
        expected.insert(b"after".to_vec(), b"upgrade".to_vec());
        expected.insert(b"m".to_vec(), b"123".to_vec());
        db.close().unwrap();
    }

    // The format 1 log is gone; what replaces it is format 2, and a clean
    // close ended it with CLOSE.
    let logs = wal_files(&db_dir);
    assert!(!logs.contains(&old_logs[0]), "the format 1 log was retired");
    let newest = logs.last().expect("a log");
    assert_eq!(format_of(newest), 2);
    let bytes = fs::read(newest).unwrap();
    let bounds = wal_format::record_bounds(&bytes);
    assert_eq!(
        wal_format::kind_at(&bytes, bounds[bounds.len() - 2]),
        wal_format::KIND_CLOSE
    );

    let reports = TailReports::new();
    let db = Db::open(
        &db_dir,
        opts().listeners(vec![reports.clone() as Arc<dyn EventListener>]),
    )
    .expect("the upgraded database reopens");
    assert_eq!(read_all(&db), expected);
    assert!(reports.taken().is_empty(), "a clean close leaves no tail");
    db.close().unwrap();
    drop(db);

    let db = Db::open_read_only(&db_dir, opts()).expect("and opens read-only");
    assert_eq!(read_all(&db), expected);
}

/// A 0.1.9 log a crash tore is read by the format 1 rule it was written
/// under: the torn final record is dropped, the drop is reported, and
/// every whole record before it replays.
#[test]
fn a_torn_0_1_9_log_replays_its_whole_records_and_reports_the_tail() {
    let tmp = TempDir::new().unwrap();
    let db_dir = tmp.path().join("db");
    copy_tree(&fixture_dir(), &db_dir);
    let log = wal_files(&db_dir).pop().unwrap();
    let bytes = fs::read(&log).unwrap();
    fs::write(&log, &bytes[..bytes.len() - 3]).unwrap();

    let reports = TailReports::new();
    let db = Db::open(
        &db_dir,
        opts().listeners(vec![reports.clone() as Arc<dyn EventListener>]),
    )
    .unwrap();
    let mut expected = fixture_state();
    expected.insert(
        b"a00003".to_vec(),
        format!("{:05}", 3).repeat(20).into_bytes(),
    );
    assert_eq!(read_all(&db), expected, "only the torn last put is lost");
    let taken = reports.taken();
    assert_eq!(taken.len(), 1);
    assert_eq!(taken[0].file_path, log);
    assert_eq!(
        taken[0].offset + taken[0].discarded_bytes,
        bytes.len() as u64 - 3
    );
}
