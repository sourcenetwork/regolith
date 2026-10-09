//! A panic in code the caller supplied, inside a commit's ordered step.
//!
//! The panic is caught, the commit that ran the code applies nothing and fails
//! with `Error::CallbackPanicked` naming the trait, and the database is
//! read-only until it is reopened. The same code run outside a commit, by an
//! explicit flush, unwinds into that call and leaves the database writable.

// Native-only. wasm-pack builds every test target for wasm32, and these use
// the filesystem. The browser suite lives in tests/wasm_opfs*.rs.
#![cfg(not(target_arch = "wasm32"))]

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::Path;
use std::sync::Arc;

use regolith::prelude::*;
use regolith::{
    Db, Error, EventListener, FixedLengthPrefix, FlushJobInfo, PrefixExtractor, Priority,
    RateLimiter,
};

/// Panics on a key that starts with `0`.
struct PanicsOn(&'static [u8]);

impl KeyClassifier for PanicsOn {
    fn classify(&self, key: &[u8]) -> KeyClass {
        assert!(!key.starts_with(self.0), "injected classifier panic");
        KeyClass::Ordinary
    }
}

fn classified(dir: &Path) -> OptimisticTransactionDb {
    OptimisticTransactionDb::open(dir, Options::default())
        .unwrap()
        .with_policy(Arc::new(PanicsOn(b"boom")))
}

fn begin(db: &OptimisticTransactionDb) -> Transaction {
    db.begin(&TxnOptions::new().isolation(IsolationLevel::DefraLevel))
}

fn panicked<T>(callback: &str, result: &TxResult<T>) -> bool {
    matches!(
        result,
        Err(TransactionError::Engine(Error::CallbackPanicked { callback: named })) if *named == callback
    )
}

#[test]
fn a_panicking_classifier_fails_the_commit_and_latches_the_database() {
    let dir = tempfile::tempdir().unwrap();
    let db = classified(dir.path());
    db.db().put(b"before", b"kept").unwrap();

    // A write is classified when it is made, to refuse a log key, so the
    // classifier meets `boom` at the commit through a read of it.
    let tx = begin(&db);
    assert_eq!(tx.get(b"boom").unwrap(), None);
    tx.put(b"beside", b"lost").unwrap();
    assert!(panicked("KeyClassifier", &tx.commit()));

    let after = db.db().put(b"after", b"v");
    assert!(
        matches!(
            after,
            Err(Error::CallbackPanicked {
                callback: "KeyClassifier"
            })
        ),
        "{after:?}"
    );
    let other = begin(&db);
    other.put(b"elsewhere", b"v").unwrap();
    assert!(panicked("KeyClassifier", &other.commit()));
    assert_eq!(db.db().get(b"before").unwrap(), Some(b"kept".to_vec()));
    assert_eq!(
        db.db().get(b"beside").unwrap(),
        None,
        "the commit applied nothing"
    );

    drop(db);
    let reopened = Db::open(dir.path(), Options::default()).unwrap();
    assert_eq!(reopened.get(b"before").unwrap(), Some(b"kept".to_vec()));
    assert_eq!(reopened.get(b"boom").unwrap(), None);
    reopened.put(b"after", b"v").unwrap();
}

/// A write is classified when it is made, so a panic there is outside any
/// commit: it unwinds into the call that ran the classifier and fails only
/// that call.
#[test]
fn a_classifier_that_panics_in_a_write_unwinds_into_it_and_leaves_the_database_writable() {
    let dir = tempfile::tempdir().unwrap();
    let db = classified(dir.path());
    let tx = begin(&db);
    assert!(catch_unwind(AssertUnwindSafe(|| tx.put(b"boom", b"v"))).is_err());
    assert!(catch_unwind(AssertUnwindSafe(|| tx.delete(b"boom"))).is_err());
    tx.put(b"fine", b"v").unwrap();
    tx.commit().unwrap();
    db.db().put(b"after", b"v").unwrap();
    assert_eq!(db.db().get(b"fine").unwrap(), Some(b"v".to_vec()));
    assert_eq!(db.db().get(b"boom").unwrap(), None);
}

#[test]
fn a_classifier_that_panics_on_a_scanned_stretch_fails_the_commit_too() {
    let dir = tempfile::tempdir().unwrap();
    let db = classified(dir.path());
    db.db().put(b"boom/1", b"v").unwrap();
    db.db().put(b"boom/2", b"v").unwrap();

    let tx = begin(&db);
    assert_eq!(tx.scan_stream(Some(b"boom/"), Some(b"boom0")).count(), 2);
    assert!(panicked("KeyClassifier", &tx.commit()));
    assert!(matches!(
        db.db().put(b"after", b"v"),
        Err(Error::CallbackPanicked { .. })
    ));
}

#[test]
fn a_classifier_that_does_not_panic_leaves_commits_alone() {
    let dir = tempfile::tempdir().unwrap();
    let db = classified(dir.path());
    let tx = begin(&db);
    tx.put(b"fine", b"v").unwrap();
    tx.commit().unwrap();
    db.db().put(b"after", b"v").unwrap();
}

/// A buffer small enough that a few writes rotate it, and so flush.
fn tiny() -> Options {
    Options::default().write_buffer_size(4 * 1024)
}

fn key(i: usize) -> Vec<u8> {
    format!("key{i:04}").into_bytes()
}

/// Write until a write fails, returning the index it failed at and why. The
/// failed write did not land.
fn write_until_it_fails(db: &Db) -> (usize, Error) {
    for i in 0..400 {
        if let Err(err) = db.put(&key(i), &[7u8; 512]) {
            return (i, err);
        }
    }
    panic!("400 writes of 512 bytes never rotated a 4 KiB buffer into a failure");
}

/// The write that rotates the buffer fails with `callback`, the database is
/// read-only after it, and a reopen finds every write before it.
fn assert_the_rotating_write_latches(dir: &Path, options: Options, callback: &str) {
    let db = Db::open(dir, options).unwrap();
    let (failed_at, err) = write_until_it_fails(&db);
    assert!(
        matches!(&err, Error::CallbackPanicked { callback: named } if *named == callback),
        "{err:?}"
    );
    assert!(failed_at > 0);
    let later = db.put(b"later", b"v");
    assert!(
        matches!(&later, Err(Error::CallbackPanicked { callback: named }) if *named == callback),
        "{later:?}"
    );
    assert_eq!(db.get(&key(failed_at)).unwrap(), None);
    assert!(db.get(&key(failed_at - 1)).unwrap().is_some());

    drop(db);
    let reopened = Db::open(dir, tiny()).unwrap();
    for i in 0..failed_at {
        assert!(
            reopened.get(&key(i)).unwrap().is_some(),
            "write {i} was lost"
        );
    }
    assert_eq!(reopened.get(&key(failed_at)).unwrap(), None);
    reopened.put(b"later", b"v").unwrap();
}

struct PanicsOnFlush;

impl EventListener for PanicsOnFlush {
    fn on_flush_completed(&self, _: &FlushJobInfo) {
        panic!("injected listener panic");
    }
}

#[test]
fn a_panicking_listener_in_the_rotation_a_write_runs_latches_the_database() {
    let dir = tempfile::tempdir().unwrap();
    let options = tiny().listeners(vec![Arc::new(PanicsOnFlush)]);
    assert_the_rotating_write_latches(dir.path(), options, "EventListener");
}

struct PanicsOnRequest;

impl RateLimiter for PanicsOnRequest {
    fn request(&self, _: u64, _: Priority) {
        panic!("injected limiter panic");
    }

    fn set_bytes_per_second(&self, _: u64) {}

    fn get_bytes_per_second(&self) -> u64 {
        0
    }

    fn get_total_bytes_through(&self, _: Priority) -> u64 {
        0
    }
}

#[test]
fn a_panicking_rate_limiter_in_the_rotation_a_write_runs_latches_the_database() {
    let dir = tempfile::tempdir().unwrap();
    let options = tiny().rate_limiter(Some(Arc::new(PanicsOnRequest)));
    assert_the_rotating_write_latches(dir.path(), options, "RateLimiter");
}

struct PanicsOnExtract;

impl PrefixExtractor for PanicsOnExtract {
    fn extract<'a>(&self, _: &'a [u8]) -> Option<&'a [u8]> {
        panic!("injected extractor panic");
    }

    fn name(&self) -> &'static str {
        "panics"
    }
}

#[test]
fn a_panicking_prefix_extractor_in_the_rotation_a_write_runs_latches_the_database() {
    let dir = tempfile::tempdir().unwrap();
    let options = tiny().prefix_extractor(Some(Arc::new(PanicsOnExtract)));
    assert_the_rotating_write_latches(dir.path(), options, "PrefixExtractor");
}

#[test]
fn the_same_listener_panic_outside_a_commit_fails_only_that_call() {
    let dir = tempfile::tempdir().unwrap();
    let options = tiny().listeners(vec![Arc::new(PanicsOnFlush)]);
    let db = Db::open(dir.path(), options).unwrap();
    db.put(b"k", b"v").unwrap();

    let unwound = catch_unwind(AssertUnwindSafe(|| db.flush()));
    assert!(
        unwound.is_err(),
        "an explicit flush runs the listener uncaught"
    );

    db.put(b"after", b"v")
        .expect("the database is still writable");
    assert_eq!(db.get(b"k").unwrap(), Some(b"v".to_vec()));
    assert_eq!(db.get(b"after").unwrap(), Some(b"v".to_vec()));
}

#[test]
fn a_prefix_extractor_that_does_not_panic_is_unaffected() {
    let dir = tempfile::tempdir().unwrap();
    let options = tiny().prefix_extractor(Some(Arc::new(FixedLengthPrefix(3))));
    let db = Db::open(dir.path(), options).unwrap();
    for i in 0..60 {
        db.put(&key(i), &[7u8; 512]).unwrap();
    }
    assert!(db.get(&key(0)).unwrap().is_some());
}
