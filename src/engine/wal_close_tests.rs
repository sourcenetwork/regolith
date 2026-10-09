//! A clean close ends the log with CLOSE after a sync of everything before
//! it; a close that cannot vouch for the log leaves CLOSE out; and an open
//! reports the tail it drops (`proofs/tla/WalRecovery.tla`, `AppendClose`
//! and `Discarded`).

use std::path::{Path, PathBuf};
use std::sync::Arc;

use tempfile::TempDir;

use super::wal_frame::{self, HEADER_LEN, KIND_CLOSE, STAMP_LEN};
use super::wal_rotation_tests::SyncFault;
use crate::statistics::{Statistics, Ticker};
use crate::{Db, EventListener, Options, WalTailDiscardedInfo};

fn log_of(dir: &TempDir) -> PathBuf {
    let mut logs: Vec<PathBuf> = std::fs::read_dir(dir.path().join("wal"))
        .unwrap()
        .map(|e| e.unwrap().path())
        .collect();
    logs.sort();
    logs.pop().expect("a log")
}

/// The kind, claim and offset of the last record of the log at `path`.
fn last_record(path: &Path) -> (u8, u64, u64) {
    let bytes = std::fs::read(path).unwrap();
    let nonce = wal_frame::stamp_nonce(bytes[..STAMP_LEN].try_into().unwrap()).unwrap();
    let mut at = STAMP_LEN as u64;
    let mut last = None;
    while (at as usize) < bytes.len() {
        let header = wal_frame::decode_header(&bytes[at as usize..], nonce, at, false).unwrap();
        last = Some((header.kind, header.synced_through, at));
        at += header.record_len();
    }
    last.expect("a record")
}

#[derive(Default)]
struct Reports(std::sync::Mutex<Vec<WalTailDiscardedInfo>>);

impl EventListener for Reports {
    fn on_wal_tail_discarded(&self, info: &WalTailDiscardedInfo) {
        self.0.lock().unwrap().push(info.clone());
    }
}

/// Close flushes what the memtable holds and seals its log, so the log
/// it closes holds only CLOSE, claiming the stamp before it synced.
#[test]
fn close_ends_the_log_with_close_claiming_everything_before_it() {
    let dir = TempDir::new().unwrap();
    let db = Db::open(dir.path(), Options::default()).unwrap();
    db.put(b"a", b"1").unwrap();
    db.put(b"b", b"2").unwrap();
    db.close().unwrap();
    let (kind, claim, at) = last_record(&log_of(&dir));
    assert_eq!(kind, KIND_CLOSE);
    assert_eq!(
        claim, at,
        "the sync before CLOSE covered every byte before it"
    );
    assert_eq!(
        std::fs::metadata(log_of(&dir)).unwrap().len(),
        at + HEADER_LEN as u64
    );
    assert!(
        db.put(b"c", b"3").is_err(),
        "a closed database takes no write"
    );
}

/// A latched database may have bytes at the end of its log nobody can
/// account for, so its close leaves CLOSE out rather than vouch for them.
#[test]
fn a_latched_database_closes_without_appending_close() {
    let dir = TempDir::new().unwrap();
    let db = Db::open(dir.path(), Options::default()).unwrap();
    db.put(b"a", b"1").unwrap();
    db.engine().latch_callback_panic("test");
    db.close().unwrap();
    // Close flushed the memtable into a table and sealed its log, so the
    // log left holds nothing: not even CLOSE.
    assert_eq!(
        std::fs::metadata(log_of(&dir)).unwrap().len(),
        STAMP_LEN as u64
    );
    drop(db);
    let db = Db::open(dir.path(), Options::default()).unwrap();
    assert_eq!(db.get(b"a").unwrap(), Some(b"1".to_vec()));
}

/// A close whose sync fails leaves the log without CLOSE, says why, and
/// latches the database, since what reached the device is unknown.
#[test]
fn a_close_whose_sync_fails_latches_and_appends_nothing() {
    let dir = TempDir::new().unwrap();
    let db = Db::open(dir.path(), Options::default()).unwrap();
    db.put(b"a", b"1").unwrap();
    // Flushed now, so close has no memtable to seal and the sync that
    // fails is the one before CLOSE.
    db.flush().unwrap();
    let before = std::fs::read(log_of(&dir)).unwrap();
    {
        let _fault = SyncFault::arm(&dir);
        let err = db.close().unwrap_err();
        assert!(
            err.to_string().contains("injected WAL sync failure"),
            "{err}"
        );
    }
    assert_eq!(std::fs::read(log_of(&dir)).unwrap(), before);
    let later = db.put(b"b", b"2").unwrap_err();
    assert!(later.to_string().contains("unknown state"), "{later}");
    drop(db);
    let db = Db::open(dir.path(), Options::default()).unwrap();
    assert_eq!(db.get(b"a").unwrap(), Some(b"1".to_vec()));
}

/// A read-only open drops the damaged tail from what it serves and
/// reports it, but writes nothing: the bytes stay for the next read-write
/// open, which reports them again and truncates them.
#[test]
fn a_read_only_open_reports_the_tail_and_leaves_it_in_place() {
    let dir = TempDir::new().unwrap();
    {
        let db = Db::open(dir.path(), Options::default()).unwrap();
        db.put(b"a", b"1").unwrap();
    }
    let log = log_of(&dir);
    let mut bytes = std::fs::read(&log).unwrap();
    let whole = bytes.len() as u64;
    bytes.extend_from_slice(&[0xAB; 100]);
    std::fs::write(&log, &bytes).unwrap();

    let open_with_reports = |read_only: bool| {
        let reports = Arc::new(Reports::default());
        let stats = Arc::new(Statistics::new());
        let opts = Options::default()
            .listeners(vec![reports.clone() as Arc<dyn EventListener>])
            .statistics(Some(Arc::clone(&stats)));
        let db = if read_only {
            Db::open_read_only(dir.path(), opts)
        } else {
            Db::open(dir.path(), opts)
        }
        .unwrap();
        assert_eq!(db.get(b"a").unwrap(), Some(b"1".to_vec()));
        let taken = reports.0.lock().unwrap().clone();
        assert_eq!(taken.len(), 1);
        assert_eq!(taken[0].file_path, log);
        assert_eq!(taken[0].offset, whole);
        assert_eq!(taken[0].discarded_bytes, 100);
        assert_eq!(taken[0].last_sequence, 1);
        assert_eq!(stats.get_ticker(Ticker::WalTailDiscarded), 1);
        assert_eq!(stats.get_ticker(Ticker::WalTailDiscardedBytes), 100);
    };
    open_with_reports(true);
    assert_eq!(
        std::fs::read(&log).unwrap(),
        bytes,
        "a read-only open writes nothing"
    );
    open_with_reports(false);
}
