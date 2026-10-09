//! A scan that fails mid-range must not read as one that finished.
//!
//! `Iterator` has nowhere to put a failure, so a scan that dies on a corrupt
//! block ends exactly like one that reached the end of its range. A caller
//! that only iterates sees a short answer and no reason for it. `status()`
//! is where the reason lives, and this holds it to that: after a scan over a
//! damaged store, the rows are a prefix and `status()` says so.

// Native-only. wasm-pack builds every test target for wasm32, and these use
// the filesystem, which does not exist there.
#![cfg(not(target_arch = "wasm32"))]

use std::io::{Read, Seek, SeekFrom, Write};

use regolith::{Db, Options, TxnOptions, WriteBatch};

fn small_options() -> Options {
    Options::default()
        .write_buffer_size(64 * 1024)
        .block_size(4 * 1024)
        .block_cache_size(0)
        .target_file_size(256 * 1024)
        .l0_compaction_trigger(8)
        .max_background_compactions(0)
}

const KEYS: u64 = 20_000;

fn build(dir: &std::path::Path) {
    let db = Db::open(dir, small_options()).unwrap();
    let value = [b'v'; 128];
    let mut batch = WriteBatch::new();
    for i in 0..KEYS {
        batch.put(&i.to_be_bytes(), &value);
        if batch.buffered_bytes() >= 64 * 1024 {
            db.write(std::mem::take(&mut batch)).unwrap();
        }
    }
    db.write(batch).unwrap();
    db.flush().unwrap();
    db.close().unwrap();
}

/// Damage the middle of the largest SSTable, past its first data block, so a
/// scan gets going and then hits the damage rather than failing at open.
fn damage_a_data_block(dir: &std::path::Path) {
    let mut biggest: Option<(u64, std::path::PathBuf)> = None;
    for entry in walk(dir) {
        if entry.extension().and_then(|e| e.to_str()) != Some("sst") {
            continue;
        }
        let len = std::fs::metadata(&entry).unwrap().len();
        if biggest.as_ref().is_none_or(|(best, _)| len > *best) {
            biggest = Some((len, entry));
        }
    }
    let (len, path) = biggest.expect("the load must have produced an SSTable");
    let mut file = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(&path)
        .unwrap();

    // A whole block's worth of garbage in the middle of the data area. The
    // checksum catches it, which is the point: the read fails rather than
    // returning wrong bytes.
    let offset = len / 3;
    file.seek(SeekFrom::Start(offset)).unwrap();
    let mut original = vec![0u8; 8 * 1024];
    file.read_exact(&mut original).unwrap();
    file.seek(SeekFrom::Start(offset)).unwrap();
    let flipped: Vec<u8> = original.iter().map(|b| !b).collect();
    file.write_all(&flipped).unwrap();
    file.sync_all().unwrap();
}

fn walk(dir: &std::path::Path) -> Vec<std::path::PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&d) else {
            continue;
        };
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
            } else {
                out.push(p);
            }
        }
    }
    out
}

#[test]
fn a_scan_cut_short_by_damage_says_so_instead_of_looking_complete() {
    let dir = tempfile::tempdir().unwrap();
    build(dir.path());
    damage_a_data_block(dir.path());

    let db = Db::open(dir.path(), small_options()).unwrap();
    let mut scan = db.scan_stream(None, None).unwrap();
    let rows = scan.by_ref().count();

    // Either outcome is acceptable on its own; what is not acceptable is a
    // short scan that reports success. If the damage happened to land
    // somewhere a scan never reads, the scan is complete and Ok.
    match scan.status() {
        Err(_) => assert!(
            (rows as u64) < KEYS,
            "status reported a failure, so the scan must not also have returned every row"
        ),
        Ok(()) => assert_eq!(
            rows as u64, KEYS,
            "status reported success, so every row must be there: a short scan \
             reporting Ok is the exact failure this test exists to catch"
        ),
    }
}

/// The iterator form of a cursor carries the failure as an item, so no caller
/// has to remember to ask: a short answer ends with its reason.
#[test]
fn the_entries_of_a_cursor_end_with_an_err_when_damage_cut_them_short() {
    let dir = tempfile::tempdir().unwrap();
    build(dir.path());
    damage_a_data_block(dir.path());

    let db = Db::open(dir.path(), small_options()).unwrap();
    let mut entries = db.snapshot().into_owned_iter().entries();
    let mut rows = 0u64;
    let mut failed = false;
    for item in entries.by_ref() {
        match item {
            Ok(_) => assert!(!failed, "nothing follows the error"),
            Err(_) => failed = true,
        }
        rows += u64::from(!failed);
    }
    assert!(
        entries.next().is_none(),
        "the iterator is finished after the error"
    );
    assert_eq!(
        failed,
        rows < KEYS,
        "a short scan ended with its reason, a full one without"
    );
}

/// The same through a transaction's cursor, a page at a time.
#[test]
fn a_transaction_cursor_cut_short_by_damage_returns_the_error() {
    use regolith::{OptimisticTransactionDb, ScanCheck, ScanDirection};

    let dir = tempfile::tempdir().unwrap();
    build(dir.path());
    damage_a_data_block(dir.path());

    let db = OptimisticTransactionDb::open(dir.path(), small_options()).unwrap();
    let txn = db.begin(&TxnOptions::new());
    let mut cursor = txn.cursor(None, None, ScanDirection::Forward, ScanCheck::Stretch);
    let mut rows = 0u64;
    let outcome = loop {
        match cursor.next_page(&txn, 64 * 1024) {
            Ok(page) => {
                rows += page.entries.len() as u64;
                if page.done {
                    break Ok(());
                }
            }
            Err(e) => break Err(e),
        }
    };
    match outcome {
        Err(_) => {
            assert!(rows < KEYS);
            assert!(cursor.next_page(&txn, 1).is_err(), "the error is final");
        }
        Ok(()) => assert_eq!(rows, KEYS, "a scan that ended must have returned every row"),
    }
}

#[test]
fn an_undamaged_scan_reports_success_and_returns_everything() {
    let dir = tempfile::tempdir().unwrap();
    build(dir.path());

    let db = Db::open(dir.path(), small_options()).unwrap();
    let mut scan = db.scan_stream(None, None).unwrap();
    let rows = scan.by_ref().count();
    scan.status().expect("an intact store must scan clean");
    assert_eq!(rows as u64, KEYS);
}

/// The same contract on the transaction side, stronger: the items carry the
/// error, so a merged stream that loses its snapshot cursor cannot finish on
/// the buffered writes alone and look like a range that ended.
#[test]
fn a_transaction_scan_cut_short_says_so_too() {
    use regolith::TransactionDb;

    let dir = tempfile::tempdir().unwrap();
    let tdb = TransactionDb::open(dir.path(), small_options()).unwrap();
    for i in 0..10u64 {
        tdb.db().put(format!("k{i:02}").as_bytes(), b"v").unwrap();
    }

    let txn = tdb.begin(&TxnOptions::new());
    txn.put(b"zzz", b"buffered").unwrap();

    let rows: Vec<_> = txn.scan_stream(None, None).collect();
    assert_eq!(rows.len(), 11, "ten committed rows plus the buffered write");
    assert!(rows.iter().all(Result::is_ok));

    // Closing the database makes every iterator built afterwards carry a
    // terminal error. The stream must hand it out as an item, not return the
    // one buffered write and look like a complete range.
    tdb.db().close().unwrap();

    let after: Vec<_> = txn.scan_stream(None, None).collect();
    assert!(
        after.last().is_some_and(Result::is_err),
        "the snapshot side died, so the scan must end with the reason rather than \
         read as a complete range of {} rows",
        after.len()
    );
    assert_eq!(after.iter().filter(|item| item.is_err()).count(), 1);
}
