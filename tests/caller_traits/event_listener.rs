//! `EventListener`: every `on_*` method is called, with what the workload
//! did: the table a flush wrote, the tables a compaction read and wrote, the
//! file an ingest was handed, the failure of a flush, the key a commit lost
//! on, the callback that panicked, and the log tail an open dropped.

use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use regolith::{
    BackgroundErrorReason, CompactionJobInfo, CompactionOutcome, Conflict, Error, EventListener,
    ExternalFileIngestionInfo, FlushJobInfo, IngestOptions, OptimisticTransactionDb, Options,
    SstFileWriter, TableFileCreationInfo, TableFileCreationReason, TableFileDeletionInfo,
    TransactionError, TxnOptions, WalTailDiscardedInfo,
};

use super::faulty_env::{FaultyEnv, logs};

/// One call of a listener method, with what it was handed.
#[derive(Debug, Clone)]
enum Event {
    FlushCompleted(FlushJobInfo),
    CompactionBegin(CompactionJobInfo),
    CompactionCompleted(CompactionJobInfo),
    TableCreated(TableFileCreationInfo),
    TableDeleted(TableFileDeletionInfo),
    Ingested(ExternalFileIngestionInfo),
    BackgroundError(BackgroundErrorReason, String),
    Conflict(Vec<u8>),
    CallbackPanic(&'static str),
    WalTailDiscarded(WalTailDiscardedInfo),
}

/// Records every call, in order.
#[derive(Default)]
struct Recording(Mutex<Vec<Event>>);

impl Recording {
    fn note(&self, event: Event) {
        self.0.lock().unwrap().push(event);
    }

    /// The calls since the last time this was asked.
    fn take(&self) -> Vec<Event> {
        std::mem::take(&mut *self.0.lock().unwrap())
    }
}

impl EventListener for Recording {
    fn on_flush_completed(&self, info: &FlushJobInfo) {
        self.note(Event::FlushCompleted(info.clone()));
    }

    fn on_compaction_begin(&self, info: &CompactionJobInfo) {
        self.note(Event::CompactionBegin(info.clone()));
    }

    fn on_compaction_completed(&self, info: &CompactionJobInfo) {
        self.note(Event::CompactionCompleted(info.clone()));
    }

    fn on_table_file_created(&self, info: &TableFileCreationInfo) {
        self.note(Event::TableCreated(info.clone()));
    }

    fn on_table_file_deleted(&self, info: &TableFileDeletionInfo) {
        self.note(Event::TableDeleted(info.clone()));
    }

    fn on_external_file_ingested(&self, info: &ExternalFileIngestionInfo) {
        self.note(Event::Ingested(info.clone()));
    }

    fn on_background_error(&self, reason: BackgroundErrorReason, err: &Error) {
        self.note(Event::BackgroundError(reason, err.to_string()));
    }

    fn on_conflict(&self, conflict: &Conflict) {
        self.note(Event::Conflict(conflict.key().to_vec()));
    }

    fn on_callback_panic(&self, callback: &'static str) {
        self.note(Event::CallbackPanic(callback));
    }

    fn on_wal_tail_discarded(&self, info: &WalTailDiscardedInfo) {
        self.note(Event::WalTailDiscarded(info.clone()));
    }
}

/// The engine's key for the caller's `key` in the default column family: the
/// form a flush reports its bounds in.
fn stored(key: &[u8]) -> Vec<u8> {
    [&1u32.to_be_bytes()[..], key].concat()
}

fn size_of(path: &Path) -> u64 {
    std::fs::metadata(path).unwrap().len()
}

#[test]
fn every_method_is_called_with_what_the_workload_did() {
    let dir = tempfile::tempdir().unwrap();
    let env = Arc::new(FaultyEnv::default());
    let seen = Arc::new(Recording::default());
    let options = || {
        Options::default()
            .env(env.clone())
            .add_listener(seen.clone())
            .l0_compaction_trigger(2)
            // Nothing flushes or compacts until the test says so.
            .max_background_compactions(0)
            .inline_compaction(false)
    };
    let db = OptimisticTransactionDb::open(dir.path(), options()).unwrap();

    // A flush: the table it wrote, then the flush itself.
    db.db().put(b"a", b"1").unwrap();
    db.db().put(b"c", b"1").unwrap();
    db.db().flush().unwrap();
    let [Event::TableCreated(table), Event::FlushCompleted(flush)] = &seen.take()[..] else {
        panic!("a flush tells of its table and of itself");
    };
    assert_eq!(table.reason, TableFileCreationReason::Flush);
    assert_eq!((table.level, table.num_entries), (0, 2));
    assert_eq!(table.file_size, size_of(&table.file_path));
    assert_eq!(
        (
            flush.file_id,
            &flush.file_path,
            flush.file_size,
            flush.num_entries
        ),
        (table.file_id, &table.file_path, table.file_size, 2)
    );
    assert_eq!(
        (&flush.smallest_key, &flush.largest_key),
        (&stored(b"a"), &stored(b"c"))
    );
    let first = table.file_id;

    // A flush that fails: the failure, by the job that failed.
    db.db().put(b"b", b"2").unwrap();
    env.fail_tables(true);
    assert!(db.db().flush().is_err());
    env.fail_tables(false);
    let [Event::BackgroundError(reason, message)] = &seen.take()[..] else {
        panic!("a failed flush tells of its failure");
    };
    assert_eq!(*reason, BackgroundErrorReason::Flush);
    assert!(message.contains("no room for a table"), "{message}");
    db.db().flush().unwrap();
    let [Event::TableCreated(table), Event::FlushCompleted(_)] = &seen.take()[..] else {
        panic!("the flush that then succeeds tells as any other");
    };
    let second = table.file_id;

    // A compaction: what it starts from, the table it wrote, the tables it
    // removed, and what it ended with.
    assert_eq!(db.db().compact_step().unwrap(), CompactionOutcome::DidWork);
    let events = seen.take();
    let [
        Event::CompactionBegin(begin),
        Event::TableCreated(merged),
        Event::TableDeleted(gone_one),
        Event::TableDeleted(gone_two),
        Event::CompactionCompleted(end),
    ] = &events[..]
    else {
        panic!("a compaction tells of each step: {events:?}");
    };
    assert_eq!((begin.input_level, begin.output_level), (0, 1));
    let mut inputs = begin.input_files_input_level.clone();
    inputs.sort_unstable();
    assert_eq!(inputs, [first, second]);
    assert!(begin.output_files.is_empty());
    assert_eq!(merged.reason, TableFileCreationReason::Compaction);
    assert_eq!((merged.level, merged.num_entries), (1, 3));
    assert_eq!(merged.file_size, size_of(&merged.file_path));
    let mut gone = [gone_one.file_id, gone_two.file_id];
    gone.sort_unstable();
    assert_eq!(gone, [first, second]);
    assert!(!gone_one.file_path.exists() && !gone_two.file_path.exists());
    assert_eq!(end.output_files, [merged.file_id]);
    assert_eq!(end.input_files_input_level, begin.input_files_input_level);

    // An ingest: the table it installed, and the file it was handed.
    let external: PathBuf = dir.path().join("external.sst");
    let mut writer = SstFileWriter::create(&external, &Options::default()).unwrap();
    writer.put(b"z", b"26").unwrap();
    writer.finish().unwrap();
    db.db()
        .ingest_external_files(std::slice::from_ref(&external), IngestOptions::default())
        .wait()
        .unwrap();
    let [Event::TableCreated(table), Event::Ingested(ingested)] = &seen.take()[..] else {
        panic!("an ingest tells of its table and of the file");
    };
    assert_eq!(ingested.external_file_path, external);
    assert_eq!(
        (
            ingested.internal_file_id,
            ingested.level,
            ingested.num_entries
        ),
        (table.file_id, table.level, 1)
    );
    assert_eq!(ingested.file_size, size_of(&table.file_path));

    // A commit that loses: the key it lost on.
    let txn = db.begin(&TxnOptions::new());
    txn.get_for_update(b"a").unwrap();
    db.db().put(b"a", b"9").unwrap();
    txn.put(b"a", b"2").unwrap();
    assert!(matches!(txn.commit(), Err(TransactionError::Conflict(_))));
    let [Event::Conflict(key)] = &seen.take()[..] else {
        panic!("a lost commit tells of its conflict");
    };
    assert_eq!(key, b"a");

    // A callback that panics after its commit: which callback.
    let mut txn = db.begin(&TxnOptions::new());
    txn.put(b"p", b"1").unwrap();
    txn.on_commit(|_| panic!("a test's on_commit panics"));
    txn.commit().unwrap();
    let [Event::CallbackPanic(callback)] = &seen.take()[..] else {
        panic!("a panic in a callback is told");
    };
    assert_eq!(*callback, "on_commit");

    // An open that drops the damaged end of the newest log: where it was.
    drop(db);
    let log = logs(dir.path()).pop().expect("a log");
    let mut bytes = std::fs::read(&log).unwrap();
    *bytes.last_mut().unwrap() ^= 0xFF;
    std::fs::write(&log, &bytes).unwrap();
    seen.take();
    let db = OptimisticTransactionDb::open(dir.path(), options()).unwrap();
    let events = seen.take();
    let tails: Vec<&WalTailDiscardedInfo> = events
        .iter()
        .filter_map(|event| match event {
            Event::WalTailDiscarded(info) => Some(info),
            _ => None,
        })
        .collect();
    let [tail] = &tails[..] else {
        panic!("the open tells of the tail it dropped, once: {events:?}");
    };
    assert_eq!(tail.file_path, log);
    assert_eq!(tail.offset + tail.discarded_bytes, bytes.len() as u64);
    assert!(tail.discarded_bytes > 0);
    drop(db);
}
