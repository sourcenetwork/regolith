//! `RateLimiter::request`, the trait's one method: asked on a compaction
//! worker for the bytes of each table it wrote, at low priority, and never
//! on a caller's thread.

use std::sync::{Arc, Mutex};

use regolith::{
    Db, EventListener, Options, Priority, RateLimiter, TableFileCreationInfo,
    TableFileCreationReason,
};

/// Records every request: the bytes, the priority, and the thread asking.
#[derive(Default)]
struct Recording(Mutex<Vec<(u64, Priority, String)>>);

impl RateLimiter for Recording {
    fn request(&self, bytes: u64, pri: Priority) {
        let thread = std::thread::current().name().unwrap_or("").to_owned();
        self.0.lock().unwrap().push((bytes, pri, thread));
    }
}

/// Records the size of every table a flush or a compaction wrote.
#[derive(Default)]
struct Tables(Mutex<Vec<(TableFileCreationReason, u64)>>);

impl EventListener for Tables {
    fn on_table_file_created(&self, info: &TableFileCreationInfo) {
        self.0.lock().unwrap().push((info.reason, info.file_size));
    }
}

#[test]
fn request_is_asked_on_a_worker_for_the_bytes_of_each_table_it_wrote() {
    let dir = tempfile::tempdir().unwrap();
    let limiter = Arc::new(Recording::default());
    let tables = Arc::new(Tables::default());
    let db = Db::open(
        dir.path(),
        Options::default()
            .rate_limiter(Some(limiter.clone()))
            .add_listener(tables.clone()),
    )
    .unwrap();

    // A flush on the caller's thread is the caller's own I/O: not asked.
    db.put(b"a", b"1").unwrap();
    db.put(b"c", b"1").unwrap();
    db.flush().unwrap();
    assert_eq!(tables.0.lock().unwrap().len(), 1);
    assert!(limiter.0.lock().unwrap().is_empty());

    // The job runs on the worker: it flushes what the memtable holds, then
    // merges the two overlapping tables. Each table it writes is asked for.
    db.put(b"b", b"2").unwrap();
    db.compact_range(None, None).wait().unwrap();

    let written: Vec<(TableFileCreationReason, u64)> = tables.0.lock().unwrap()[1..].to_vec();
    assert!(
        written
            .iter()
            .any(|(reason, _)| *reason == TableFileCreationReason::Flush)
            && written
                .iter()
                .any(|(reason, _)| *reason == TableFileCreationReason::Compaction),
        "the job flushed and compacted: {written:?}"
    );
    let asked = limiter.0.lock().unwrap().clone();
    let mut bytes_asked: Vec<u64> = asked.iter().map(|(bytes, ..)| *bytes).collect();
    let mut bytes_written: Vec<u64> = written.iter().map(|(_, bytes)| *bytes).collect();
    bytes_asked.sort_unstable();
    bytes_written.sort_unstable();
    assert_eq!(
        bytes_asked, bytes_written,
        "one request per table, for the table's size on disk"
    );
    for (_, pri, thread) in &asked {
        assert_eq!(*pri, Priority::Low);
        assert!(
            thread.starts_with("regolith-compaction-"),
            "asked on {thread:?}"
        );
    }
}
