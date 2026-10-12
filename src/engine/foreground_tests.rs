//! A foreground job and the stop its hold on the compaction gate kept
//! stopped writers from relieving.

use std::sync::Arc;
use std::sync::mpsc;

use tempfile::TempDir;

use crate::{Db, Error, IngestOptions, Options, SstFileWriter, WouldBlock};

/// One L0 table stops every write; no worker, inline compaction on, so a
/// stopped writer relieves the stop with compaction steps of its own.
fn stopped_db(dir: &std::path::Path) -> Arc<Db> {
    let options = Options::default()
        .max_background_compactions(0)
        .inline_compaction(true)
        .l0_compaction_trigger(1)
        .level0_slowdown_writes_trigger(1)
        .level0_stop_writes_trigger(1);
    let db = Arc::new(Db::open(dir, options).unwrap());
    db.put(b"m", b"in L0").unwrap();
    db.flush().unwrap();
    assert_eq!(
        db.get_int_property("regolith.num-files-at-level0"),
        Some(1),
        "setup: one table in L0"
    );
    db
}

/// A writer stopped while an ingest holds the compaction gate finds its
/// relief contended and waits for the thread holding the gate. The ingest,
/// once it releases the gate, relieves the stop, so the wait completes. With
/// no relief after the job, nothing would ever compact and the writer would
/// wait for good.
#[test]
fn a_writer_stopped_during_an_ingest_is_relieved_when_the_ingest_ends() {
    let dir = TempDir::new().unwrap();
    let db = stopped_db(dir.path());
    // Keys far from the L0 table's, so the ingest lands below L0 and adds
    // nothing to the stop.
    let source = dir.path().join("external.sst");
    let mut writer = SstFileWriter::create(&source, &Options::default()).unwrap();
    writer.put(b"z-ingested", b"v").unwrap();
    writer.finish().unwrap();

    let (sent, received) = mpsc::channel();
    {
        let db = Arc::clone(&db);
        // Runs on this thread, under the gate and the pipeline, after the
        // ingest took its sequence.
        super::super::ingest::after_next_ingest_seq(move || {
            let (put, outcome) = mpsc::channel();
            std::thread::spawn(move || put.send(db.put(b"late", b"v")));
            // A write the stop did not refuse would wait for the pipeline this
            // thread holds: bounded, so that fails the test instead.
            let outcome = outcome
                .recv_timeout(std::time::Duration::from_secs(10))
                .expect("setup: the write was not stopped and waits for the pipeline");
            sent.send(outcome).unwrap();
        });
    }
    db.ingest_external_files(std::slice::from_ref(&source), IngestOptions::default())
        .wait()
        .unwrap();
    let wait = match received.recv().unwrap() {
        Err(Error::WouldBlock(WouldBlock::Stall(wait))) => wait,
        other => panic!("setup: the write met the stop while the gate was held: {other:?}"),
    };
    assert!(
        wait.is_ready(),
        "the stop the ingest's gate kept the writer from relieving was left in place"
    );
    db.put(b"late", b"v").unwrap();
    assert_eq!(db.get(b"z-ingested").unwrap(), Some(b"v".to_vec()));
}
