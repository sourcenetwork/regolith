//! Concurrent durable writers share an fsync, through the public API, with
//! the overlap made certain instead of left to the scheduler.
//!
//! Group commit amortises an fsync across writers that are inside the commit
//! path at the same time. Threads started together need luck to overlap: on
//! one or two cores, or on a filesystem whose fsync returns at once, each
//! write can finish before the next begins, and every write then forms a
//! group of its own. So the test holds the pipeline, as a leader in the
//! middle of a group does, until every writer's first write is queued behind
//! it, and only then lets them go. That first group forms on any core count
//! and any filesystem.

use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

use tempfile::TempDir;

use crate::{Db, DurabilityMode, Options, Statistics, Ticker};

/// Wait, with a deadline and a bounded backoff, until the commit ring is
/// full: one ticket per writer, since there are as many writers as slots.
fn wait_until_every_writer_is_queued(db: &Db) {
    let deadline = Instant::now() + Duration::from_secs(60);
    let mut pause = Duration::from_micros(50);
    while !db.engine.commit_ring.is_full() {
        assert!(
            Instant::now() < deadline,
            "the writers never queued behind the held pipeline"
        );
        thread::sleep(pause);
        pause = (pause * 2).min(Duration::from_millis(20));
    }
}

#[test]
fn concurrent_durable_writers_cost_far_fewer_fsyncs_than_writes() {
    let dir = TempDir::new().unwrap();
    let stats = Arc::new(Statistics::new());
    let db = Arc::new(
        Db::open(
            dir.path(),
            Options::default()
                .durability(DurabilityMode::Immediate)
                .statistics(Some(Arc::clone(&stats))),
        )
        .unwrap(),
    );

    // One writer per ring slot, so a full ring means every writer is queued.
    // The ring's own count: it may round the size it was asked for.
    let writers = db.engine.commit_ring.capacity();
    // About two thousand durable writes in all, as many per writer as that
    // takes, and at least two so writers go on after the held group.
    let per_writer = 2000usize.div_ceil(writers).max(2);

    // Held as a leader holds it while its group is written and synced: a
    // writer that arrives cannot lead, so it queues its ticket and parks.
    let held = db.engine.pipeline.lock();
    let handles: Vec<_> = (0..writers)
        .map(|w| {
            let db = Arc::clone(&db);
            thread::spawn(move || {
                for i in 0..per_writer {
                    crate::through_stalls(|| db.put(format!("w{w}k{i:05}").as_bytes(), b"value"))
                        .unwrap();
                }
            })
        })
        .collect();
    wait_until_every_writer_is_queued(&db);
    assert_eq!(
        stats.get_ticker(Ticker::WalSyncCount),
        0,
        "nothing commits while the pipeline is held"
    );
    drop(held);
    for handle in handles {
        handle.join().unwrap();
    }

    let writes = (writers * per_writer) as u64;
    let syncs = stats.get_ticker(Ticker::WalSyncCount);
    assert!(syncs >= 1, "durable writes must reach stable storage");

    // Every write that returned Ok must be readable.
    for w in 0..writers {
        for i in 0..per_writer {
            let key = format!("w{w}k{i:05}");
            assert_eq!(
                db.get(key.as_bytes()).unwrap(),
                Some(b"value".to_vec()),
                "every write that returned Ok must be readable"
            );
        }
    }

    // The writes queued behind the held pipeline went out in groups of two
    // or more, one fsync a group, so that wave alone saved an fsync for
    // every second writer.
    assert!(
        syncs <= writes - (writers as u64 / 2),
        "{writers} writers queued behind one leader must share fsyncs: \
         {syncs} syncs for {writes} durable writes"
    );
    assert!(
        syncs < writes,
        "group commit never amortised an fsync across {writers} concurrent writers: \
         every write formed its own group"
    );
    println!("group commit: {syncs} syncs for {writes} durable writes");
}
