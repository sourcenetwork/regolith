//! A stopped write is told when the engine fails (E35).
//!
//! A write a stall stopped waits on the stall's unit, and the unit lands when
//! the stall clears. An engine that latches a failure will not clear it:
//! every later write fails before it does any of the work that would. So the
//! latch lands the unit, and the stopped write, run again, gets the error a
//! fresh write gets. A rotation that flushed and then could not seal changed
//! what the stall counts, so it re-classifies on its way out too.
//!
//! Each test stops a write first and fails the engine second, through the
//! log sync a rotation or a flush makes (`wal::fault`), and none sleeps: a
//! flush is held in flight by a prefix extractor, and a blocked thread is
//! watched through a channel with a deadline.

use std::sync::{Arc, Mutex, mpsc};
use std::time::{Duration, Instant};

use super::tests::{HeldFlush, stopped_engine_with};
use crate::column_family::{DEFAULT_CF_ID, prefix_key};
use crate::engine::background_health::Job;
use crate::engine::wal::wal_filename;
use crate::engine::wal_rotation_tests::SyncFault;
use crate::engine::{DurabilityMode, EngineOptions, RegolithEngine};
use crate::portability::{AtomicBool, Ordering};
use crate::{Db, Error, IoBudget, Options, StallWait, WouldBlock, WriteBatchOp};

/// How long a test waits for another thread before it calls the wait a hang.
const DEADLINE: Duration = Duration::from_secs(60);

/// One 1 KiB put, applied below the stall admission as an admitted write is.
fn fill(engine: &RegolithEngine, key: &[u8]) -> std::io::Result<u64> {
    let ops = vec![WriteBatchOp::Put {
        key: prefix_key(DEFAULT_CF_ID, key),
        value: vec![7u8; 1024],
    }];
    engine.apply_batch(ops, DurabilityMode::Eventual, false)
}

/// A flush holder, the channel that says a flush entered it, and the one
/// that lets the flush go.
fn held_flush() -> (Arc<HeldFlush>, mpsc::Receiver<()>, mpsc::Sender<()>) {
    let (entered, when_entered) = mpsc::channel();
    let (release, when_released) = mpsc::channel();
    let held = Arc::new(HeldFlush {
        armed: AtomicBool::new(false),
        entered: Mutex::new(entered),
        release: Mutex::new(when_released),
    });
    (held, when_entered, release)
}

/// The wait of a write the stall stops now.
fn stopped_write(engine: &RegolithEngine) -> StallWait {
    match engine.admit_write(false) {
        Err(Error::WouldBlock(WouldBlock::Stall(wait))) => wait,
        other => panic!("the write was not stopped: {other:?}"),
    }
}

/// What a fresh write is told on this engine now.
fn fresh_write_error(engine: &RegolithEngine) -> String {
    Error::from(fill(engine, b"fresh").expect_err("the engine takes no write")).to_string()
}

/// A stopped write, run again on a latched engine, gets what a fresh write
/// gets, and that is the latch.
fn assert_told_the_latch(engine: &RegolithEngine) {
    let told = engine
        .admit_write(false)
        .expect_err("a latched engine admits no write")
        .to_string();
    assert!(told.contains("unknown state"), "{told}");
    assert_eq!(told, fresh_write_error(engine));
}

/// No worker, one L0 table at the stop, no step that relieves it, a 2 KiB
/// buffer, and `held` in every flush.
fn stopped_engine_where_writers_relieve(
    held: &Arc<HeldFlush>,
    max_write_buffer_number: usize,
) -> (tempfile::TempDir, Arc<RegolithEngine>) {
    stopped_engine_with(EngineOptions {
        inline_compaction: true,
        l0_compaction_trigger: 100,
        write_buffer_size: 2 * 1024,
        max_write_buffer_number,
        prefix_extractor: Some(held.clone()),
        ..EngineOptions::default()
    })
}

/// A worker, one L0 table at the stop, and a compaction trigger the worker
/// never reaches: stopped writes wait for a relief that does not come.
fn stopped_engine_with_a_worker() -> (tempfile::TempDir, Arc<RegolithEngine>) {
    let dir = tempfile::TempDir::new().unwrap();
    let engine = RegolithEngine::open(
        dir.path(),
        EngineOptions {
            max_background_compactions: 1,
            level0_stop_writes_trigger: 1,
            l0_compaction_trigger: 100,
            ..EngineOptions::default()
        },
    )
    .unwrap();
    fill(&engine, b"k").unwrap();
    engine.flush_active_memtable().unwrap();
    assert!(matches!(engine.stall_signal().classify(), Some((_, true))));
    (dir, engine)
}

/// Latch the engine as a flush whose log cannot be synced does.
fn latch_through_a_flush(dir: &tempfile::TempDir, engine: &RegolithEngine) -> SyncFault {
    fill(engine, b"unflushed").unwrap();
    let fault = SyncFault::arm(dir);
    let err = engine
        .flush_active_memtable()
        .expect_err("the flush seals a log it cannot sync");
    assert!(
        err.to_string().contains("injected WAL sync failure"),
        "{err}"
    );
    fault
}

/// With a worker: a write waits for the worker to relieve the stop, the
/// engine latches, and the write is told at once, not when the stop clears.
#[test]
fn a_latched_engine_tells_the_write_waiting_for_the_worker() {
    let (dir, engine) = stopped_engine_with_a_worker();
    let wait = stopped_write(&engine);
    assert!(!wait.is_ready());
    let _fault = latch_through_a_flush(&dir, &engine);
    assert!(
        wait.is_ready(),
        "the engine latched and the stopped write was not told"
    );
    assert_told_the_latch(&engine);
}

/// A write that meets the stop after the latch is told the latch, and is
/// handed no wait.
#[test]
fn a_write_stopped_on_a_latched_engine_is_told_the_latch() {
    let (dir, engine) = stopped_engine_with_a_worker();
    let _fault = latch_through_a_flush(&dir, &engine);
    assert!(matches!(engine.stall_signal().classify(), Some((_, true))));
    assert_told_the_latch(&engine);
}

/// The latch is the answer even where the stop has another one to give: the
/// relief that would clear it is failing too, and a fresh write is told the
/// latch, so the stopped one is.
#[test]
fn a_write_stopped_on_a_latched_engine_is_told_the_latch_before_a_failing_relief() {
    let (dir, engine) = stopped_engine_with_a_worker();
    let _fault = latch_through_a_flush(&dir, &engine);
    engine.background_health.record_failure(
        Job::Compaction,
        &std::io::Error::other("the relief is failing"),
    );
    assert_told_the_latch(&engine);
}

/// A wait recorded on a queue is completed at that queue's poll once the
/// engine latched.
#[test]
fn a_latched_engine_completes_a_wait_on_a_queue_at_its_poll() {
    let (dir, engine) = stopped_engine_with_a_worker();
    let mut queue = engine.io_queue();
    let wait = stopped_write(&engine);
    assert_eq!(wait.queue(), Some(queue.id()));
    queue.poll(IoBudget::ALL);
    assert!(!wait.is_ready());
    let _fault = latch_through_a_flush(&dir, &engine);
    queue.poll(IoBudget::ALL);
    assert!(
        wait.is_ready(),
        "the engine latched and the wait on the queue was not completed"
    );
    assert_told_the_latch(&engine);
}

/// The blocking form, through the public calls: a thread waits out the
/// stall, the engine latches, and the thread's write returns the latch
/// instead of waiting until the database closes.
#[test]
fn a_thread_waiting_out_a_stall_returns_the_latch() {
    let dir = tempfile::TempDir::new().unwrap();
    let db = Db::open(
        dir.path(),
        Options::default()
            .level0_slowdown_writes_trigger(1)
            .level0_stop_writes_trigger(1)
            .l0_compaction_trigger(100),
    )
    .unwrap();
    db.put(b"k", b"v").unwrap();
    db.flush().unwrap();
    // Admitted before the stop is looked at again: below the admission, as
    // a write that was let in is.
    fill(db.engine(), b"unflushed").unwrap();

    let (told, when_told) = mpsc::channel();
    std::thread::scope(|scope| {
        scope.spawn(|| {
            let outcome = crate::through_stalls(|| db.put(b"stopped", b"v"));
            told.send(outcome.map_err(|err| err.to_string())).unwrap();
        });
        // The write is stopped once the stall has its unit.
        let deadline = Instant::now() + DEADLINE;
        while !db.engine().stall_signal().has_unit() {
            assert!(Instant::now() < deadline, "the write was never stopped");
            std::thread::yield_now();
        }
        let _fault = SyncFault::arm(&dir);
        db.flush()
            .expect_err("the flush seals a log it cannot sync");
        let outcome = when_told.recv_timeout(DEADLINE);
        if outcome.is_err() {
            // Closing completes every wait, so the thread ends and this
            // test fails instead of hanging with it.
            let _ = db.close();
        }
        let outcome =
            outcome.expect("the stopped write was still waiting after the engine latched");
        let told = outcome.expect_err("a latched engine takes no write");
        assert!(told.contains("unknown state"), "{told}");
        assert_eq!(told, db.put(b"fresh", b"v").unwrap_err().to_string());
    });
}

/// No worker: a write whose own step finds another writer's owed flush in
/// flight waits for that writer. The engine latches while the flush is
/// still in flight, and the write is told then, not when the flush ends.
#[test]
fn a_latched_engine_tells_the_write_a_flush_in_flight_holds_off() {
    let (held, when_entered, release) = held_flush();
    let (dir, engine) = stopped_engine_where_writers_relieve(&held, 4);
    // Two 1 KiB puts fill the buffer, so the third seals it, and the step
    // that write owes flushes it.
    fill(&engine, b"a").unwrap();
    fill(&engine, b"b").unwrap();
    held.armed.store(true, Ordering::Release);
    std::thread::scope(|scope| {
        scope.spawn(|| fill(&engine, b"c").unwrap());
        when_entered
            .recv_timeout(DEADLINE)
            .expect("the sealing write never flushed");
        let wait = stopped_write(&engine);
        assert!(!wait.is_ready());
        // The buffer is full again, and the rotation that seals it cannot
        // sync its log. Under the memtable cap it flushes nothing first.
        fill(&engine, b"d").unwrap();
        let _fault = SyncFault::arm(&dir);
        let err = fill(&engine, b"e").expect_err("the rotation seals a log it cannot sync");
        assert!(
            err.to_string().contains("injected WAL sync failure"),
            "{err}"
        );
        let told = wait.is_ready();
        release.send(()).unwrap();
        assert!(
            told,
            "the engine latched and the write the flush held off was not told"
        );
    });
    assert_told_the_latch(&engine);
}

/// The memtable frozen under a full active one, with nothing owed for it: a
/// rotation at the memtable cap flushes it in its turn of the commit
/// pipeline.
fn freeze_one_and_fill_the_next(engine: &RegolithEngine) {
    fill(engine, b"a").unwrap();
    engine.seal_active().unwrap();
    fill(engine, b"b").unwrap();
    fill(engine, b"c").unwrap();
    assert_eq!(engine.view.load().frozen.len(), 1);
}

/// No worker: a write waits for the flush a rotation at the memtable cap
/// has in flight. The flush succeeds, the rotation then cannot sync the log
/// it seals, the engine latches, and that writer returns its error. The
/// stopped write is told, where it used to wait until the database closed.
#[test]
fn a_rotation_that_latches_after_its_flush_tells_the_write_it_held_off() {
    let (held, when_entered, release) = held_flush();
    let (dir, engine) = stopped_engine_where_writers_relieve(&held, 2);
    freeze_one_and_fill_the_next(&engine);
    held.armed.store(true, Ordering::Release);
    let _fault = SyncFault::arm(&dir);
    let wait = std::thread::scope(|scope| {
        let rotating = scope.spawn(|| fill(&engine, b"d"));
        when_entered
            .recv_timeout(DEADLINE)
            .expect("the rotation never flushed the frozen memtable");
        let wait = stopped_write(&engine);
        assert!(!wait.is_ready());
        release.send(()).unwrap();
        let err = rotating
            .join()
            .unwrap()
            .expect_err("the rotation seals a log it cannot sync");
        assert!(
            err.to_string().contains("injected WAL sync failure"),
            "{err}"
        );
        wait
    });
    assert_eq!(
        engine.view.load().version.levels[0].len(),
        2,
        "setup: the rotation's flush installed its table"
    );
    assert!(
        wait.is_ready(),
        "the rotation latched the engine after its flush and the write it held off was not told"
    );
    assert_told_the_latch(&engine);
}

/// Make the next log a rotation creates impossible to create, without
/// latching anything: its name is taken by a directory. The rotation's flush
/// takes the next file id and its seal the one after.
fn block_the_next_log(engine: &RegolithEngine) {
    let next = engine.versions.current().next_file_id;
    std::fs::create_dir(engine.wal_dir.join(wal_filename(next + 1))).unwrap();
}

/// No worker: the same rotation, whose seal fails with nothing latched (the
/// next log cannot be created). Its flush took a memtable out and put a
/// table in, so it re-classifies on its way out and the write it held off
/// looks again.
#[test]
fn a_rotation_whose_seal_fails_after_its_flush_hands_the_stop_back() {
    let (held, when_entered, release) = held_flush();
    let (_dir, engine) = stopped_engine_where_writers_relieve(&held, 2);
    freeze_one_and_fill_the_next(&engine);
    block_the_next_log(&engine);
    held.armed.store(true, Ordering::Release);
    let wait = std::thread::scope(|scope| {
        let rotating = scope.spawn(|| fill(&engine, b"d"));
        when_entered
            .recv_timeout(DEADLINE)
            .expect("the rotation never flushed the frozen memtable");
        let wait = stopped_write(&engine);
        assert!(!wait.is_ready());
        release.send(()).unwrap();
        rotating
            .join()
            .unwrap()
            .expect_err("the rotation cannot create the next log");
        wait
    });
    engine
        .ensure_writable()
        .expect("setup: nothing latched the engine");
    assert!(
        wait.is_ready(),
        "the rotation changed what the stall counts and the write it held off was not told"
    );
}

/// The same, with the rotating writer on a queue it has not polled: the step
/// its flush left owing waits on that queue, so nothing but the rotation
/// itself can hand the stop back.
#[test]
fn a_rotation_whose_seal_fails_hands_the_stop_back_before_its_writer_polls() {
    let (held, when_entered, release) = held_flush();
    let (_dir, engine) = stopped_engine_where_writers_relieve(&held, 2);
    freeze_one_and_fill_the_next(&engine);
    block_the_next_log(&engine);
    held.armed.store(true, Ordering::Release);
    let (failed, when_failed) = mpsc::channel();
    let (done, when_done) = mpsc::channel::<()>();
    let engine = &engine;
    std::thread::scope(|scope| {
        scope.spawn(move || {
            let _unpolled = engine.io_queue();
            failed.send(fill(engine, b"d").is_err()).unwrap();
            // The queue lives, unpolled, until the test has looked.
            let _ = when_done.recv_timeout(DEADLINE);
        });
        when_entered
            .recv_timeout(DEADLINE)
            .expect("the rotation never flushed the frozen memtable");
        let wait = stopped_write(engine);
        assert!(!wait.is_ready());
        release.send(()).unwrap();
        assert!(
            when_failed
                .recv_timeout(DEADLINE)
                .expect("the rotating write never returned"),
            "the rotation cannot create the next log"
        );
        let told = wait.is_ready();
        done.send(()).unwrap();
        assert!(
            told,
            "the rotation changed what the stall counts and the write it held off was not told"
        );
    });
}

/// The race the flag closes: a write found the engine unlatched when it was
/// admitted, and the latch landed the unit before the write registered on
/// one. Registering reads the flag again, so the write is told the latch
/// and no unit is left that nothing would land.
#[test]
fn a_wait_registered_after_the_latch_is_told_the_latch_and_leaves_no_unit() {
    let (dir, engine) = stopped_engine_with_a_worker();
    let _fault = latch_through_a_flush(&dir, &engine);
    assert!(!engine.stall_signal().has_unit());
    let told = engine.stall_wait(None, "stop", None).to_string();
    assert!(told.contains("unknown state"), "{told}");
    assert_eq!(told, fresh_write_error(&engine));
    assert!(!engine.stall_signal().has_unit());
}
