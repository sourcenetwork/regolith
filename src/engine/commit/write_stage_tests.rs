//! The write stage on the code (`write_stage.rs`): a batch writes every
//! record waiting before the caller's in one write, and a blocking writer
//! that finds the claim held parks and still gets its record written.

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::time::Duration;

use tempfile::TempDir;

use super::super::descriptor::WRITTEN;
use super::super::hook::{self, Stage};
use super::super::park::Help;
use super::super::pipeline::Turn;
use super::super::pipeline_tests::{eventual_put, install, open_engine, seq_of};

/// Two decided slots, neither record written: the second's writer writes
/// both, in one batch, the first record first.
#[test]
fn a_batch_writes_the_records_waiting_before_its_own() {
    let dir = TempDir::new().unwrap();
    let engine = open_engine(&dir);
    let pipe = engine.pipe().unwrap();
    let (_, first) = install(&engine, eventual_put(b"first", b"v"));
    let (second_index, second) = install(&engine, eventual_put(b"second", b"v"));
    assert!(matches!(
        engine.help_decide(pipe, second_index, Help::Wait, None),
        Turn::Done
    ));
    assert!(!first.is(WRITTEN) && !second.is(WRITTEN));
    let writes = Arc::new(AtomicUsize::new(0));
    hook::set({
        let writes = Arc::clone(&writes);
        move |stage| {
            if stage == Stage::InWrite {
                writes.fetch_add(1, Ordering::SeqCst);
            }
        }
    });
    engine.write_slot(pipe, &second, Help::Wait);
    hook::clear();
    assert!(first.is(WRITTEN), "the record before the writer's was left");
    assert!(second.is(WRITTEN), "the writer's own record was left");
    assert_eq!(
        writes.load(Ordering::SeqCst),
        1,
        "two records took more than one write"
    );
    engine.drive(pipe, second_index, &second);
    assert!(seq_of(&first).unwrap() < seq_of(&second).unwrap());
}

/// The claim held by a write in flight: a blocking writer parks, and once
/// the patience passed and its record is not in the batch under way, it
/// writes its record itself. Nothing waits for a thread to be scheduled.
#[test]
fn a_writer_that_finds_the_claim_held_parks_and_then_writes_its_own() {
    let dir = TempDir::new().unwrap();
    let engine = open_engine(&dir);
    let pipe = engine.pipe().unwrap();
    let log = Arc::clone(&engine.pipeline_state().unwrap().after.log);
    let held = log
        .count_in(log.epoch(), true)
        .expect("a write of the current epoch is let in");
    assert!(held.claimed());
    let (index, desc) = install(&engine, eventual_put(b"waits", b"v"));
    let parked = Arc::new(AtomicBool::new(false));
    std::thread::scope(|scope| {
        let writer = scope.spawn(|| {
            let parked = Arc::clone(&parked);
            hook::set(move |stage| {
                if stage == Stage::WriteWait {
                    parked.store(true, Ordering::SeqCst);
                }
            });
            engine.drive(pipe, index, &desc);
            hook::clear();
        });
        let deadline = std::time::Instant::now() + Duration::from_secs(30);
        while !writer.is_finished() {
            assert!(
                std::time::Instant::now() < deadline,
                "the writer never got through"
            );
            std::thread::sleep(Duration::from_millis(1));
        }
    });
    assert!(parked.load(Ordering::SeqCst), "the writer never parked");
    assert!(desc.is(WRITTEN));
    seq_of(&desc).unwrap();
    assert_eq!(held.leave(), 0, "the writer still counts as parked");
}

/// W2, WG4 on the code: a record written as a copy, which leaves the
/// written hint where it was, and then made durable by a sync, is not in a
/// batch that comes after: the batch looks at each record after its count
/// in and begins past it, so nothing lands on the synced range again.
#[test]
fn a_batch_leaves_out_a_record_written_and_synced_before_it_counted_in() {
    let dir = TempDir::new().unwrap();
    let engine = open_engine(&dir);
    let pipe = engine.pipe().unwrap();
    let (_, first) = install(&engine, eventual_put(b"first", b"v"));
    let (second_index, second) = install(&engine, eventual_put(b"second", b"v"));
    assert!(matches!(
        engine.help_decide(pipe, second_index, Help::Wait, None),
        Turn::Done
    ));
    engine.write_copy(&first);
    assert!(first.is(WRITTEN));
    let log = Arc::clone(&engine.pipeline_state().unwrap().after.log);
    let second_at = second.decision().unwrap().place.unwrap().offset;
    log.sync_through(second_at).unwrap();
    assert!(log.durable() >= second_at, "the first record is durable");
    engine.write_slot(pipe, &second, Help::Wait);
    assert!(second.is(WRITTEN));
    let (offset, _) = super::last_batch();
    assert_eq!(
        offset, second_at,
        "a batch began on a record written and synced before it counted in"
    );
    engine.drive(pipe, second_index, &second);
    seq_of(&second).unwrap();
}
