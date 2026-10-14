//! The write unit (`write_unit.rs`) against a real database: records reach
//! the log in runs, one host write each; the holder writes only records
//! their owners filled, and looks at them again once counted in; a commit
//! whose record another thread is slow to write writes it itself after a
//! bounded patience; and a `commit_nowait` commit leaves the unit on its
//! queue. Each test drives the pipeline step by step, or stops a thread at a
//! hook, so nothing depends on timing but the patience itself.

use std::sync::mpsc;
use std::thread;
use std::time::Duration;

use tempfile::TempDir;

use super::descriptor::{Descriptor, FILLED, WRITTEN};
use super::hook::{self, Stage};
use super::pipeline::Turn;
use super::pipeline_tests::{eventual_put, install, key, seq_of, stopped_at};
use super::write_unit::{Await, Brought, CLAIMED, QUEUED, WANTED, WriteUnit};
use super::*;
use crate::engine::EngineOptions;
use crate::engine::recovery_tests::RecordingEnv;

const DEADLINE: Duration = Duration::from_secs(30);

/// An engine whose log writes are recorded, one entry per host write.
fn recorded(dir: &TempDir) -> (Arc<RegolithEngine>, Arc<RecordingEnv>) {
    let recording = Arc::new(RecordingEnv::default());
    let engine = RegolithEngine::open(
        dir.path(),
        EngineOptions {
            env: recording.clone(),
            ..EngineOptions::default()
        },
    )
    .expect("engine open");
    (engine, recording)
}

/// The length of every host write to a log since the last call.
fn writes_since(recording: &RecordingEnv) -> Vec<usize> {
    let mut events = recording.events.lock().unwrap();
    let lens = events.writes.iter().map(Vec::len).collect();
    events.writes.clear();
    lens
}

/// The bytes slot `desc`'s record takes in the log.
fn record_len(desc: &Descriptor) -> usize {
    desc.decision()
        .and_then(|decision| decision.place)
        .map_or(0, |place| place.len as usize)
}

/// Install `names` as eventual puts and decide every one of them, on this
/// thread, without filling or writing any record.
fn decided(engine: &RegolithEngine, names: &[&[u8]]) -> Vec<(u64, RingArc<Descriptor>)> {
    let slots: Vec<_> = names
        .iter()
        .map(|name| install(engine, eventual_put(name, b"v")))
        .collect();
    let pipe = engine.pipe().unwrap();
    let last = slots.last().map_or(0, |(index, _)| *index);
    assert!(matches!(
        engine.help_decide(pipe, last, Help::Wait, None),
        Turn::Done
    ));
    slots
}

#[test]
fn filled_records_go_to_the_log_in_one_host_write() {
    let dir = TempDir::new().unwrap();
    let (engine, recording) = recorded(&dir);
    let slots = decided(&engine, &[b"a", b"b", b"c"]);
    for (_, desc) in &slots {
        engine.fill(desc);
        assert!(desc.is(FILLED));
    }
    writes_since(&recording);
    let pipe = engine.pipe().unwrap();
    let (last_index, last) = &slots[2];
    assert!(matches!(
        engine.bring_written(pipe, last, Await::Park),
        Brought::Written
    ));
    let lens: usize = slots.iter().map(|(_, desc)| record_len(desc)).sum();
    assert_eq!(
        writes_since(&recording),
        vec![lens],
        "the three records went to the log in one host write"
    );
    for (_, desc) in &slots {
        assert!(
            desc.is(WRITTEN),
            "every record of the run is marked written"
        );
    }
    engine.drive(pipe, *last_index, last);
    for ((_, desc), name) in slots.iter().zip([b"a", b"b", b"c"]) {
        seq_of(desc).unwrap();
        assert_eq!(
            engine.get(&key(name), u64::MAX).unwrap(),
            Some(b"v".to_vec())
        );
    }
}

/// WU2: the holder writes only records their owners filled. A record its
/// owner has not filled ends the run before it, and the holder encodes none.
#[test]
fn a_run_stops_at_a_record_its_owner_has_not_filled() {
    let dir = TempDir::new().unwrap();
    let (engine, recording) = recorded(&dir);
    let slots = decided(&engine, &[b"a", b"b", b"c"]);
    engine.fill(&slots[0].1);
    engine.fill(&slots[2].1);
    writes_since(&recording);
    let pipe = engine.pipe().unwrap();
    assert!(matches!(
        engine.bring_written(pipe, &slots[2].1, Await::Park),
        Brought::Written
    ));
    assert_eq!(
        writes_since(&recording),
        vec![record_len(&slots[0].1), record_len(&slots[2].1)],
        "two runs, one on each side of the record nobody filled"
    );
    let gap = &slots[1].1;
    assert!(
        !gap.is(FILLED) && !gap.is(WRITTEN),
        "the holder encoded a record its owner had not filled"
    );
    let (last_index, last) = &slots[2];
    engine.drive(pipe, *last_index, last);
    for (_, desc) in &slots {
        seq_of(desc).unwrap();
    }
}

/// WU3: a run looks at its records again once it counted in. A record a copy
/// wrote between the gather and the count in is left out, with the records
/// after it.
#[test]
fn a_run_leaves_out_a_record_written_after_it_was_gathered() {
    let dir = TempDir::new().unwrap();
    let (engine, recording) = recorded(&dir);
    let slots = decided(&engine, &[b"a", b"b"]);
    for (_, desc) in &slots {
        engine.fill(desc);
    }
    writes_since(&recording);
    let pipe = engine.pipe().unwrap();
    let second = RingArc::clone(&slots[1].1);
    let copier = Arc::clone(&engine);
    let mut fired = false;
    hook::set(move |stage| {
        if stage == Stage::Write && !fired {
            fired = true;
            // Gathered, not counted in yet: another thread copies the
            // second record now.
            copier.copy_record(&second);
        }
    });
    let brought = engine.bring_written(pipe, &slots[0].1, Await::Park);
    hook::clear();
    assert!(matches!(brought, Brought::Written));
    assert_eq!(
        writes_since(&recording),
        vec![record_len(&slots[1].1), record_len(&slots[0].1)],
        "the copy of the second record, then a run of the first alone"
    );
    let (last_index, last) = &slots[1];
    engine.drive(pipe, *last_index, last);
    for (_, desc) in &slots {
        seq_of(desc).unwrap();
    }
}

/// Run `call` on its own thread and wait for it for at most `DEADLINE`: a
/// call that never returns fails the test instead of hanging it.
fn within_deadline<T: Send + 'static>(call: impl FnOnce() -> T + Send + 'static) -> T {
    let (done, finished) = mpsc::channel();
    thread::spawn(move || {
        let _ = done.send(call());
    });
    finished
        .recv_timeout(DEADLINE)
        .expect("the call waited on a stopped thread without bound")
}

/// WU5: a commit whose record waits behind a holder that stopped with the
/// unit claimed writes its record, and the holder's, itself once its
/// patience ran out. The holder, let go on, finds its record written and
/// writes nothing.
#[test]
fn a_commit_behind_a_stopped_holder_writes_the_records_itself() {
    let dir = TempDir::new().unwrap();
    let (engine, recording) = recorded(&dir);
    let holder = Arc::clone(&engine);
    let behind = Arc::clone(&engine);
    let held = stopped_at(
        Stage::Write,
        move || holder.submit(eventual_put(b"held", b"v")),
        move || {
            writes_since(&recording);
            within_deadline(move || behind.submit(eventual_put(b"behind", b"v")))
                .expect("the commit behind the stopped holder");
            assert_eq!(
                writes_since(&recording).len(),
                2,
                "the commit behind wrote its record and the holder's, one copy each"
            );
        },
    );
    held.expect("the holder's commit, written by the commit behind it");
    assert_eq!(
        engine.get(&key(b"held"), u64::MAX).unwrap(),
        Some(b"v".to_vec())
    );
    assert_eq!(
        engine.get(&key(b"behind"), u64::MAX).unwrap(),
        Some(b"v".to_vec())
    );
}

/// WU5 for a record its owner is encoding: an owner that stopped after it
/// claimed the encoding of its record, before it filled it, holds nobody up
/// for longer than the patience. The commit behind it encodes the record on
/// its own thread and writes it as a copy.
#[test]
fn a_commit_behind_an_owner_that_stopped_while_it_encoded_writes_its_record() {
    let dir = TempDir::new().unwrap();
    let engine = RegolithEngine::open(dir.path(), EngineOptions::default()).unwrap();
    let owner = Arc::clone(&engine);
    let behind = Arc::clone(&engine);
    let stopped = stopped_at(
        Stage::Fill,
        move || owner.submit(eventual_put(b"owner", b"v")),
        move || {
            let staged = within_deadline(move || {
                behind
                    .submit(eventual_put(b"behind", b"v"))
                    .expect("the commit behind");
                super::write_unit::stage_buffer().0
            });
            assert!(
                staged > 0,
                "the commit behind encoded the stopped owner's record on its own thread"
            );
        },
    );
    stopped.expect("the owner's commit, written by the commit behind it");
    assert_eq!(
        engine.get(&key(b"owner"), u64::MAX).unwrap(),
        Some(b"v".to_vec())
    );
}

/// D4: a record nobody is encoding is encoded by the thread that needs it
/// written, into the slot's own descriptor, and goes out in a run like any
/// other: no park on an owner that is not running, and no copy. Here the
/// owner stopped before it decided its slot; the commit behind decides it,
/// encodes its record, and writes it.
#[test]
fn a_record_nobody_encoded_is_encoded_by_the_thread_that_needs_it() {
    let dir = TempDir::new().unwrap();
    let engine = RegolithEngine::open(dir.path(), EngineOptions::default()).unwrap();
    let owner = Arc::clone(&engine);
    let behind = Arc::clone(&engine);
    let stopped = stopped_at(
        Stage::Decide,
        move || owner.submit(eventual_put(b"owner", b"v")),
        move || {
            let staged = within_deadline(move || {
                behind
                    .submit(eventual_put(b"behind", b"v"))
                    .expect("the commit behind");
                super::write_unit::stage_buffer().0
            });
            assert_eq!(
                staged, 0,
                "the commit behind copied the owner's record instead of encoding it into its slot"
            );
        },
    );
    stopped.expect("the owner's commit, encoded and written by the commit behind it");
    assert_eq!(
        engine.get(&key(b"owner"), u64::MAX).unwrap(),
        Some(b"v".to_vec())
    );
}

/// D53: a `commit_nowait` commit that finds the unit claimed by another
/// thread leaves it on its queue and returns at once, unpublished; its queue
/// is told when the holder lets the unit go, and the commit lands then.
#[test]
fn a_nowait_commit_leaves_a_claimed_unit_on_its_queue() {
    let dir = TempDir::new().unwrap();
    let db = crate::OptimisticTransactionDb::open(dir.path(), crate::Options::default()).unwrap();
    let mut queue = db.db().io_queue();
    let options = crate::TxnOptions::new().io_queue(queue.id());
    // The unit claimed, as by a holder in the middle of its run: a lone
    // writer takes the fast path (WU8) and never holds it.
    let writes = &db.db().engine.pipe().unwrap().writes;
    let claimed = writes.try_claim().expect("a free unit is claimed");
    let tx = db.begin(&options);
    tx.put(b"nowait", b"v").unwrap();
    let left = tx.commit_nowait();
    assert!(
        !left.is_ready(),
        "the commit was written beside the holder instead of left on its queue"
    );
    // The holder lets go and tells the queues left on it, as Claim's drop
    // does.
    if writes.release(claimed) & QUEUED != 0 {
        writes.tell_line();
    }
    queue
        .block_on(left)
        .expect("the commit lands once the holder lets the unit go");
    assert_eq!(db.db().get(b"nowait").unwrap(), Some(b"v".to_vec()));
}

/// The unit's word: one claim at a time; a note goes only on the claim it
/// was meant for, and its holder reads it when it lets go.
#[test]
fn the_unit_takes_one_claim_and_hands_its_holder_the_notes() {
    let unit = WriteUnit::new(0);
    let claimed = unit.try_claim().expect("a free unit is claimed");
    assert_ne!(claimed & CLAIMED, 0);
    assert_eq!(
        unit.try_claim(),
        Err(claimed),
        "a claimed unit is not claimed again"
    );
    assert!(unit.holds(claimed));
    assert!(unit.note(claimed, WANTED), "a note on the claim in place");
    assert_eq!(
        unit.release(claimed),
        WANTED,
        "the holder reads the note when it lets go"
    );
    assert!(!unit.holds(claimed), "the claim was let go");
    assert!(
        !unit.note(claimed, WANTED),
        "a note for a claim that was let go is refused"
    );
    let again = unit.try_claim().expect("a let go unit is claimed again");
    assert_ne!(again, claimed, "a later claim is told from the earlier one");
    assert_eq!(
        unit.release(again),
        0,
        "a claim nobody noted hands back no note"
    );
}

/// Many writers at once: every commit lands, and a reopened database
/// replays every record, whichever thread wrote which run.
#[test]
fn concurrent_commits_through_runs_all_land_and_replay() {
    let dir = TempDir::new().unwrap();
    {
        let engine = RegolithEngine::open(dir.path(), EngineOptions::default()).unwrap();
        thread::scope(|scope| {
            for t in 0..8u32 {
                let engine = &engine;
                scope.spawn(move || {
                    for i in 0..200u32 {
                        let name = format!("k{t}-{i}");
                        engine.submit(eventual_put(name.as_bytes(), b"v")).unwrap();
                    }
                });
            }
        });
        for t in 0..8u32 {
            for i in 0..200u32 {
                let name = format!("k{t}-{i}");
                assert_eq!(
                    engine.get(&key(name.as_bytes()), u64::MAX).unwrap(),
                    Some(b"v".to_vec())
                );
            }
        }
    }
    let engine = RegolithEngine::open(dir.path(), EngineOptions::default()).unwrap();
    for t in 0..8u32 {
        for i in 0..200u32 {
            let name = format!("k{t}-{i}");
            assert_eq!(
                engine.get(&key(name.as_bytes()), u64::MAX).unwrap(),
                Some(b"v".to_vec()),
                "{name} was not replayed"
            );
        }
    }
}
