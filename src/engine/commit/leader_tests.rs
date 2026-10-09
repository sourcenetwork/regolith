//! A bounded commit leader (E21): one leadership turn commits one group, of
//! at most `MAX_GROUP_MEMBERS` members and `MAX_GROUP_BYTES` staged bytes,
//! and hands the pipeline to the ticket at the head of the ring.

use tempfile::TempDir;

use super::super::EngineOptions;
use super::*;
use crate::column_family::{DEFAULT_CF_ID, prefix_key};

fn open() -> (TempDir, Arc<RegolithEngine>) {
    let dir = TempDir::new().unwrap();
    let engine = RegolithEngine::open(dir.path(), EngineOptions::default()).unwrap();
    (dir, engine)
}

fn put(name: String, value_len: usize) -> WriteRequest {
    WriteRequest::Put {
        key: prefix_key(DEFAULT_CF_ID, name.as_bytes()),
        value: vec![7u8; value_len],
        durability: DurabilityMode::Eventual,
        disable_wal: false,
    }
}

/// Queue `count` puts of `value_len` bytes in the ring, as parked writers
/// would, and return their slots in ring order.
fn queue(engine: &RegolithEngine, count: usize, value_len: usize) -> Vec<Arc<WriteSlot>> {
    (0..count)
        .map(|i| {
            let slot = Arc::new(WriteSlot::new());
            slot.arm(put(format!("queued{i:05}"), value_len))
                .expect("a fresh slot arms");
            engine
                .commit_ring
                .push(Arc::clone(&slot))
                .map_err(|_| "ring full")
                .unwrap();
            slot
        })
        .collect()
}

fn done(slots: &[Arc<WriteSlot>]) -> usize {
    slots.iter().filter(|slot| slot.is_done()).count()
}

/// The ticket the last leader handed the pipeline to.
fn held_is(engine: &RegolithEngine, slot: &Arc<WriteSlot>) -> bool {
    matches!(
        &engine.pipeline.lock().held,
        Some(GroupTicket { slot: Some(held), .. }) if Arc::ptr_eq(held, slot)
    )
}

/// One turn commits at most `MAX_GROUP_MEMBERS` members, the leader's own
/// write included, however many wait behind it; the next waiting ticket
/// heads the next group, and ring order is commit order.
#[test]
fn a_leader_commits_one_group_of_at_most_the_member_cap() {
    let (_dir, engine) = open();
    let extra = 20;
    let slots = queue(&engine, MAX_GROUP_MEMBERS + extra, 8);

    let own = engine
        .submit(put("own".to_string(), 8))
        .expect("the leader's own write commits");
    assert_eq!(
        done(&slots),
        MAX_GROUP_MEMBERS - 1,
        "one turn took the leader's write and {} queued ones",
        MAX_GROUP_MEMBERS - 1
    );
    assert!(
        held_is(&engine, &slots[MAX_GROUP_MEMBERS - 1]),
        "the turn ended by handing the pipeline to the next ticket in the ring"
    );

    assert!(
        engine.try_drain(),
        "the pipeline is free for the next leader"
    );
    assert_eq!(done(&slots), slots.len(), "the next turn took the rest");

    let mut last = own;
    for (i, slot) in slots.iter().enumerate() {
        let seq = slot.finish().expect("every queued write commits");
        assert!(seq > last, "ticket {i} committed out of ring order");
        last = seq;
    }
    assert!(engine.pipeline.lock().held.is_none());
    assert!(engine.commit_ring.is_empty());
}

/// Bytes bound a turn as members do: a queue of large writes is committed a
/// group of at most `MAX_GROUP_BYTES` (plus the one ticket that crosses it)
/// per turn.
#[test]
fn a_leader_commits_one_group_of_at_most_the_byte_cap() {
    let (_dir, engine) = open();
    let value_len = MAX_GROUP_BYTES / 8;
    let slots = queue(&engine, 32, value_len);

    let mut turns = 0;
    let mut before = 0;
    while done(&slots) < slots.len() {
        assert!(engine.try_drain());
        turns += 1;
        let now = done(&slots);
        let staged = (now - before) * value_len;
        assert!(
            staged <= MAX_GROUP_BYTES + value_len,
            "turn {turns} staged {staged} bytes in one group"
        );
        assert!(now > before, "turn {turns} committed nothing");
        before = now;
    }
    assert!(
        turns >= 4,
        "32 writes of an eighth of the cap took {turns} turns"
    );
}

/// Writers that queue behind a leader all finish: each turn hands the
/// pipeline on and wakes the writer it handed it to, so no writer waits on
/// one that never leads.
#[test]
fn every_writer_finishes_when_each_turn_hands_the_pipeline_on() {
    let (_dir, engine) = open();
    const WRITERS: usize = 32;
    const WRITES: usize = 200;
    std::thread::scope(|scope| {
        for w in 0..WRITERS {
            let engine = &engine;
            scope.spawn(move || {
                for i in 0..WRITES {
                    engine
                        .submit(put(format!("w{w:02}-{i:04}"), 64))
                        .expect("a write commits");
                }
            });
        }
    });
    for w in 0..WRITERS {
        let key = prefix_key(
            DEFAULT_CF_ID,
            format!("w{w:02}-{:04}", WRITES - 1).as_bytes(),
        );
        assert_eq!(engine.get(&key, u64::MAX).unwrap(), Some(vec![7u8; 64]));
    }
}
