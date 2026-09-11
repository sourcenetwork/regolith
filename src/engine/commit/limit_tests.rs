//! Coverage for the record-length limit: the fold in the three
//! validation loops, the admission hold-back, and the last-resort guard
//! in `run_and_complete`.

use std::collections::BTreeMap;
use std::time::Instant;

use proptest::prelude::*;
use tempfile::TempDir;

use super::super::wal::{ops_record_len, put_record_len};
use super::super::{EngineOptions, ValidationSet};
use super::*;
use crate::WriteBatchOp;
use crate::options::DEFAULT_MAX_VALUE_SIZE;

// -- helpers, reusing the shapes `commit::tests` already uses ---------

fn open_engine(dir: &TempDir) -> Arc<RegolithEngine> {
    RegolithEngine::open(dir.path(), EngineOptions::default()).expect("engine open")
}

/// Default-column-family prefix, the shape every engine key carries.
fn key(name: &[u8]) -> Vec<u8> {
    let mut k = vec![0u8; 4];
    k.extend_from_slice(name);
    k
}

fn durable_put(name: &[u8], value: &[u8]) -> WriteRequest {
    WriteRequest::Put {
        key: key(name),
        value: value.to_vec(),
        durability: DurabilityMode::Immediate,
        disable_wal: false,
    }
}

/// Puts under `count` keys whose values are zeroed and sized so the write
/// frames to exactly `framed` bytes. Uses the fact that a record's length
/// is its length with empty values plus the sum of the value lengths.
fn puts_framing_to(framed: usize, count: usize) -> Vec<WriteBatchOp> {
    let mut ops: Vec<WriteBatchOp> = (0..count)
        .map(|i| WriteBatchOp::Put {
            key: key(format!("k{i:02}").as_bytes()),
            value: Vec::new(),
        })
        .collect();
    let base = ops_record_len(&ops);
    let mut remaining = framed - base;
    for op in &mut ops {
        let WriteBatchOp::Put { value, .. } = op else {
            unreachable!("puts_framing_to only builds Put ops")
        };
        let take = remaining.min(DEFAULT_MAX_VALUE_SIZE);
        *value = vec![0u8; take];
        remaining -= take;
    }
    assert_eq!(ops_record_len(&ops), framed);
    ops
}

/// 16 zeroed puts plus one delete, one merge and one range delete, framed
/// to exactly `framed` bytes: every arm `validate_ops_sizes` folds gets
/// exercised, not only the put one.
fn mixed_ops_framing_to(framed: usize) -> Vec<WriteBatchOp> {
    let mut ops: Vec<WriteBatchOp> = (0..16)
        .map(|i| WriteBatchOp::Put {
            key: key(format!("k{i:02}").as_bytes()),
            value: Vec::new(),
        })
        .collect();
    ops.push(WriteBatchOp::Delete { key: key(b"del") });
    ops.push(WriteBatchOp::Merge {
        key: key(b"m"),
        operand: b"op".to_vec(),
    });
    ops.push(WriteBatchOp::DeleteRange {
        start: key(b"ra"),
        end: key(b"rb"),
    });
    let base = ops_record_len(&ops);
    let mut remaining = framed - base;
    for op in &mut ops {
        if let WriteBatchOp::Put { value, .. } = op {
            let take = remaining.min(DEFAULT_MAX_VALUE_SIZE);
            *value = vec![0u8; take];
            remaining -= take;
        }
    }
    assert_eq!(ops_record_len(&ops), framed);
    ops
}

/// Buffers shaped like a transaction commit's: 17 zeroed `Some` values,
/// one `None`, one range delete, one merge, framed to exactly `framed`
/// bytes through `grouped_batch_ops`, the same mapping
/// `commit_optimistic` validates against.
#[allow(clippy::type_complexity)]
fn commit_buffers_framing_to(
    framed: usize,
) -> (
    BTreeMap<Vec<u8>, Option<Vec<u8>>>,
    Vec<(Vec<u8>, Vec<u8>)>,
    Vec<(Vec<u8>, Vec<u8>)>,
) {
    let mut point_ops: BTreeMap<Vec<u8>, Option<Vec<u8>>> = (0..17)
        .map(|i| (key(format!("k{i:02}").as_bytes()), Some(Vec::new())))
        .collect();
    point_ops.insert(key(b"del"), None);
    let range_deletes = vec![(key(b"ra"), key(b"rb"))];
    let merges = vec![(key(b"m"), b"op".to_vec())];

    // Values are still empty here, so cloning to measure the base length
    // costs nothing resident.
    let base = ops_record_len(&grouped_batch_ops(
        point_ops.clone(),
        range_deletes.clone(),
        merges.clone(),
    ));
    let mut remaining = framed - base;
    for v in point_ops.values_mut().flatten() {
        let take = remaining.min(DEFAULT_MAX_VALUE_SIZE);
        *v = vec![0u8; take];
        remaining -= take;
    }

    // From here the values are zeroed and can run to a gigabyte, so the
    // buffers are moved through `grouped_batch_ops` rather than cloned:
    // cloning a filled `Vec<u8>` copies its bytes and faults the pages
    // resident, which is exactly the cost these tests exist to avoid.
    let ops = grouped_batch_ops(point_ops, range_deletes, merges);
    assert_eq!(ops_record_len(&ops), framed);

    let mut point_ops = BTreeMap::new();
    let mut range_deletes = Vec::new();
    let mut merges = Vec::new();
    for op in ops {
        match op {
            WriteBatchOp::Put { key, value } => {
                point_ops.insert(key, Some(value));
            }
            WriteBatchOp::Delete { key } => {
                point_ops.insert(key, None);
            }
            WriteBatchOp::DeleteRange { start, end } => range_deletes.push((start, end)),
            WriteBatchOp::Merge { key, operand } => merges.push((key, operand)),
        }
    }
    (point_ops, range_deletes, merges)
}

/// Poll `f` until it is true, or fail with `msg` after `deadline`. Backs
/// off from 1 ms to 50 ms rather than spinning or sleeping a fixed
/// amount, so a fast run returns almost immediately and a stuck one
/// fails instead of hanging the suite.
fn wait_until(deadline: Duration, msg: &str, mut f: impl FnMut() -> bool) {
    let start = Instant::now();
    let mut backoff = Duration::from_millis(1);
    while !f() {
        assert!(start.elapsed() < deadline, "{msg}");
        thread::sleep(backoff);
        backoff = (backoff * 2).min(Duration::from_millis(50));
    }
}

/// Run `call` on its own thread while this thread holds the pipeline
/// mutex, and assert it refuses the write without ever needing that
/// mutex: it must finish inside the deadline even though the mutex is
/// unavailable, and every trace of the attempt (sequence, WAL offset,
/// the key itself) must be untouched.
fn assert_refused_while_pipeline_locked(
    engine: &Arc<RegolithEngine>,
    probe_key: &[u8],
    call: impl FnOnce(Arc<RegolithEngine>) -> io::Result<u64> + Send + 'static,
) {
    let before_seq = engine.latest_seq.load(Ordering::Acquire);
    let before_wal = engine
        .active_wal
        .lock()
        .as_ref()
        .map(|w| w.offset())
        .unwrap();

    let guard = engine.pipeline.lock();
    let spawned = Arc::clone(engine);
    let handle = thread::spawn(move || call(spawned));

    wait_until(
        Duration::from_secs(60),
        "the record-limit check must refuse a write before it needs the pipeline mutex",
        || handle.is_finished(),
    );
    drop(guard);

    let err = handle
        .join()
        .expect("the writer thread must not panic")
        .expect_err("an oversized write must be refused");
    assert_eq!(err.kind(), io::ErrorKind::InvalidInput);

    assert_eq!(engine.latest_seq.load(Ordering::Acquire), before_seq);
    assert_eq!(
        engine
            .active_wal
            .lock()
            .as_ref()
            .map(|w| w.offset())
            .unwrap(),
        before_wal
    );
    assert_eq!(engine.get(probe_key, u64::MAX).unwrap(), None);
}

// -- T3.1, T3.2: the validation loops fold the record length ----------

#[test]
fn validate_ops_sizes_refuses_one_byte_past_the_limit() {
    let dir = TempDir::new().unwrap();
    let engine = open_engine(&dir);

    let ops = puts_framing_to(MAX_RECORD_LEN as usize, 17);
    assert!(engine.validate_ops_sizes(&ops, false).is_ok());

    let ops = puts_framing_to(MAX_RECORD_LEN as usize + 1, 17);
    let err = engine
        .validate_ops_sizes(&ops, false)
        .expect_err("a record one byte past the limit must be refused");
    assert_eq!(err.kind(), io::ErrorKind::InvalidInput);
    assert_eq!(
        err.to_string(),
        format!(
            "write is too large: it would log {} bytes and one write can log at most {}; \
             split it into smaller writes",
            MAX_RECORD_LEN as usize + 1,
            MAX_RECORD_LEN
        )
    );
    assert!(engine.validate_ops_sizes(&ops, true).is_ok());

    // Every arm of the fold must contribute, not only the put one.
    let mixed = mixed_ops_framing_to(MAX_RECORD_LEN as usize);
    assert!(engine.validate_ops_sizes(&mixed, false).is_ok());
    let mixed = mixed_ops_framing_to(MAX_RECORD_LEN as usize + 1);
    assert!(engine.validate_ops_sizes(&mixed, false).is_err());
}

// -- T3.3: refused before the pipeline, at every producer -------------

#[test]
fn an_oversized_write_is_refused_before_it_reaches_the_pipeline() {
    {
        let dir = TempDir::new().unwrap();
        let engine = open_engine(&dir);
        let probe = key(b"k00");
        assert_refused_while_pipeline_locked(&engine, &probe, move |engine| {
            engine.apply_batch(
                puts_framing_to(MAX_RECORD_LEN as usize + 1, 17),
                DurabilityMode::Eventual,
                false,
            )
        });
    }

    {
        let dir = TempDir::new().unwrap();
        let engine = open_engine(&dir);
        let (point_ops, range_deletes, merges) =
            commit_buffers_framing_to(MAX_RECORD_LEN as usize + 1);
        let probe = key(b"k00");
        assert_refused_while_pipeline_locked(&engine, &probe, move |engine| {
            let checks = ValidationSet {
                reads: Vec::new(),
                writes_at: None,
            };
            engine
                .commit_optimistic(
                    &checks,
                    point_ops,
                    range_deletes,
                    merges,
                    DurabilityMode::Eventual,
                )
                .map(|_outcome| 0)
        });
    }

    {
        let dir = TempDir::new().unwrap();
        let engine = RegolithEngine::open(
            dir.path(),
            EngineOptions {
                max_value_size: u32::MAX as usize,
                ..EngineOptions::default()
            },
        )
        .expect("engine open");
        let probe = key(b"big");
        let base = put_record_len(&probe, &[]);
        let v = MAX_RECORD_LEN as usize + 1 - base;
        assert_eq!(
            put_record_len(&probe, &vec![0u8; v]),
            MAX_RECORD_LEN as usize + 1
        );
        let put_key = probe.clone();
        assert_refused_while_pipeline_locked(&engine, &probe, move |engine| {
            engine.apply_single_put(put_key, vec![0u8; v], DurabilityMode::Eventual, false)
        });
    }
}

// -- T3.4: a group over the limit is refused whole --------------------

#[test]
fn a_group_past_the_limit_is_refused_whole_before_it_takes_a_sequence() {
    let dir = TempDir::new().unwrap();
    let engine = open_engine(&dir);

    let before_seq = engine.latest_seq.load(Ordering::Acquire);
    let before_horizon = engine.snapshot_seq();
    let before_wal = engine
        .active_wal
        .lock()
        .as_ref()
        .map(|w| w.offset())
        .unwrap();

    // Two requests under the record limit on their own (600 MiB each),
    // but 1.2 GiB together: only the group-level guard can catch this.
    let names = [b"biga".to_vec(), b"bigb".to_vec()];
    let slots: Vec<Arc<WriteSlot>> = names
        .iter()
        .map(|name| {
            let slot = Arc::new(WriteSlot::new());
            slot.arm(WriteRequest::Put {
                key: key(name),
                value: vec![0u8; 600 << 20],
                durability: DurabilityMode::Eventual,
                disable_wal: false,
            })
            .expect("fresh slot arms");
            slot
        })
        .collect();

    let mut pipe = engine.pipeline.lock();
    pipe.group.clear();
    for slot in &slots {
        let request = slot.take_request();
        pipe.group.push(GroupTicket {
            slot: Some(Arc::clone(slot)),
            request,
        });
    }
    let result = engine.run_and_complete(&mut pipe, engine.view.load());
    let err = result.expect_err("a group over the record limit must be refused");
    assert_eq!(err.kind(), io::ErrorKind::InvalidInput);
    assert_eq!(pipe.stage.len(), 0);
    drop(pipe);

    for slot in &slots {
        assert!(slot.is_done());
        let err = slot
            .finish()
            .expect_err("an over-limit group must fail every member");
        assert_eq!(err.kind(), io::ErrorKind::InvalidInput);
    }

    assert_eq!(engine.latest_seq.load(Ordering::Acquire), before_seq);
    assert_eq!(engine.snapshot_seq(), before_horizon);
    assert_eq!(
        engine
            .active_wal
            .lock()
            .as_ref()
            .map(|w| w.offset())
            .unwrap(),
        before_wal
    );
    for name in &names {
        assert_eq!(engine.get(&key(name), u64::MAX).unwrap(), None);
    }
}

// -- T3.5-T3.8: admission's hold-back ----------------------------------

#[test]
fn admission_holds_back_a_ticket_that_would_take_the_group_past_the_limit() {
    let dir = TempDir::new().unwrap();
    let engine = open_engine(&dir);

    let a = durable_put(b"a", b"short").staged_len();
    let b = durable_put(b"b", b"a-bit-longer-value").staged_len();
    let push_ab = |engine: &RegolithEngine| {
        let slot_a = Arc::new(WriteSlot::new());
        slot_a.arm(durable_put(b"a", b"short")).unwrap();
        engine
            .commit_ring
            .push(slot_a)
            .map_err(|_| "ring full")
            .unwrap();
        let slot_b = Arc::new(WriteSlot::new());
        slot_b
            .arm(durable_put(b"b", b"a-bit-longer-value"))
            .unwrap();
        engine
            .commit_ring
            .push(slot_b)
            .map_err(|_| "ring full")
            .unwrap();
    };

    let mut pipe = engine.pipeline.lock();
    let view = engine.view.load();

    pipe.group.clear();
    pipe.held = None;
    push_ab(&engine);
    engine.admit_from_ring(&mut pipe, &view, a + b - 1);
    assert_eq!(pipe.group.len(), 1);
    assert_eq!(pipe.group[0].request.staged_len(), a);
    assert!(pipe.held.is_some());
    assert_eq!(pipe.held.as_ref().unwrap().request.staged_len(), b);

    pipe.group.clear();
    pipe.held = None;
    push_ab(&engine);
    engine.admit_from_ring(&mut pipe, &view, a + b);
    assert_eq!(pipe.group.len(), 2);
    assert!(pipe.held.is_none());
}

#[test]
fn a_seeded_group_holds_back_what_does_not_fit() {
    let dir = TempDir::new().unwrap();
    let engine = open_engine(&dir);

    let s = durable_put(b"seed", b"value").staged_len();
    let a = durable_put(b"a", b"a-value").staged_len();

    let seed = |pipe: &mut Pipeline| {
        pipe.group.clear();
        pipe.held = None;
        pipe.group.push(GroupTicket {
            slot: None,
            request: durable_put(b"seed", b"value"),
        });
    };
    let push_a = |engine: &RegolithEngine| {
        let slot = Arc::new(WriteSlot::new());
        slot.arm(durable_put(b"a", b"a-value")).unwrap();
        engine
            .commit_ring
            .push(slot)
            .map_err(|_| "ring full")
            .unwrap();
    };

    let mut pipe = engine.pipeline.lock();
    let view = engine.view.load();

    seed(&mut pipe);
    push_a(&engine);
    engine.admit_from_ring(&mut pipe, &view, s + a - 1);
    assert_eq!(pipe.group.len(), 1);
    assert!(pipe.held.is_some());

    seed(&mut pipe);
    push_a(&engine);
    engine.admit_from_ring(&mut pipe, &view, s + a);
    assert_eq!(pipe.group.len(), 2);
    assert!(pipe.held.is_none());
}

#[test]
fn a_held_ticket_leads_the_next_group_ahead_of_the_ring() {
    let dir = TempDir::new().unwrap();
    let engine = open_engine(&dir);

    let h_slot = Arc::new(WriteSlot::new());
    h_slot.arm(durable_put(b"held", b"h")).unwrap();
    let a_slot = Arc::new(WriteSlot::new());
    a_slot.arm(durable_put(b"a", b"a")).unwrap();
    engine
        .commit_ring
        .push(Arc::clone(&a_slot))
        .map_err(|_| "ring full")
        .unwrap();

    let mut pipe = engine.pipeline.lock();
    pipe.group.clear();
    pipe.held = Some(GroupTicket {
        slot: Some(Arc::clone(&h_slot)),
        request: h_slot.take_request(),
    });
    let view = engine.view.load();
    engine.admit_from_ring(&mut pipe, &view, usize::MAX);

    assert_eq!(pipe.group.len(), 2);
    assert!(Arc::ptr_eq(pipe.group[0].slot.as_ref().unwrap(), &h_slot));
    assert!(Arc::ptr_eq(pipe.group[1].slot.as_ref().unwrap(), &a_slot));
    assert!(pipe.held.is_none());
}

#[test]
fn the_first_ticket_is_admitted_whatever_the_limit() {
    let dir = TempDir::new().unwrap();
    let engine = open_engine(&dir);

    let a_slot = Arc::new(WriteSlot::new());
    a_slot.arm(durable_put(b"a", b"value")).unwrap();
    engine
        .commit_ring
        .push(Arc::clone(&a_slot))
        .map_err(|_| "ring full")
        .unwrap();

    // Nothing else holds the pipeline mutex here: the deadline is
    // guarding against the hold-back condition looping inside a single
    // call, not against contention.
    let spawned = Arc::clone(&engine);
    let handle = thread::spawn(move || {
        let mut pipe = spawned.pipeline.lock();
        pipe.group.clear();
        pipe.held = None;
        let view = spawned.view.load();
        spawned.admit_from_ring(&mut pipe, &view, 1);
        (pipe.group.len(), pipe.held.is_some())
    });

    wait_until(
        Duration::from_secs(60),
        "admission must terminate even when the first ticket alone exceeds the limit",
        || handle.is_finished(),
    );
    let (group_len, held) = handle.join().expect("admission must not panic");
    assert_eq!(
        group_len, 1,
        "the first ticket is admitted whatever it costs"
    );
    assert!(!held);
}

// -- T3.9: a held ticket survives to the next drain --------------------

#[test]
fn a_held_ticket_is_committed_by_the_next_drain() {
    let dir = TempDir::new().unwrap();
    let engine = open_engine(&dir);

    let h_slot = Arc::new(WriteSlot::new());
    h_slot.arm(durable_put(b"held", b"v")).unwrap();
    {
        let mut pipe = engine.pipeline.lock();
        pipe.group.clear();
        pipe.held = Some(GroupTicket {
            slot: Some(Arc::clone(&h_slot)),
            request: h_slot.take_request(),
        });
    }

    assert!(
        engine.try_drain(),
        "a held ticket alone must still be drained"
    );
    assert!(h_slot.is_done());
    assert!(h_slot.finish().is_ok());
    assert_eq!(
        engine.get(&key(b"held"), u64::MAX).unwrap(),
        Some(b"v".to_vec())
    );
    assert!(engine.pipeline.lock().held.is_none());

    // A held ticket left by an interrupted leader is admitted into the
    // next leader's group, behind that leader's own seeded request.
    let h2_slot = Arc::new(WriteSlot::new());
    h2_slot.arm(durable_put(b"held2", b"v2")).unwrap();
    {
        let mut pipe = engine.pipeline.lock();
        pipe.held = Some(GroupTicket {
            slot: Some(Arc::clone(&h2_slot)),
            request: h2_slot.take_request(),
        });
    }
    let seq_own = engine
        .submit(durable_put(b"own", b"v"))
        .expect("the leader's own write commits");
    assert!(h2_slot.is_done());
    let seq_held = h2_slot.finish().expect("the held ticket commits too");
    assert!(
        seq_own < seq_held,
        "the leader's own seeded request runs before the held ticket it admits: \
         {seq_own} >= {seq_held}"
    );
    assert_eq!(
        engine.get(&key(b"own"), u64::MAX).unwrap(),
        Some(b"v".to_vec())
    );
    assert_eq!(
        engine.get(&key(b"held2"), u64::MAX).unwrap(),
        Some(b"v2".to_vec())
    );
}

// -- T3.10: admission never stages a group past the limit -------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(48))]
    #[test]
    fn admission_never_stages_a_group_past_the_limit_and_keeps_ring_order(
        value_lens in proptest::collection::vec(0usize..200, 1..=15),
        limit in 32usize..600,
    ) {
        let dir = TempDir::new().unwrap();
        let engine = open_engine(&dir);

        let mut pushed = Vec::new();
        for (i, len) in value_lens.iter().enumerate() {
            let k = key(format!("k{i:02}").as_bytes());
            let slot = Arc::new(WriteSlot::new());
            slot.arm(WriteRequest::Put {
                key: k.clone(),
                value: vec![0u8; *len],
                durability: DurabilityMode::Eventual,
                disable_wal: false,
            })
            .expect("fresh slot arms");
            engine.commit_ring.push(slot).map_err(|_| "ring full").unwrap();
            pushed.push(k);
        }

        let mut pipe = engine.pipeline.lock();
        pipe.group.clear();
        pipe.held = None;
        let view = engine.view.load();

        let mut seen: Vec<Vec<u8>> = Vec::new();
        loop {
            engine.admit_from_ring(&mut pipe, &view, limit);
            if pipe.group.is_empty() {
                break;
            }
            let staged: usize = pipe.group.iter().map(|t| t.request.staged_len()).sum();
            prop_assert!(pipe.group.len() == 1 || staged <= limit);
            for ticket in pipe.group.drain(..) {
                if let WriteRequest::Put { key, .. } = &ticket.request {
                    seen.push(key.clone());
                }
            }
        }

        prop_assert!(engine.commit_ring.is_empty());
        prop_assert!(pipe.held.is_none());
        prop_assert_eq!(seen, pushed);
    }
}
