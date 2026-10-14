//! Property: at DefraLevel the committed transactions are the same as those
//! transactions run one at a time in commit order (the invariant of
//! `all_classes_serial` in `proofs/lean/Regolith/Validation.lean`).
//!
//! Random schedules interleave transactions that decide on a whole value, on
//! one part of a value, on a validated range, and on nothing, with blind
//! writes, flushes and compactions. A transaction decides what to write from
//! what it read at its snapshot. After the run each committed transaction is
//! replayed against the state the earlier ones left, deciding again from that
//! state: it must decide the same writes (the decision at its snapshot has the
//! effect of the decision at its commit point), and the database must end in
//! the state the replay reaches.
//!
//! A write-free transaction is placed at its snapshot, not at its commit, as the
//! proof does: it reads one point in time, and writes nothing that could move.
//!
//! A mutant that stops validating a rule (a part read that ignores operands, a
//! value read that compares nothing) makes this fail, which is how the rules
//! were checked to be load-bearing.

// Native-only: these use the filesystem.
#![cfg(not(target_arch = "wasm32"))]

mod common;

use std::sync::Arc;

use common::parted::{PARTS, Parted, add, parts_of, value};
use proptest::prelude::*;
use regolith::{
    Db, IsolationLevel, OptimisticTransactionDb, Options, ScanCheck, ScanDirection, Transaction,
    TransactionError, TxnOptions,
};

const KEYS: usize = 3;
/// The key a range decision writes its total to; outside the scanned range.
const TOTAL: usize = KEYS;
const SLOTS: usize = 3;

type State = [Option<[u64; PARTS]>; KEYS + 1];

fn name(key: usize) -> Vec<u8> {
    if key == TOTAL {
        b"t0".to_vec()
    } else {
        format!("k{key}").into_bytes()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Op {
    Put(usize, [u64; PARTS]),
    Delete(usize),
    Add(usize, u32, u64),
}

/// What a transaction reads, and decides from.
#[derive(Clone, Debug)]
enum Prog {
    /// Read a value, write it back with the first part one higher.
    ReadModifyWrite(usize),
    /// Read a value and write it back unchanged, if it is there.
    Rewrite(usize),
    /// Read one part of `from`, add what it read plus one to a part of `to`.
    ProjectedAdd {
        from: usize,
        part: u32,
        to: usize,
        to_part: u32,
    },
    /// Scan every key with a validated range, add the sum of one part, plus
    /// one, to the total.
    RangeTotal(u32),
    /// Read some keys and write nothing.
    ReadOnly(Vec<usize>),
    /// Write without reading.
    Blind(Op),
}

/// The writes `prog` decides on from `seen`, the values it read.
fn decide(prog: &Prog, seen: &State) -> Vec<Op> {
    match prog {
        Prog::ReadModifyWrite(key) => {
            let mut v = seen[*key].unwrap_or([0; PARTS]);
            v[0] = v[0].wrapping_add(1);
            vec![Op::Put(*key, v)]
        }
        Prog::Rewrite(key) => seen[*key].map(|v| Op::Put(*key, v)).into_iter().collect(),
        Prog::ProjectedAdd {
            from,
            part,
            to,
            to_part,
        } => {
            // Only the named part of `from` and whether it is there.
            let read = seen[*from].map_or(0, |v| v[*part as usize]);
            vec![Op::Add(*to, *to_part, read.wrapping_add(1))]
        }
        Prog::RangeTotal(part) => {
            let total: u64 = (0..KEYS)
                .map(|key| seen[key].map_or(0, |v| v[*part as usize]))
                .fold(0, u64::wrapping_add);
            vec![Op::Add(TOTAL, 0, total.wrapping_add(1))]
        }
        Prog::ReadOnly(_) => Vec::new(),
        Prog::Blind(op) => vec![op.clone()],
    }
}

fn decode(bytes: Option<impl AsRef<[u8]>>) -> Option<[u64; PARTS]> {
    bytes.map(|bytes| parts_of(bytes.as_ref()).expect("a value of three parts"))
}

/// Run the reads of `prog` in `tx`, and return what they saw.
fn observe(prog: &Prog, tx: &Transaction) -> State {
    let mut seen: State = [None; KEYS + 1];
    match prog {
        Prog::ReadModifyWrite(key) | Prog::Rewrite(key) => {
            seen[*key] = decode(tx.get(&name(*key)).unwrap());
        }
        Prog::ProjectedAdd { from, part, .. } => {
            seen[*from] = decode(tx.get_parts(&name(*from), &[*part]).unwrap());
        }
        Prog::RangeTotal(_) => {
            let mut cursor = tx.cursor(
                Some(b"k0"),
                Some(b"k9"),
                ScanDirection::Forward,
                ScanCheck::Range,
            );
            loop {
                let page = cursor.next_page(tx, 64).unwrap();
                for (key, bytes) in page.entries {
                    let index = usize::from(key[1] - b'0');
                    seen[index] = decode(Some(bytes));
                }
                if page.done {
                    break;
                }
            }
        }
        Prog::ReadOnly(keys) => {
            for key in keys {
                seen[*key] = decode(tx.get(&name(*key)).unwrap());
            }
        }
        Prog::Blind(_) => {}
    }
    seen
}

fn buffer(tx: &Transaction, op: &Op) {
    match op {
        Op::Put(key, parts) => tx.put(&name(*key), &value(*parts)).unwrap(),
        Op::Delete(key) => tx.delete(&name(*key)).unwrap(),
        Op::Add(key, part, delta) => tx.merge(&name(*key), &add(*part, *delta)).unwrap(),
    }
}

/// How the engine applies a write to the state.
fn apply(state: &mut State, op: &Op) {
    match op {
        Op::Put(key, parts) => state[*key] = Some(*parts),
        Op::Delete(key) => state[*key] = None,
        Op::Add(key, part, delta) => {
            let mut parts = state[*key].unwrap_or([0; PARTS]);
            parts[*part as usize] = parts[*part as usize].wrapping_add(*delta);
            state[*key] = Some(parts);
        }
    }
}

#[derive(Clone, Debug)]
enum Action {
    Begin(usize, Prog),
    Commit(usize),
    Flush,
    Compact,
}

fn key() -> impl Strategy<Value = usize> {
    0..KEYS
}

fn prog() -> impl Strategy<Value = Prog> {
    let part = 0..PARTS as u32;
    prop_oneof![
        3 => key().prop_map(Prog::ReadModifyWrite),
        2 => key().prop_map(Prog::Rewrite),
        4 => (key(), part.clone(), key(), part.clone()).prop_map(|(from, part, to, to_part)| {
            Prog::ProjectedAdd { from, part, to, to_part }
        }),
        2 => part.clone().prop_map(Prog::RangeTotal),
        1 => proptest::collection::vec(key(), 1..3).prop_map(Prog::ReadOnly),
        3 => (key(), part.clone(), 0u64..3).prop_map(|(k, p, d)| Prog::Blind(Op::Add(k, p, d))),
        1 => (key(), proptest::array::uniform3(0u64..3))
            .prop_map(|(k, parts)| Prog::Blind(Op::Put(k, parts))),
        1 => key().prop_map(|k| Prog::Blind(Op::Delete(k))),
    ]
}

fn action() -> impl Strategy<Value = Action> {
    prop_oneof![
        6 => (0..SLOTS, prog()).prop_map(|(slot, prog)| Action::Begin(slot, prog)),
        6 => (0..SLOTS).prop_map(Action::Commit),
        1 => Just(Action::Flush),
        1 => Just(Action::Compact),
    ]
}

fn read_state(db: &Db) -> State {
    let mut state: State = [None; KEYS + 1];
    for (key, slot) in state.iter_mut().enumerate() {
        *slot = decode(db.get(&name(key)).unwrap());
    }
    state
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 200, ..ProptestConfig::default() })]

    #[test]
    fn committed_transactions_equal_the_same_transactions_run_in_commit_order(
        seeded in proptest::array::uniform4(proptest::option::of(proptest::array::uniform3(0u64..3))),
        actions in proptest::collection::vec(action(), 1..30),
    ) {
        let dir = tempfile::tempdir().unwrap();
        let db = OptimisticTransactionDb::open(
            dir.path(),
            Options::default().merge_operator(Some(Arc::new(Parted))),
        )
        .unwrap();
        for (key, parts) in seeded.iter().enumerate() {
            if let Some(parts) = parts {
                db.db().put(&name(key), &value(*parts)).unwrap();
            }
        }
        let initial = read_state(db.db());

        // Prog, its writes, its transaction, and the writers committed when it began.
        type Slot = Option<(Prog, Vec<Op>, Transaction, usize)>;
        let mut open: Vec<Slot> = (0..SLOTS).map(|_| None).collect();
        let mut writers: Vec<(Prog, Vec<Op>)> = Vec::new();
        let mut write_free: Vec<(Prog, usize)> = Vec::new();
        let mut finish = |slot: &mut Slot, writers: &mut Vec<(Prog, Vec<Op>)>| {
            let Some((prog, ops, tx, snapshot)) = slot.take() else { return Ok(()) };
            let free = ops.is_empty();
            match tx.commit() {
                Ok(_) if free => write_free.push((prog, snapshot)),
                Ok(_) => writers.push((prog, ops)),
                Err(TransactionError::Conflict(_)) => {
                    prop_assert!(!free, "a write-free transaction never conflicts");
                }
                Err(other) => prop_assert!(false, "unexpected {other:?}"),
            }
            Ok(())
        };

        for action in &actions {
            match action {
                Action::Begin(slot, prog) => {
                    if open[*slot].is_some() {
                        continue;
                    }
                    let tx = db.begin(&TxnOptions::new().isolation(IsolationLevel::DefraLevel));
                    let seen = observe(prog, &tx);
                    let ops = decide(prog, &seen);
                    ops.iter().for_each(|op| buffer(&tx, op));
                    open[*slot] = Some((prog.clone(), ops, tx, writers.len()));
                }
                Action::Commit(slot) => finish(&mut open[*slot], &mut writers)?,
                Action::Flush => db.db().flush().unwrap(),
                Action::Compact => db.db().compact_range(None, None).unwrap(),
            }
        }
        for slot in &mut open {
            finish(slot, &mut writers)?;
        }

        // What a transaction reads of `state`, as its program reads it.
        let seen_in = |prog: &Prog, state: &State| -> State {
            let mut seen: State = [None; KEYS + 1];
            match prog {
                Prog::ReadModifyWrite(k) | Prog::Rewrite(k) => seen[*k] = state[*k],
                Prog::ProjectedAdd { from, .. } => seen[*from] = state[*from],
                Prog::RangeTotal(_) => seen[..KEYS].copy_from_slice(&state[..KEYS]),
                Prog::ReadOnly(keys) => keys.iter().for_each(|k| seen[*k] = state[*k]),
                Prog::Blind(_) => {}
            }
            seen
        };

        // The replay: each writer decides again from the state the ones before
        // it left, and a write-free transaction from the state its snapshot held.
        let mut state = initial;
        let mut states = vec![state];
        for (prog, ops) in &writers {
            let again = decide(prog, &seen_in(prog, &state));
            prop_assert_eq!(&again, ops, "{:?} decided differently at its commit point", prog);
            again.iter().for_each(|op| apply(&mut state, op));
            states.push(state);
        }
        for (prog, snapshot) in &write_free {
            let again = decide(prog, &seen_in(prog, &states[*snapshot]));
            prop_assert!(again.is_empty(), "{:?} wrote something", prog);
        }
        prop_assert_eq!(read_state(db.db()), state, "the database is not the serial state");
    }
}
