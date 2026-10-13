//! A TTL database with a merge operator reads the same before and after a
//! flush, a compaction and a reopen, whatever was written when, and reads
//! what its rule says: each write expires by its own time.
//!
//! The steps are puts, merges and deletes on a few keys, the clock moved on
//! at random, flushes, one compaction pass at a time, full compactions and
//! reopens. Level sizes are tiny and a single level-0 table is due for
//! compaction, so a pass often rewrites a value while a newer merge of its
//! key sits in a table or a memtable the pass does not read.

// Native-only. wasm-pack builds every test target for wasm32, and the browser
// suite lives in tests/wasm_opfs*.rs.
#![cfg(not(target_arch = "wasm32"))]

use std::collections::BTreeMap;
use std::sync::Arc;

use proptest::prelude::*;
use regolith::{DbWithTtl, MemEnv, MergeOperator, Options, WriteBatch};

/// Seconds a write lives.
const TTL: u64 = 10;

/// The keys the steps write.
const KEYS: u8 = 3;

/// Concatenates, base first, then the operands oldest first.
struct Concat;

impl MergeOperator for Concat {
    fn full_merge(&self, _key: &[u8], base: Option<&[u8]>, operands: &[&[u8]]) -> Option<Vec<u8>> {
        let mut out = base.map(<[u8]>::to_vec).unwrap_or_default();
        for operand in operands {
            out.extend_from_slice(operand);
        }
        Some(out)
    }

    fn name(&self) -> &'static str {
        "concat"
    }
}

#[derive(Clone, Debug)]
enum Op {
    Put(u8, u8),
    Merge(u8, u8),
    Delete(u8),
    /// Move the wall clock on by this many seconds.
    Advance(u8),
    Flush,
    /// One compaction pass, which may leave newer tables out.
    CompactStep,
    /// A compaction of the whole database.
    CompactAll,
    Reopen,
}

fn op() -> impl Strategy<Value = Op> {
    prop_oneof![
        3 => (0..KEYS, any::<u8>()).prop_map(|(k, v)| Op::Put(k, v)),
        4 => (0..KEYS, any::<u8>()).prop_map(|(k, v)| Op::Merge(k, v)),
        1 => (0..KEYS).prop_map(Op::Delete),
        3 => (0u8..=12).prop_map(Op::Advance),
        2 => Just(Op::Flush),
        2 => Just(Op::CompactStep),
        1 => Just(Op::CompactAll),
        1 => Just(Op::Reopen),
    ]
}

fn key(k: u8) -> Vec<u8> {
    vec![b'k', k]
}

fn open(env: &Arc<MemEnv>) -> DbWithTtl {
    let options = Options::memory()
        .env(env.clone())
        .merge_operator(Some(Arc::new(Concat)))
        // Compaction runs only when a step asks for it.
        .inline_compaction(false)
        .l0_compaction_trigger(1)
        .level_base_bytes(1);
    DbWithTtl::open("ttl-props", options, TTL).unwrap()
}

/// What every key reads, by a point read, and what a scan of the whole
/// database returns.
type Reads = (Vec<Option<Vec<u8>>>, Vec<(Vec<u8>, Vec<u8>)>);

fn reads(db: &DbWithTtl) -> Reads {
    let points = (0..KEYS).map(|k| db.get(&key(k)).unwrap()).collect();
    (points, db.scan(None, None).unwrap())
}

/// One key's writes: the put the merges apply to and the operands merged
/// since, each with the second it was written at.
type Writes = (Option<(Vec<u8>, u64)>, Vec<(Vec<u8>, u64)>);

/// The rule, written out: per key, the base a put left and the operands
/// merged since, each with the second it was written at. A read folds the
/// writes that have not expired.
#[derive(Default)]
struct Model {
    keys: BTreeMap<u8, Writes>,
}

impl Model {
    fn read(&self, k: u8, now: u64) -> Option<Vec<u8>> {
        let (base, operands) = self.keys.get(&k)?;
        let live = |at: u64| at + TTL >= now;
        let base = base.as_ref().filter(|(_, at)| live(*at));
        let operands: Vec<&Vec<u8>> = operands
            .iter()
            .filter(|(_, at)| live(*at))
            .map(|(operand, _)| operand)
            .collect();
        if base.is_none() && operands.is_empty() {
            return None;
        }
        let mut out = base.map(|(value, _)| value.clone()).unwrap_or_default();
        for operand in operands {
            out.extend_from_slice(operand);
        }
        Some(out)
    }

    fn reads(&self, now: u64) -> Reads {
        let points: Vec<Option<Vec<u8>>> = (0..KEYS).map(|k| self.read(k, now)).collect();
        let scan = (0..KEYS)
            .filter_map(|k| points[usize::from(k)].clone().map(|v| (key(k), v)))
            .collect();
        (points, scan)
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// A flush, a compaction pass, a full compaction or a reopen never
    /// changes what a read returns.
    #[test]
    fn no_flush_compaction_or_reopen_changes_a_read(steps in prop::collection::vec(op(), 1..24)) {
        let env = Arc::new(MemEnv::new());
        let mut db = open(&env);
        for step in &steps {
            let before = reads(&db);
            match step {
                Op::Put(k, v) => db.put(&key(*k), &[b'p', *v]).unwrap(),
                Op::Merge(k, v) => {
                    let mut batch = WriteBatch::new();
                    batch.merge(&key(*k), &[b'm', *v]);
                    db.write(batch).unwrap();
                }
                Op::Delete(k) => db.delete(&key(*k)).unwrap(),
                Op::Advance(secs) => env.advance_micros(u64::from(*secs) * 1_000_000),
                Op::Flush => db.inner().flush().unwrap(),
                Op::CompactStep => {
                    db.inner().compact_step().unwrap();
                }
                Op::CompactAll => db.compact_range(None, None).wait().unwrap(),
                Op::Reopen => {
                    db.close().unwrap();
                    drop(db);
                    db = open(&env);
                }
            }
            if matches!(step, Op::Flush | Op::CompactStep | Op::CompactAll | Op::Reopen) {
                prop_assert_eq!(&reads(&db), &before, "{:?} changed a read", step);
            }
        }
    }

    /// What a read returns is what the rule says: each write expires by its
    /// own time, and a read folds the writes that have not expired.
    #[test]
    fn a_read_folds_the_writes_that_have_not_expired(steps in prop::collection::vec(op(), 1..24)) {
        let env = Arc::new(MemEnv::new());
        let mut db = open(&env);
        let mut model = Model::default();
        let mut now = 0u64;
        for step in &steps {
            match step {
                Op::Put(k, v) => {
                    db.put(&key(*k), &[b'p', *v]).unwrap();
                    model.keys.insert(*k, (Some((vec![b'p', *v], now)), Vec::new()));
                }
                Op::Merge(k, v) => {
                    let mut batch = WriteBatch::new();
                    batch.merge(&key(*k), &[b'm', *v]);
                    db.write(batch).unwrap();
                    model.keys.entry(*k).or_default().1.push((vec![b'm', *v], now));
                }
                Op::Delete(k) => {
                    db.delete(&key(*k)).unwrap();
                    model.keys.remove(k);
                }
                Op::Advance(secs) => {
                    env.advance_micros(u64::from(*secs) * 1_000_000);
                    now += u64::from(*secs);
                }
                Op::Flush => db.inner().flush().unwrap(),
                Op::CompactStep => {
                    db.inner().compact_step().unwrap();
                }
                Op::CompactAll => db.compact_range(None, None).wait().unwrap(),
                Op::Reopen => {
                    db.close().unwrap();
                    drop(db);
                    db = open(&env);
                }
            }
            prop_assert_eq!(&reads(&db), &model.reads(now), "after {:?}", step);
        }
    }
}
