//! A key merged N times in one optimistic transaction is validated with
//! one conflict probe, not N.
//!
//! Each probe that lands on a flushed key walks past every merge operand
//! already stored for it (`sstable.rs` continues past `VALUE_TYPE_MERGE`
//! entries), all while `commit_optimistic` holds the pipeline mutex. A
//! probe per merge op instead of per distinct key turns commit cost into
//! merges-in-the-transaction times operands-already-stored, under a lock
//! every other writer is waiting on. `Statistics::BloomFilterFullPositive`
//! is the public-API proxy for probe count here: each probe that reaches
//! the flushed SSTable and finds the key bumps it by exactly one.

use std::sync::Arc;

use regolith::{
    IsolationLevel, MergeOperator, OptimisticTransactionDb, Options, Statistics, Ticker,
};

/// Sums big-endian i64 deltas, so two `+1` operands make `+2` and the
/// operation is plainly not idempotent.
struct CounterMerge;

impl MergeOperator for CounterMerge {
    fn name(&self) -> &'static str {
        "counter"
    }

    fn full_merge(&self, _key: &[u8], base: Option<&[u8]>, operands: &[&[u8]]) -> Option<Vec<u8>> {
        let mut total: i64 = match base {
            Some(bytes) if bytes.len() == 8 => i64::from_be_bytes(bytes.try_into().unwrap()),
            Some(_) => return None,
            None => 0,
        };
        for operand in operands {
            if operand.len() != 8 {
                return None;
            }
            total = total.wrapping_add(i64::from_be_bytes((*operand).try_into().unwrap()));
        }
        Some(total.to_be_bytes().to_vec())
    }
}

#[test]
fn a_key_merged_many_times_is_probed_once() {
    const MERGES: i64 = 100;

    let dir = tempfile::tempdir().unwrap();
    let stats = Arc::new(Statistics::new());
    let options = Options {
        merge_operator: Some(Arc::new(CounterMerge)),
        statistics: Some(stats.clone()),
        ..Options::default()
    };
    let db = OptimisticTransactionDb::open(dir.path(), options).unwrap();

    // Flush the base value so every probe below has to reach the SSTable
    // and consult its bloom filter, rather than being served from the
    // active memtable where no bloom check happens.
    db.db().put(b"counter", &0i64.to_be_bytes()).unwrap();
    db.db().flush().unwrap();
    stats.reset();

    let tx = db.begin_transaction_with(IsolationLevel::SnapshotIsolation);
    for _ in 0..MERGES {
        tx.merge(b"counter", &1i64.to_be_bytes()).unwrap();
    }
    tx.commit().unwrap();

    assert_eq!(
        stats.get_ticker(Ticker::BloomFilterFullPositive),
        1,
        "a key merged {MERGES} times must be probed once, not once per merge op"
    );
    assert_eq!(
        db.db().get(b"counter").unwrap().as_deref(),
        Some(MERGES.to_be_bytes().as_slice())
    );
}
