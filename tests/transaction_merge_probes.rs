//! A key merged N times in one optimistic transaction is validated with
//! one conflict probe, not N.
//!
//! Each probe runs while `commit_optimistic` holds the pipeline mutex that
//! every other writer is waiting on, so a probe per merge op instead of per
//! distinct key multiplies commit cost by the merges in the transaction.
//! A probe stops at the key's newest entry, merge operands included: a
//! newer operand is a newer write, wherever it is stored. `Statistics::BloomFilterFullPositive`
//! is the public-API proxy for probe count here: each probe that reaches
//! the flushed SSTable and finds the key bumps it by exactly one.

use std::sync::Arc;

use regolith::{
    IsolationLevel, MergeOperator, OptimisticTransactionDb, Options, Statistics, Ticker,
    TransactionError,
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

/// Where the newer merge operand sits when the reader commits.
#[derive(Clone, Copy, Debug)]
enum OperandAt {
    Memtable,
    /// Flushed into its own L0 file, above the flushed base.
    SeparateTable,
    /// Compacted into the same table as the base it sits on.
    SameTable,
}

/// A point read is stale once a newer merge operand commits on its key,
/// wherever that operand is stored. The conflict check used to see only
/// the memtable copy: the SSTable probe walked past merge operands to
/// the base under them, so after a flush the reader's anchor looked
/// current and a stale read committed.
#[test]
fn a_newer_merge_operand_conflicts_a_point_read_wherever_it_is_stored() {
    for at in [
        OperandAt::Memtable,
        OperandAt::SeparateTable,
        OperandAt::SameTable,
    ] {
        let dir = tempfile::tempdir().unwrap();
        let options = Options {
            merge_operator: Some(Arc::new(CounterMerge)),
            ..Options::default()
        };
        let db = OptimisticTransactionDb::open(dir.path(), options).unwrap();
        db.db().put(b"counter", &0i64.to_be_bytes()).unwrap();
        db.db().flush().unwrap();

        let tx = db.begin_transaction_with(IsolationLevel::RepeatableRead);
        assert_eq!(
            tx.get(b"counter").unwrap().as_deref(),
            Some(0i64.to_be_bytes().as_slice())
        );

        db.db().merge(b"counter", &1i64.to_be_bytes()).unwrap();
        match at {
            OperandAt::Memtable => {}
            OperandAt::SeparateTable => db.db().flush().unwrap(),
            OperandAt::SameTable => {
                db.db().flush().unwrap();
                db.db().compact_range(None, None).unwrap();
            }
        }

        tx.put(b"elsewhere", b"x").unwrap();
        assert!(
            matches!(tx.commit(), Err(TransactionError::Conflict { .. })),
            "a read of `counter` overtaken by a merge operand stored in {at:?} must conflict"
        );
    }
}
