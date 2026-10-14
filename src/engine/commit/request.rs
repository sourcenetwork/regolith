//! What a writer hands to the commit pipeline, and how a decided commit
//! turns into WAL bytes and memtable entries.

use std::io;

use super::super::wal::{
    check_record_len, encode_ops_record, encode_put_record, ops_record_len, put_record_len,
};
use super::super::{DurabilityMode, MemTable, apply_batch_op_to_memtable, batch_op_wal_bytes};
use super::txn::TxnRequest;
use crate::WriteBatchOp;
use crate::column_family::CF_PREFIX_LEN;
use crate::statistics::{Histogram, Statistics, Ticker};

/// The unit of work one writer hands to the commit pipeline.
///
/// Every byte a request refers to is owned by the request, never borrowed
/// from the submitting frame. That is what makes G3 hold: any thread can
/// finish a commit whose submitter has already unwound.
pub(crate) enum WriteRequest {
    /// A single put, the shape [`crate::Db::put`] produces.
    Put {
        /// Column-family-prefixed key.
        key: Vec<u8>,
        /// Value bytes.
        value: Vec<u8>,
        /// WAL fsync policy this writer asked for.
        durability: DurabilityMode,
        /// Skip the WAL entirely for this writer's operations.
        disable_wal: bool,
    },
    /// An ordered batch applied atomically.
    Batch {
        /// Operations in the order the caller recorded them.
        ops: Vec<WriteBatchOp>,
        /// WAL fsync policy this writer asked for.
        durability: DurabilityMode,
        /// Skip the WAL entirely for this writer's operations.
        disable_wal: bool,
    },
    /// An optimistic transaction's commit. It is validated when its slot is
    /// decided, and lands its own operations, or, when it carries appends,
    /// the batch deciding it numbered them into. Boxed: the request is moved
    /// several times on its way into the ring, and a plain put should not
    /// carry a transaction's size each time.
    Txn(Box<TxnRequest>),
}

impl WriteRequest {
    /// The operations the request carries, as the writer handed them over.
    pub(super) fn ops(&self) -> Ops<'_> {
        match self {
            WriteRequest::Put { key, value, .. } => Ops::Put { key, value },
            WriteRequest::Batch { ops, .. } => Ops::Batch(ops),
            WriteRequest::Txn(txn) => Ops::Batch(&txn.ops),
        }
    }

    pub(super) fn skips_wal(&self) -> bool {
        match self {
            WriteRequest::Put { disable_wal, .. } | WriteRequest::Batch { disable_wal, .. } => {
                *disable_wal
            }
            WriteRequest::Txn(_) => false,
        }
    }

    /// Bytes of operations this request's record carries: exactly one
    /// record's payload, or none when it skips the log. Every producer
    /// refuses a request whose record is over the limit.
    pub(super) fn staged_len(&self) -> usize {
        if self.skips_wal() {
            return 0;
        }
        self.ops().payload_len()
    }

    /// Refuse this request when its record is longer than `limit` bytes.
    /// A request that skips the log has no record and always passes.
    pub(super) fn check_record_len(&self, limit: usize) -> io::Result<()> {
        check_record_len(self.staged_len(), limit)
    }
}

/// A commit's operations, wherever they are held: in the request, or in the
/// decision when deciding produced them (a transaction whose appends were
/// numbered, a counter reservation).
pub(super) enum Ops<'a> {
    /// Nothing to land.
    None,
    Put {
        key: &'a [u8],
        value: &'a [u8],
    },
    Batch(&'a [WriteBatchOp]),
}

impl Ops<'_> {
    /// How many sequence numbers the operations consume: one each.
    pub(super) fn count(&self) -> u64 {
        match self {
            Ops::None => 0,
            Ops::Put { .. } => 1,
            Ops::Batch(ops) => ops.len() as u64,
        }
    }

    /// Bytes of the record's payload: what [`Ops::encode`] appends.
    pub(super) fn payload_len(&self) -> usize {
        match self {
            Ops::None => 0,
            Ops::Put { key, value } => put_record_len(key, value),
            Ops::Batch(ops) => ops_record_len(ops),
        }
    }

    /// Most memtable bytes applying the operations can add.
    ///
    /// The pipeline counts every commit against the active memtable's
    /// `write_buffer_size` with this, so it has to be an upper bound:
    /// over-stating a cost runs the rotation check one commit early, while
    /// under-stating one would let the memtable pass its budget unnoticed.
    ///
    /// A `DeleteRange` op costs range-tombstone heap rather than an arena
    /// node, and is charged the same way [`MemTable::delete_range`]
    /// charges it.
    pub(super) fn memtable_cost(&self) -> usize {
        match self {
            Ops::None => 0,
            Ops::Put { key, value } => MemTable::max_entry_size(key.len(), value.len()),
            Ops::Batch(ops) => ops
                .iter()
                .map(batch_op_memtable_cost)
                .fold(0usize, usize::saturating_add),
        }
    }

    /// Payload bytes reported to [`crate::statistics::Ticker::WalBytesWritten`].
    /// Counts the key, value and sequence bytes of each operation and no
    /// framing, as the ticker always has, so it stays comparable across log
    /// formats.
    pub(super) fn reported_bytes(&self) -> u64 {
        match self {
            Ops::None => 0,
            Ops::Put { key, value } => (key.len() + value.len() + 8) as u64,
            Ops::Batch(ops) => ops.iter().map(batch_op_wal_bytes).sum(),
        }
    }

    /// Count the operations in `stats` as one write that landed: what the
    /// write tickers and [`Histogram::BytesPerWrite`] report. Bytes are the
    /// user's, as [`Ticker::BytesWritten`] documents them: the key and the
    /// value of each put and the key of each delete, a key counted without
    /// the column family in front of it. Operations that write nothing are
    /// no write.
    pub(super) fn count_written(&self, stats: &Statistics) {
        let user = |key: &[u8]| key.len().saturating_sub(CF_PREFIX_LEN) as u64;
        let (mut puts, mut deletes, mut range_deletes, mut merges, mut bytes) = (0, 0, 0, 0, 0u64);
        match self {
            Ops::None => return,
            Ops::Put { key, value } => {
                puts = 1;
                bytes = user(key) + value.len() as u64;
            }
            Ops::Batch(ops) => {
                if ops.is_empty() {
                    return;
                }
                for op in *ops {
                    match op {
                        WriteBatchOp::Put { key, value } => {
                            puts += 1;
                            bytes += user(key) + value.len() as u64;
                        }
                        WriteBatchOp::Delete { key } => {
                            deletes += 1;
                            bytes += user(key);
                        }
                        WriteBatchOp::DeleteRange { .. } => range_deletes += 1,
                        WriteBatchOp::Merge { .. } => merges += 1,
                    }
                }
            }
        }
        for (ticker, count) in [
            (Ticker::KeysWritten, puts),
            (Ticker::KeysDeleted, deletes),
            (Ticker::RangeDeletesWritten, range_deletes),
            (Ticker::MergesWritten, merges),
            (Ticker::BytesWritten, bytes),
        ] {
            if count > 0 {
                stats.add(ticker, count);
            }
        }
        stats.record(Histogram::BytesPerWrite, bytes);
    }

    /// Append the operations to `out` as a record's payload, the first of
    /// them at `base_seq`.
    pub(super) fn encode(&self, out: &mut Vec<u8>, base_seq: u64) {
        match self {
            Ops::None => {}
            Ops::Put { key, value } => encode_put_record(out, key, value, base_seq),
            Ops::Batch(ops) => encode_ops_record(out, ops, base_seq),
        }
    }

    /// Apply the operations to `memtable`, the first of them at `base_seq`.
    /// Idempotent: a second application, by this thread or another, adds
    /// nothing (`engine::skiplist`, S2).
    pub(super) fn apply(&self, memtable: &MemTable, base_seq: u64) {
        // One hint per commit: a commit's point ops arrive in key order
        // (`grouped_batch_ops`), so each insert after the first starts where
        // the previous one landed.
        let mut hint = memtable.insert_hint();
        match self {
            Ops::None => {}
            Ops::Put { key, value } => memtable.put_hinted(&mut hint, key, value, base_seq),
            Ops::Batch(ops) => {
                for (op, seq) in ops.iter().zip(base_seq..) {
                    apply_batch_op_to_memtable(memtable, &mut hint, op, seq);
                }
            }
        }
    }
}

/// Upper bound on the memtable bytes one batch operation can add.
pub(super) fn batch_op_memtable_cost(op: &WriteBatchOp) -> usize {
    match op {
        WriteBatchOp::Put { key, value } => MemTable::max_entry_size(key.len(), value.len()),
        WriteBatchOp::Delete { key } => MemTable::max_entry_size(key.len(), 0),
        WriteBatchOp::Merge { key, operand } => MemTable::max_entry_size(key.len(), operand.len()),
        WriteBatchOp::DeleteRange { start, end } => {
            start.len() + end.len() + size_of::<crate::engine::range_tombstone::RangeTombstone>()
        }
    }
}

/// Shape only, never payload bytes: a request's key and value are user
/// data and have no business in a panic message or a log line.
impl std::fmt::Debug for WriteRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WriteRequest::Put {
                key,
                value,
                durability,
                disable_wal,
            } => f
                .debug_struct("WriteRequest::Put")
                .field("key_len", &key.len())
                .field("value_len", &value.len())
                .field("durability", durability)
                .field("disable_wal", disable_wal)
                .finish(),
            WriteRequest::Batch {
                ops,
                durability,
                disable_wal,
            } => f
                .debug_struct("WriteRequest::Batch")
                .field("ops", &ops.len())
                .field("durability", durability)
                .field("disable_wal", disable_wal)
                .finish(),
            WriteRequest::Txn(txn) => f
                .debug_struct("WriteRequest::Txn")
                .field("ops", &txn.ops.len())
                .field("appends", &txn.appends.len())
                .field("durability", &txn.durability)
                .finish(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::memtable::MemTableConfig;
    use super::super::super::wal::RecordLen;
    use super::*;
    use proptest::prelude::*;

    fn put(key: &[u8], value: &[u8]) -> WriteRequest {
        WriteRequest::Put {
            key: key.to_vec(),
            value: value.to_vec(),
            durability: DurabilityMode::Eventual,
            disable_wal: false,
        }
    }

    fn batch(ops: Vec<WriteBatchOp>) -> WriteRequest {
        WriteRequest::Batch {
            ops,
            durability: DurabilityMode::Eventual,
            disable_wal: false,
        }
    }

    #[test]
    fn the_count_matches_the_sequence_numbers_a_request_consumes() {
        assert_eq!(Ops::None.count(), 0);
        assert_eq!(put(b"k", b"v").ops().count(), 1);
        assert_eq!(
            batch(vec![
                WriteBatchOp::Put {
                    key: b"a".to_vec(),
                    value: b"1".to_vec()
                },
                WriteBatchOp::Delete { key: b"b".to_vec() },
            ])
            .ops()
            .count(),
            2
        );
    }

    #[test]
    fn staged_len_matches_the_bytes_actually_encoded() {
        let request = put(b"key", b"value");
        let mut out = Vec::new();
        request.ops().encode(&mut out, 7);
        assert_eq!(out.len(), request.staged_len());

        let batch = WriteRequest::Batch {
            ops: vec![
                WriteBatchOp::Put {
                    key: b"a".to_vec(),
                    value: b"1".to_vec(),
                },
                WriteBatchOp::Merge {
                    key: b"b".to_vec(),
                    operand: b"2".to_vec(),
                },
            ],
            durability: DurabilityMode::Immediate,
            disable_wal: false,
        };
        let mut out = Vec::new();
        batch.ops().encode(&mut out, 3);
        assert_eq!(out.len(), batch.staged_len());
    }

    #[test]
    fn a_wal_disabled_request_stages_nothing() {
        let request = WriteRequest::Put {
            key: b"k".to_vec(),
            value: b"v".to_vec(),
            durability: DurabilityMode::Immediate,
            disable_wal: true,
        };
        assert_eq!(request.staged_len(), 0);
        assert!(request.skips_wal());
    }

    /// Applying a commit's operations twice, as two threads helping one
    /// slot do, leaves the memtable as one application does.
    #[test]
    fn applying_the_same_operations_twice_adds_nothing() {
        let config = MemTableConfig::default();
        let once = MemTable::new(&config).unwrap();
        let twice = MemTable::new(&config).unwrap();
        let request = batch(vec![
            WriteBatchOp::Put {
                key: b"a".to_vec(),
                value: b"1".to_vec(),
            },
            WriteBatchOp::Merge {
                key: b"a".to_vec(),
                operand: b"+".to_vec(),
            },
            WriteBatchOp::Delete { key: b"b".to_vec() },
            WriteBatchOp::DeleteRange {
                start: b"c".to_vec(),
                end: b"d".to_vec(),
            },
        ]);
        request.ops().apply(&once, 5);
        request.ops().apply(&twice, 5);
        request.ops().apply(&twice, 5);
        assert_eq!(once.iter_internal(), twice.iter_internal());
        assert_eq!(
            once.clone_range_tombstones().len(),
            twice.clone_range_tombstones().len()
        );
        assert_eq!(once.approximate_size(), twice.approximate_size());
        assert_eq!(once.iter_internal().len(), 3);
    }

    /// One `WriteBatchOp`, covering every variant with short byte payloads.
    fn batch_op_strategy() -> impl Strategy<Value = WriteBatchOp> {
        let bytes = || proptest::collection::vec(any::<u8>(), 0..64);
        prop_oneof![
            (bytes(), bytes()).prop_map(|(key, value)| WriteBatchOp::Put { key, value }),
            bytes().prop_map(|key| WriteBatchOp::Delete { key }),
            (bytes(), bytes()).prop_map(|(start, end)| WriteBatchOp::DeleteRange { start, end }),
            (bytes(), bytes()).prop_map(|(key, operand)| WriteBatchOp::Merge { key, operand }),
        ]
    }

    /// A random request: a lone put or a batch of 0..24 ops.
    fn request_strategy() -> impl Strategy<Value = WriteRequest> {
        prop_oneof![
            (
                proptest::collection::vec(any::<u8>(), 0..64),
                proptest::collection::vec(any::<u8>(), 0..64)
            )
                .prop_map(|(key, value)| put(&key, &value)),
            proptest::collection::vec(batch_op_strategy(), 0..24).prop_map(batch),
        ]
    }

    proptest! {
        #[test]
        fn any_request_encodes_exactly_its_staged_len(request in request_strategy()) {
            // Covers `ops_record_len`'s three arms: empty (stages
            // nothing), one op (single-record framing), several ops
            // (batch framing), plus the put shape.
            let staged_len = request.staged_len();
            let mut out = Vec::new();
            out.reserve_exact(staged_len);
            request.ops().encode(&mut out, 1);
            prop_assert_eq!(out.len(), staged_len);
            prop_assert_eq!(out.capacity(), staged_len);
            if let WriteRequest::Batch { ops, .. } = &request {
                let mut len = RecordLen::default();
                ops.iter().for_each(|op| len.op(op));
                prop_assert_eq!(len.framed(), staged_len);
            }
        }
    }

    #[test]
    fn a_request_is_refused_past_the_limit_unless_it_skips_the_wal() {
        let request = put(b"key", b"value");
        let limit = request.staged_len();
        assert!(request.check_record_len(limit).is_ok());
        let err = request.check_record_len(limit - 1).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidInput);

        let request = batch(vec![
            WriteBatchOp::Put {
                key: b"a".to_vec(),
                value: b"1".to_vec(),
            },
            WriteBatchOp::Delete { key: b"b".to_vec() },
        ]);
        let limit = request.staged_len();
        assert!(request.check_record_len(limit).is_ok());
        let err = request.check_record_len(limit - 1).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidInput);

        let disabled = WriteRequest::Put {
            key: b"key".to_vec(),
            value: b"value".to_vec(),
            durability: DurabilityMode::Eventual,
            disable_wal: true,
        };
        assert!(disabled.check_record_len(0).is_ok());
    }
}
