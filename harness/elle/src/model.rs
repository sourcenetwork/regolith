//! Workload generation and execution against regolith transactions.
//!
//! A transaction is planned before it runs and the plan is reused
//! across retries, so the append values in the `invoke` record always
//! match the ones in the completion record even when an optimistic
//! transaction has to be replayed.

use regolith::{
    Db, IsolationLevel, OptimisticTransactionDb, Options, Transaction, TransactionDb,
    TransactionError, TxResult,
};
use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::sync::Arc;
use std::sync::atomic::{AtomicI64, Ordering};

use crate::cli::{Isolation, Model};
use crate::history::{Mop, MopVal};
use crate::list::{self, ListAppend};

/// Deterministic splitmix64. A dependency-free RNG is enough here: the
/// workload only needs reproducible key and shape choices.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Self(seed)
    }

    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    pub fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n.max(1)
    }
}

/// Hands out the globally unique values Elle needs to reconstruct
/// version order. Each process gets a disjoint base so a child's values
/// can never collide with the parent's.
pub struct ValueSource(AtomicI64);

impl ValueSource {
    pub fn new(base: i64) -> Self {
        Self(AtomicI64::new(base))
    }

    pub fn next(&self) -> i64 {
        self.0.fetch_add(1, Ordering::Relaxed)
    }
}

/// Every variant is a point operation. The `repeatable-read` rows of
/// `just elle-matrix` rest on that: the level validates point reads and
/// not scans, so a range read added here would need rows of its own,
/// and Elle's list-append and rw-register models have no range operation
/// to record one with.
///
/// `ReadForUpdate` is a read through `get_for_update` that the transaction
/// does not write back, recorded as a plain read. It is the one read
/// `ReadCommitted` leaves unvalidated and `SnapshotIsolation` validates.
#[derive(Clone, Debug)]
pub enum PlannedMop {
    Append { key: i64, val: i64 },
    Read { key: i64 },
    ReadForUpdate { key: i64 },
    Write { key: i64, val: i64 },
}

/// A planned transaction: the micro-operations plus the values they
/// will write, fixed before the first attempt.
#[derive(Clone, Debug)]
pub struct TxnPlan {
    pub mops: Vec<PlannedMop>,
}

impl TxnPlan {
    /// Only `read-committed` plans carry [`PlannedMop::ReadForUpdate`]: it is
    /// there so that level and `snapshot-isolation` run different commit
    /// validation, and every other level's plans stay as they were.
    pub fn generate(
        model: Model,
        isolation: Isolation,
        keys: i64,
        rng: &mut Rng,
        values: &ValueSource,
    ) -> Self {
        let locking_reads = isolation == Isolation::ReadCommitted;
        let count = 1 + rng.below(3) as usize;
        let mut mops = Vec::with_capacity(count);
        for _ in 0..count {
            let key = rng.below(keys as u64) as i64;
            let write = rng.below(3) != 0;
            mops.push(match (model, write) {
                (Model::ListAppend, true) => PlannedMop::Append {
                    key,
                    val: values.next(),
                },
                (Model::RwRegister, true) => PlannedMop::Write {
                    key,
                    val: values.next(),
                },
                (_, false) if locking_reads && rng.below(2) == 0 => {
                    PlannedMop::ReadForUpdate { key }
                }
                (_, false) => PlannedMop::Read { key },
            });
        }
        Self { mops }
    }

    /// Read-only transaction over every key, used for the post-recovery
    /// read-back phases.
    pub fn read_all(keys: i64) -> Self {
        Self {
            mops: (0..keys).map(|key| PlannedMop::Read { key }).collect(),
        }
    }

    /// The `invoke` value: writes carry their value, reads carry null.
    pub fn invoke_value(&self) -> Vec<Mop> {
        self.mops
            .iter()
            .map(|mop| match mop {
                PlannedMop::Append { key, val } => Mop("append".into(), *key, MopVal::Int(*val)),
                PlannedMop::Write { key, val } => Mop("w".into(), *key, MopVal::Int(*val)),
                PlannedMop::Read { key } | PlannedMop::ReadForUpdate { key } => {
                    Mop("r".into(), *key, MopVal::Null)
                }
            })
            .collect()
    }

    /// Run every micro-operation inside one regolith transaction and return
    /// the completion value, with observed results filled into reads.
    ///
    /// Appends are read-modify-write against `get_for_update`, which is
    /// the API a caller reaches for precisely to make an increment safe.
    /// With `blind_appends`, an append to a key the transaction has not read
    /// goes in as a merge operand instead, the one write DefraLevel lets
    /// commute with another transaction's. A key that has taken an operand
    /// keeps taking them, because a put and an operand in one commit apply
    /// in the engine's order and not the plan's.
    pub fn execute(
        &self,
        model: Model,
        blind_appends: bool,
        tx: &mut Transaction<'_>,
    ) -> TxResult<Vec<Mop>> {
        let mut observed = Vec::with_capacity(self.mops.len());
        let mut read = HashSet::new();
        let mut merged: HashMap<i64, Vec<i64>> = HashMap::new();
        for mop in &self.mops {
            match mop {
                PlannedMop::Append { key, val } => {
                    if blind_appends && (merged.contains_key(key) || !read.contains(key)) {
                        tx.merge(&key_bytes(*key), &list::encode(&[*val]))?;
                        merged.entry(*key).or_default().push(*val);
                    } else {
                        read.insert(*key);
                        let current = tx.get_for_update(&key_bytes(*key))?;
                        let mut list = list::decode(current.as_deref()).unwrap_or_default();
                        list.push(*val);
                        tx.put(&key_bytes(*key), &list::encode(&list))?;
                    }
                    observed.push(Mop("append".into(), *key, MopVal::Int(*val)));
                }
                PlannedMop::Write { key, val } => {
                    tx.put(&key_bytes(*key), val.to_string().as_bytes())?;
                    observed.push(Mop("w".into(), *key, MopVal::Int(*val)));
                }
                PlannedMop::Read { key } => {
                    read.insert(*key);
                    let current = tx.get(&key_bytes(*key))?;
                    let own = merged.get(key).map_or(&[][..], Vec::as_slice);
                    observed.push(read_mop(model, *key, current.as_deref(), own));
                }
                PlannedMop::ReadForUpdate { key } => {
                    read.insert(*key);
                    let current = tx.get_for_update(&key_bytes(*key))?;
                    let own = merged.get(key).map_or(&[][..], Vec::as_slice);
                    observed.push(read_mop(model, *key, current.as_deref(), own));
                }
            }
        }
        Ok(observed)
    }
}

/// The completion record of a read that returned `current`. A read does not
/// return the operands the same transaction has buffered, so `own` (the
/// elements it merged into the key) is added the way the commit will apply
/// them.
fn read_mop(model: Model, key: i64, current: Option<&[u8]>, own: &[i64]) -> Mop {
    let value = match model {
        Model::ListAppend => {
            let mut list = list::decode(current);
            if !own.is_empty() {
                list.get_or_insert_default().extend_from_slice(own);
            }
            list.map_or(MopVal::Null, MopVal::List)
        }
        Model::RwRegister => decode_int(current).map_or(MopVal::Null, MopVal::Int),
    };
    Mop("r".into(), key, value)
}

/// The transaction flavor the requested isolation level maps onto.
pub enum TxDb {
    Pessimistic(TransactionDb),
    Optimistic(OptimisticTransactionDb),
    /// The optimistic flavour at `DefraLevel`, opened with the list-append
    /// merge operator so an append can be a merge operand.
    Defra(OptimisticTransactionDb),
}

impl TxDb {
    pub fn open(path: &Path, isolation: Isolation, opts: Options) -> regolith::Result<Self> {
        match isolation {
            Isolation::ReadCommitted => Ok(TxDb::Pessimistic(
                TransactionDb::open(path, opts)?.with_isolation(IsolationLevel::ReadCommitted),
            )),
            // The optimistic flavour at the regolith level of the same name.
            Isolation::Snapshot => Ok(TxDb::Optimistic(
                OptimisticTransactionDb::open(path, opts)?
                    .with_isolation(IsolationLevel::SnapshotIsolation),
            )),
            Isolation::RepeatableRead => Ok(TxDb::Optimistic(
                OptimisticTransactionDb::open(path, opts)?
                    .with_isolation(IsolationLevel::RepeatableRead),
            )),
            Isolation::Serializable => Ok(TxDb::Optimistic(
                OptimisticTransactionDb::open(path, opts)?
                    .with_isolation(IsolationLevel::Serializable),
            )),
            // No key classifier: these workloads are point operations, so
            // DefraLevel validates point reads exactly as RepeatableRead
            // does. What it adds here is the blind merge, which needs the
            // operator.
            Isolation::DefraLevel => Ok(TxDb::Defra(
                OptimisticTransactionDb::open(
                    path,
                    Options {
                        merge_operator: Some(Arc::new(ListAppend)),
                        ..opts
                    },
                )?
                .with_isolation(IsolationLevel::DefraLevel),
            )),
        }
    }

    pub fn begin(&self) -> Transaction<'_> {
        match self {
            TxDb::Pessimistic(db) => db.begin_transaction(),
            TxDb::Optimistic(db) | TxDb::Defra(db) => db.begin_transaction(),
        }
    }

    pub fn db(&self) -> &Db {
        match self {
            TxDb::Pessimistic(db) => db.db(),
            TxDb::Optimistic(db) | TxDb::Defra(db) => db.db(),
        }
    }

    /// Optimistic transactions surface write-write conflicts to the
    /// caller, so the client retries them; pessimistic ones resolve
    /// contention by blocking and never report a conflict.
    pub fn retries(&self) -> u32 {
        match self {
            TxDb::Pessimistic(_) => 1,
            TxDb::Optimistic(_) | TxDb::Defra(_) => 16,
        }
    }

    /// Whether an append the transaction has not read may be a merge
    /// operand: only at the level that lets blind merges commute.
    pub fn blind_appends(&self) -> bool {
        matches!(self, TxDb::Defra(_))
    }
}

/// How a transaction attempt ended, mapped to a history record type.
pub enum Outcome {
    Committed(Vec<Mop>),
    /// Definitely not committed: rolled back after a conflict or a
    /// lock timeout.
    Aborted,
    /// Indeterminate: the commit itself failed with an I/O error, so
    /// the write may or may not be durable.
    Unknown,
}

pub fn run_txn(db: &TxDb, model: Model, plan: &TxnPlan) -> Outcome {
    let mut last_retryable = false;
    for _ in 0..db.retries() {
        let mut tx = db.begin();
        match plan.execute(model, db.blind_appends(), &mut tx) {
            Ok(observed) => match tx.commit() {
                Ok(()) => return Outcome::Committed(observed),
                Err(TransactionError::Conflict { .. }) | Err(TransactionError::Busy(_)) => {
                    last_retryable = true;
                }
                Err(_) => return Outcome::Unknown,
            },
            Err(TransactionError::Conflict { .. }) | Err(TransactionError::Busy(_)) => {
                tx.rollback();
                last_retryable = true;
            }
            Err(_) => {
                tx.rollback();
                return Outcome::Unknown;
            }
        }
    }
    if last_retryable {
        Outcome::Aborted
    } else {
        Outcome::Unknown
    }
}

pub fn key_bytes(key: i64) -> Vec<u8> {
    format!("k{:08}", key).into_bytes()
}

fn decode_int(raw: Option<&[u8]>) -> Option<i64> {
    std::str::from_utf8(raw?).ok()?.parse::<i64>().ok()
}

#[cfg(test)]
mod tests;
