//! Workload generation and execution against regolith transactions.
//!
//! A transaction is planned before it runs and the plan is reused
//! across retries, so the append values in the `invoke` record always
//! match the ones in the completion record even when an optimistic
//! transaction has to be replayed.

use regolith::{
    Db, IsolationLevel, KeyClass, KeyClassifier, LogLayout, OptimisticTransactionDb, Options,
    ScanCheck, ScanDirection, Transaction, TransactionDb, TransactionError, TxResult, TxnOptions,
};
use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::sync::Arc;
use std::sync::atomic::{AtomicI64, Ordering};

use crate::cli::{Isolation, Model, Shape};
use crate::history::{Mop, MopVal};
use crate::list::{self, ListAppend};
use crate::parts::{self, AppendToParts};

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

/// Every variant but `ScanAll` is a point operation. The `repeatable-read`
/// rows of `just elle-matrix` that run the `point` shape rest on that: the
/// level validates point reads and not scans.
///
/// `ReadForUpdate` is a read through `get_for_update` that the transaction
/// does not write back, recorded as a plain read. It is the one read
/// `ReadCommitted` leaves unvalidated and `SnapshotIsolation` validates. In
/// the `parts` shape it locks the part's document and records the part.
///
/// `ScanAll` is one validated scan of the whole key prefix. Elle's models
/// have no range operation, so it is recorded as a read of every key of
/// the workload, the ones it did not return as reads of nothing: over a
/// known set of keys that is what the scan observed.
#[derive(Clone, Debug)]
pub enum PlannedMop {
    Append { key: i64, val: i64 },
    Read { key: i64 },
    ReadForUpdate { key: i64 },
    Write { key: i64, val: i64 },
    ScanAll,
}

/// A planned transaction: the micro-operations plus the values they
/// will write, fixed before the first attempt.
#[derive(Clone, Debug)]
pub struct TxnPlan {
    pub mops: Vec<PlannedMop>,
    /// How many keys the workload has: what a `ScanAll` records a read of.
    pub keys: i64,
    /// A value no other transaction has, for the keys a transaction of the
    /// `classified` shape writes beside its operations. `None` for a plan
    /// that writes none.
    pub nonce: Option<i64>,
}

impl TxnPlan {
    /// Only `read-committed` plans carry [`PlannedMop::ReadForUpdate`]: it is
    /// there so that level and `snapshot-isolation` run different commit
    /// validation, and every other level's plans stay as they were.
    pub fn generate(
        model: Model,
        isolation: Isolation,
        shape: Shape,
        keys: i64,
        rng: &mut Rng,
        values: &ValueSource,
    ) -> Self {
        let mops = match shape {
            Shape::Point | Shape::Classified | Shape::Parts => {
                Self::point_mops(model, isolation, keys, rng, values)
            }
            Shape::Appends => Self::log_mops(keys, rng, values),
            Shape::Scan => Self::scan_mops(model, keys, rng, values),
        };
        Self {
            mops,
            keys,
            nonce: (shape == Shape::Classified).then(|| values.next()),
        }
    }

    fn point_mops(
        model: Model,
        isolation: Isolation,
        keys: i64,
        rng: &mut Rng,
        values: &ValueSource,
    ) -> Vec<PlannedMop> {
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
        mops
    }

    /// A transaction on logs appends or reads, never both: a read of a log
    /// is not validated, so a transaction that read one and then appended
    /// would have decided nothing on the read, and Elle would still order
    /// it before every later append to that log.
    fn log_mops(keys: i64, rng: &mut Rng, values: &ValueSource) -> Vec<PlannedMop> {
        let appends = rng.below(3) != 0;
        let count = 1 + rng.below(3) as usize;
        (0..count)
            .map(|_| {
                let key = rng.below(keys as u64) as i64;
                if appends {
                    PlannedMop::Append {
                        key,
                        val: values.next(),
                    }
                } else {
                    PlannedMop::Read { key }
                }
            })
            .collect()
    }

    /// Most transactions scan every key and then write one or two of them,
    /// which is the shape write skew takes; some only scan, and some only
    /// write.
    fn scan_mops(model: Model, keys: i64, rng: &mut Rng, values: &ValueSource) -> Vec<PlannedMop> {
        let mut mops = Vec::new();
        let scans = rng.below(4) != 0;
        if scans {
            mops.push(PlannedMop::ScanAll);
        }
        let writes = if scans {
            rng.below(3)
        } else {
            1 + rng.below(2)
        };
        for _ in 0..writes {
            let key = rng.below(keys as u64) as i64;
            let val = values.next();
            mops.push(match model {
                Model::ListAppend => PlannedMop::Append { key, val },
                Model::RwRegister => PlannedMop::Write { key, val },
            });
        }
        mops
    }

    /// Read-only transaction over every key, used for the post-recovery
    /// read-back phases.
    pub fn read_all(keys: i64, shape: Shape) -> Self {
        let mops = match shape {
            Shape::Scan => vec![PlannedMop::ScanAll],
            _ => (0..keys).map(|key| PlannedMop::Read { key }).collect(),
        };
        Self {
            mops,
            keys,
            nonce: None,
        }
    }

    /// The `invoke` value: writes carry their value, reads carry null.
    pub fn invoke_value(&self) -> Vec<Mop> {
        let read = |key: i64| Mop("r".into(), key, MopVal::Null);
        self.mops
            .iter()
            .flat_map(|mop| match mop {
                PlannedMop::Append { key, val } => {
                    vec![Mop("append".into(), *key, MopVal::Int(*val))]
                }
                PlannedMop::Write { key, val } => vec![Mop("w".into(), *key, MopVal::Int(*val))],
                PlannedMop::Read { key } | PlannedMop::ReadForUpdate { key } => vec![read(*key)],
                PlannedMop::ScanAll => (0..self.keys).map(read).collect(),
            })
            .collect()
    }

    /// Run every micro-operation inside one regolith transaction and return
    /// the completion value, with observed results filled into reads.
    ///
    /// In the `point` and `classified` shapes appends are read-modify-write
    /// against `get_for_update`, which is the API a caller reaches for
    /// precisely to make an increment safe. With `blind_appends`, an append
    /// to a key the transaction has not read goes in as a merge operand
    /// instead, the one write DefraLevel lets commute with another
    /// transaction's. A key that has taken an operand keeps taking them.
    ///
    /// The other shapes are in README.md: `appends` runs each append through
    /// `Transaction::append` and reads a log in one snapshot, `parts` appends
    /// to and reads one part of a document, and `scan` reads through one
    /// validated scan and writes the keys it was returned.
    pub fn execute(
        &self,
        model: Model,
        shape: Shape,
        blind_appends: bool,
        tx: &mut Transaction,
    ) -> TxResult<Vec<Mop>> {
        if let Some(nonce) = self.nonce {
            classified_side_keys(tx, nonce)?;
        }
        let mut observed = Vec::with_capacity(self.mops.len());
        let mut read = HashSet::new();
        let mut merged = HashSet::new();
        // What the scan returned for each key, with the appends this
        // transaction made to it since.
        let mut scanned: Option<HashMap<i64, Vec<i64>>> = None;
        for mop in &self.mops {
            match mop {
                PlannedMop::Append { key, val } if shape == Shape::Appends => {
                    // Every other append names a once key no other append
                    // names, so the entry is appended either way and both
                    // paths of the ordered step run.
                    let once = (*val % 2 == 0).then(|| once_key(*val));
                    tx.append(&log_of(*key), val.to_string().as_bytes(), once.as_deref())?;
                    observed.push(Mop("append".into(), *key, MopVal::Int(*val)));
                }
                PlannedMop::Append { key, val } if shape == Shape::Parts => {
                    let (document, part) = part_key(*key);
                    tx.merge(&document, &parts::append(part, *val))?;
                    observed.push(Mop("append".into(), *key, MopVal::Int(*val)));
                }
                PlannedMop::Append { key, val } => {
                    if let Some(lists) = scanned.as_mut() {
                        // The scan read the list and covers the key: a write
                        // landing on it since refuses this commit.
                        let list = lists.entry(*key).or_default();
                        list.push(*val);
                        tx.put(&key_bytes(*key), &list::encode(list))?;
                    } else if blind_appends && (merged.contains(key) || !read.contains(key)) {
                        tx.merge(&key_bytes(*key), &list::encode(&[*val]))?;
                        merged.insert(*key);
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
                PlannedMop::Read { key } if shape == Shape::Appends => {
                    observed.push(Mop("r".into(), *key, read_log(tx, *key)?));
                }
                PlannedMop::Read { key } if shape == Shape::Parts => {
                    let (document, part) = part_key(*key);
                    let current = tx.get_parts(&document, &[part])?;
                    let value = parts::list_of(current.as_deref(), part);
                    observed.push(Mop(
                        "r".into(),
                        *key,
                        value.map_or(MopVal::Null, MopVal::List),
                    ));
                }
                PlannedMop::Read { key } => {
                    read.insert(*key);
                    let current = tx.get(&key_bytes(*key))?;
                    observed.push(read_mop(model, *key, current.as_deref()));
                }
                // A part lives in its document, as for a plain read: the
                // locking read takes the document's key and reads the part.
                PlannedMop::ReadForUpdate { key } if shape == Shape::Parts => {
                    let (document, part) = part_key(*key);
                    let current = tx.get_for_update(&document)?;
                    let value = parts::list_of(current.as_deref(), part);
                    observed.push(Mop(
                        "r".into(),
                        *key,
                        value.map_or(MopVal::Null, MopVal::List),
                    ));
                }
                PlannedMop::ReadForUpdate { key } => {
                    read.insert(*key);
                    let current = tx.get_for_update(&key_bytes(*key))?;
                    observed.push(read_mop(model, *key, current.as_deref()));
                }
                PlannedMop::ScanAll => {
                    let values = scan_all(tx)?;
                    for key in 0..self.keys {
                        let current = values.get(&key).map(Vec::as_slice);
                        observed.push(read_mop(model, key, current));
                    }
                    scanned = Some(
                        values
                            .iter()
                            .filter_map(|(key, raw)| Some((*key, list::decode(Some(raw))?)))
                            .collect(),
                    );
                }
            }
        }
        Ok(observed)
    }
}

/// The completion record of a read that returned `current`, which already
/// holds the elements the same transaction merged into the key.
fn read_mop(model: Model, key: i64, current: Option<&[u8]>) -> Mop {
    let value = match model {
        Model::ListAppend => list::decode(current).map_or(MopVal::Null, MopVal::List),
        Model::RwRegister => decode_int(current).map_or(MopVal::Null, MopVal::Int),
    };
    Mop("r".into(), key, value)
}

/// The keys a classifier of this harness names: `b/` content-addressed
/// blocks, `h/` a commutative prefix, and the logs with their once keys.
pub struct Classes;

impl KeyClassifier for Classes {
    fn classify(&self, key: &[u8]) -> KeyClass {
        if key.starts_with(b"b/") {
            KeyClass::ContentAddressed
        } else if key.starts_with(b"h/") {
            KeyClass::CommutativePrefix { len: 2 }
        } else if key.starts_with(b"log/") || key.starts_with(b"once/") {
            KeyClass::Log
        } else {
            KeyClass::Ordinary
        }
    }
}

/// A commit-ordered log: its head at `log/<name>/head` and its entries at
/// `log/<name>/e<20 decimal digits>`.
struct NamedLog {
    head: Vec<u8>,
    entries: String,
}

impl NamedLog {
    fn new(name: &str) -> Self {
        Self {
            head: format!("log/{name}/head").into_bytes(),
            entries: format!("log/{name}/e"),
        }
    }

    fn entry(&self, position: u64) -> Vec<u8> {
        format!("{}{position:020}", self.entries).into_bytes()
    }
}

impl LogLayout for NamedLog {
    fn head_key(&self) -> &[u8] {
        &self.head
    }

    fn entry_key(&self, position: u64, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.entry(position));
    }

    fn max_entry_key_len(&self) -> usize {
        self.entries.len() + 20
    }
}

/// The log that stands for list-append key `key` in the `appends` shape.
fn log_of(key: i64) -> Arc<dyn LogLayout> {
    Arc::new(NamedLog::new(&format!("{key:08}")))
}

/// The once key of the append of `val`.
fn once_key(val: i64) -> Vec<u8> {
    format!("once/{val}").into_bytes()
}

fn position(raw: Option<Vec<u8>>) -> u64 {
    raw.map_or(0, |bytes| {
        u64::from_be_bytes(bytes.as_slice().try_into().expect("an 8-byte position"))
    })
}

/// The log of `key` as `tx` reads it: its head, then every entry up to it.
///
/// A snapshot holds a dense prefix of a log, so an entry missing below the
/// head is not a state a reader can be handed. It is a broken log, and the
/// run stops on it instead of recording a history from it.
fn read_log(tx: &Transaction, key: i64) -> TxResult<MopVal> {
    let log = NamedLog::new(&format!("{key:08}"));
    let head = position(tx.get(log.head_key())?);
    let mut list = Vec::with_capacity(head as usize);
    for at in 1..=head {
        let entry = tx.get(&log.entry(at))?.unwrap_or_else(|| {
            panic!("the log of key {key} has no entry at position {at} below its head {head}")
        });
        list.push(decode_int(Some(&entry)).expect("an entry is a decimal value"));
    }
    Ok(if head == 0 {
        MopVal::Null
    } else {
        MopVal::List(list)
    })
}

/// The document and the part that stand for list-append key `key` in the
/// `parts` shape: neighbouring keys share a document.
fn part_key(key: i64) -> (Vec<u8>, u32) {
    (
        format!("d{:08}", key / parts::PARTS).into_bytes(),
        (key % parts::PARTS) as u32,
    )
}

/// Every key of the workload with its value, read by one validated scan of
/// the key prefix: a write that lands anywhere in the prefix before the
/// commit refuses it, a key that appears included.
fn scan_all(tx: &Transaction) -> TxResult<HashMap<i64, Vec<u8>>> {
    let mut cursor = tx.cursor(
        Some(b"k"),
        Some(b"l"),
        ScanDirection::Forward,
        ScanCheck::Range,
    );
    let mut values = HashMap::new();
    loop {
        let page = cursor.next_page(tx, 64 * 1024)?;
        for (key, value) in page.entries {
            let index = std::str::from_utf8(&key[1..])
                .ok()
                .and_then(|digits| digits.parse::<i64>().ok())
                .expect("a workload key is `k` and its number");
            values.insert(index, value.to_vec());
        }
        if page.done {
            return Ok(values);
        }
    }
}

/// The log every transaction of the `classified` shape appends to.
const JOURNAL: &str = "journal";

/// The bytes of the blocks: a block's key determines them.
const BLOCK: &[u8] = b"the bytes of a block";

/// What a transaction of the `classified` shape does beside its
/// operations, on keys of each class the classifier names:
///
/// - it reads whether one of two shared blocks is stored and stores it when
///   it is not, as a block store does;
/// - it scans a set of heads and adds a head of its own, and rewrites a
///   marker every transaction writes alike;
/// - it reads the head of a journal and appends an entry.
///
/// None of it may refuse the commit or be refused: the classes say these
/// writes commute. The head and the journal entry land in one commit, so
/// [`side_keys_agree`] can count them against each other afterwards.
fn classified_side_keys(tx: &Transaction, nonce: i64) -> TxResult<()> {
    let block: &[u8] = if nonce % 2 == 0 { b"b/even" } else { b"b/odd" };
    if tx.get(block)?.is_none() {
        tx.put(block, BLOCK)?;
    }
    for head in tx.scan_stream(Some(b"h/"), Some(b"h0")) {
        head?;
    }
    tx.put(format!("h/own/{nonce:020}").as_bytes(), b"head")?;
    tx.put(b"h/marker", b"head")?;
    let journal: Arc<dyn LogLayout> = Arc::new(NamedLog::new(JOURNAL));
    tx.get(journal.head_key())?;
    tx.append(&journal, nonce.to_string().as_bytes(), None)
}

/// Whether the side keys of the `classified` shape tell one story: the
/// journal has an entry at every position up to its head, and as many
/// entries as there are heads, since a transaction commits one of each or
/// neither. `Err` says what does not agree.
pub fn side_keys_agree(db: &Db) -> Result<(), String> {
    let err = |e: regolith::Error| e.to_string();
    let journal = NamedLog::new(JOURNAL);
    let head = position(db.get(journal.head_key()).map_err(err)?);
    let mut entries = HashSet::new();
    for at in 1..=head {
        let entry = db.get(&journal.entry(at)).map_err(err)?.ok_or_else(|| {
            format!("the journal has no entry at position {at} below its head {head}")
        })?;
        if !entries.insert(entry) {
            return Err(format!(
                "the journal holds the entry at position {at} twice"
            ));
        }
    }
    let heads = db
        .scan(Some(b"h/own/"), Some(b"h/own0"))
        .map_err(err)?
        .len() as u64;
    if heads != head {
        return Err(format!(
            "{heads} transactions left a head and {head} a journal entry: a commit applied one \
             without the other"
        ));
    }
    Ok(())
}

/// The transaction flavor the requested isolation level maps onto.
pub enum TxDb {
    Pessimistic(TransactionDb),
    Optimistic(OptimisticTransactionDb),
    /// The optimistic flavour at `DefraLevel`, opened with a merge operator
    /// so an append can be a merge operand, and with a classifier for every
    /// shape but `point`.
    Defra(OptimisticTransactionDb),
}

impl TxDb {
    pub fn open(
        path: &Path,
        isolation: Isolation,
        shape: Shape,
        opts: Options,
    ) -> regolith::Result<Self> {
        // A part is appended to by an operand at every level.
        let opts = match shape {
            Shape::Parts => opts.merge_operator(Some(Arc::new(AppendToParts))),
            _ => opts,
        };
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
            Isolation::DefraLevel => {
                let opts = match shape {
                    Shape::Parts => opts,
                    _ => opts.merge_operator(Some(Arc::new(ListAppend))),
                };
                let db = OptimisticTransactionDb::open(path, opts)?
                    .with_isolation(IsolationLevel::DefraLevel);
                // The `point` shape runs with no classifier: its workloads
                // are point operations, so DefraLevel validates point reads
                // exactly as RepeatableRead does, and what it adds is the
                // blind merge.
                Ok(TxDb::Defra(match shape {
                    Shape::Point => db,
                    _ => db.with_policy(Arc::new(Classes)),
                }))
            }
        }
    }

    pub fn begin(&self) -> Transaction {
        match self {
            TxDb::Pessimistic(db) => db.begin(&TxnOptions::new()),
            TxDb::Optimistic(db) | TxDb::Defra(db) => db.begin(&TxnOptions::new()),
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

pub fn run_txn(db: &TxDb, model: Model, shape: Shape, plan: &TxnPlan) -> Outcome {
    let mut last_retryable = false;
    for _ in 0..db.retries() {
        let mut tx = db.begin();
        match plan.execute(model, shape, db.blind_appends(), &mut tx) {
            Ok(observed) => match tx.commit() {
                Ok(_) => return Outcome::Committed(observed),
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
