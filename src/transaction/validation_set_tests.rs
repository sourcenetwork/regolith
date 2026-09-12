//! Equivalence check: the `ValidationSet` this branch builds names exactly
//! the same (key, observed sequence, read-or-not) triples the old
//! `BTreeMap`-based `validation_set` did.

use super::*;
use proptest::prelude::*;
use std::collections::BTreeMap;
use tempfile::TempDir;

/// The dedupe `commit_inner` ran before this branch (a `HashSet` over
/// cloned keys) followed by the old `validation_set` body (a `BTreeMap`
/// keyed by the flattened `(seq, read)` pair). Kept verbatim as the
/// oracle the proptest below checks the new code against; nothing here
/// is meant to be idiomatic, only faithful to what shipped before.
fn oracle(
    tx: &Transaction<'_>,
    tracked: Vec<(Vec<u8>, Arc<KeyState>)>,
    writes: &BTreeMap<Vec<u8>, Option<Vec<u8>>>,
    merges: &[(Vec<u8>, Vec<u8>)],
) -> BTreeMap<Vec<u8>, (u64, bool)> {
    let mut seen = std::collections::HashSet::new();
    let tracked: Vec<(Vec<u8>, Arc<KeyState>)> = tracked
        .into_iter()
        .filter(|(key, _)| seen.insert(key.clone()))
        .collect();

    let optimistic = matches!(tx.mode, TxMode::Optimistic);
    let serializable = tx.isolation == IsolationLevel::Serializable;
    let read_committed = tx.isolation == IsolationLevel::ReadCommitted;
    let mut checks: BTreeMap<Vec<u8>, (u64, bool)> = BTreeMap::new();
    for (key, state) in tracked {
        let written = writes.contains_key(&key) || merges.iter().any(|(merged, _)| *merged == key);
        let validate = if serializable {
            true
        } else if read_committed {
            written
        } else {
            state.for_update.load(Ordering::Acquire) || written
        };
        if validate {
            checks.insert(key, (state.first_read_seq, true));
        }
    }
    if optimistic {
        for key in writes.keys() {
            checks
                .entry(key.clone())
                .or_insert((tx.snapshot_seq, false));
        }
        for (key, _) in merges {
            checks
                .entry(key.clone())
                .or_insert((tx.snapshot_seq, false));
        }
    }
    checks
}

/// Flatten a `ValidationSet` back into the old shape, so it can be
/// compared against [`oracle`] directly.
fn expand(
    checks: &ValidationSet,
    writes: &BTreeMap<Vec<u8>, Option<Vec<u8>>>,
    merges: &[(Vec<u8>, Vec<u8>)],
) -> BTreeMap<Vec<u8>, (u64, bool)> {
    let mut out: BTreeMap<Vec<u8>, (u64, bool)> = checks
        .reads
        .iter()
        .map(|read| (read.key.clone(), (read.observed_seq, true)))
        .collect();
    if let Some(observed_seq) = checks.writes_at {
        for key in writes.keys() {
            out.entry(key.clone()).or_insert((observed_seq, false));
        }
        for (key, _) in merges {
            out.entry(key.clone()).or_insert((observed_seq, false));
        }
    }
    out
}

/// Either transaction flavor behind one type, so the op loop below does
/// not have to be written out twice.
enum AnyDb {
    Optimistic(OptimisticTransactionDb),
    Pessimistic(TransactionDb),
}

impl AnyDb {
    fn begin(&self, isolation: IsolationLevel) -> Transaction<'_> {
        match self {
            AnyDb::Optimistic(db) => db.begin_transaction_with(isolation),
            AnyDb::Pessimistic(db) => db.begin_transaction_with(isolation),
        }
    }

    /// A write around the transaction API, exactly like a concurrent
    /// writer would make one. Used to advance the horizon so a
    /// pessimistic `get_for_update` anchors above the begin snapshot.
    fn put_external(&self, key: &[u8], value: &[u8]) -> Result<()> {
        match self {
            AnyDb::Optimistic(db) => db.db().put(key, value),
            AnyDb::Pessimistic(db) => db.db().put(key, value),
        }
    }
}

fn isolation_level(level: u8) -> IsolationLevel {
    match level % 3 {
        0 => IsolationLevel::ReadCommitted,
        1 => IsolationLevel::SnapshotIsolation,
        _ => IsolationLevel::Serializable,
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 256, ..ProptestConfig::default() })]

    /// For every mix of reads, writes and merges a transaction can buffer,
    /// the new `ValidationSet` names the same keys, at the same anchor,
    /// with the same read-or-not distinction, as the old flattened map did.
    #[test]
    fn new_validation_set_equals_the_old_one(
        flavor in 0..2u8,
        level in 0..3u8,
        ops in proptest::collection::vec((0u8..6, 0u8..6), 0..24),
    ) {
        let dir = TempDir::new().expect("tempdir");
        let db = if flavor == 0 {
            AnyDb::Optimistic(
                OptimisticTransactionDb::open(dir.path(), Options::default()).expect("open"),
            )
        } else {
            AnyDb::Pessimistic(
                TransactionDb::open(dir.path(), Options::default())
                    .expect("open")
                    .with_lock_timeout(Duration::from_secs(10)),
            )
        };

        let mut tx = db.begin(isolation_level(level));
        for (kind, key) in &ops {
            let key = [*key];
            match kind {
                0 => prop_assert!(tx.get(&key).is_ok()),
                1 => prop_assert!(tx.get_for_update(&key).is_ok()),
                2 => prop_assert!(tx.put(&key, b"v").is_ok()),
                3 => prop_assert!(tx.delete(&key).is_ok()),
                4 => prop_assert!(tx.merge(&key, b"op").is_ok()),
                _ => prop_assert!(db.put_external(&key, b"v").is_ok()),
            }
        }

        // Drained exactly as `commit_inner` drains them. This never
        // reaches the engine: no merge operator is configured, and
        // nothing here commits.
        let mut writes: BTreeMap<Vec<u8>, Option<Vec<u8>>> = BTreeMap::new();
        for (key, value) in tx.writes.drain() {
            writes.entry(key).or_insert(value);
        }
        let merges = drain(&tx.merges);
        let tracked = tx.tracked.drain();

        let want = oracle(&tx, tracked.clone(), &writes, &merges);
        let checks = tx.validation_set(tracked, &writes, &merges);
        prop_assert!(
            checks.reads.windows(2).all(|pair| pair[0].key < pair[1].key),
            "reads must be strictly ascending by key with no duplicates"
        );
        let got = expand(&checks, &writes, &merges);
        prop_assert_eq!(got, want);

        drop(tx);
    }
}

/// Duplicate cells for one key reach `validation_set` only when two
/// threads race `get_or_insert` on a shared transaction (`observe` in the
/// parent module): the proptest above drives one op sequence per
/// transaction, so `tracked` never holds two cells for the same key there
/// and the `sort_by` + `dedup_by` in `validation_set` goes unexercised.
/// These two cases build `tracked` directly with duplicates instead.
///
/// Neither case alone is enough. Case 1 mixes `for_update` values, so a
/// missing dedupe can still pass by coincidence: the `SnapshotIsolation`
/// filter drops the losing (`for_update = false`) cell on its own. Case 2
/// gives both cells the same `for_update`, so only the dedupe itself can
/// collapse them to one.
#[test]
fn duplicate_tracked_cells_are_deduped_keeping_the_newest() {
    let dir = TempDir::new().expect("tempdir");
    let db = OptimisticTransactionDb::open(dir.path(), Options::default()).expect("open");
    let tx = db.begin_transaction_with(IsolationLevel::SnapshotIsolation);
    let seq = tx.snapshot_seq;

    // Case 1: catches a dedupe that keeps the wrong (older) cell. Newest
    // first, as the drain yields them; the newest cell carries
    // `for_update`, and keeping the other one instead would drop this
    // `get_for_update` key from validation, a lost update.
    let tracked = vec![
        (b"k".to_vec(), Arc::new(KeyState::new(seq, true))),
        (b"k".to_vec(), Arc::new(KeyState::new(seq, false))),
    ];
    let checks = tx.validation_set(tracked, &BTreeMap::new(), &[]);
    assert_eq!(checks.reads.len(), 1, "a duplicate key validates once");
    assert_eq!(checks.reads[0].key.as_slice(), b"k");

    // Case 2: catches a missing dedupe outright. Both cells carry
    // `for_update`, so a missing dedupe validates the key twice.
    let tracked = vec![
        (b"k".to_vec(), Arc::new(KeyState::new(seq, true))),
        (b"k".to_vec(), Arc::new(KeyState::new(seq, true))),
    ];
    let checks = tx.validation_set(tracked, &BTreeMap::new(), &[]);
    assert_eq!(
        checks.reads.len(),
        1,
        "a key is validated once however many cells it has"
    );

    drop(tx);
}
