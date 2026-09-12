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

    /// A delete around the transaction API.
    fn delete_external(&self, key: &[u8]) -> Result<()> {
        match self {
            AnyDb::Optimistic(db) => db.db().delete(key),
            AnyDb::Pessimistic(db) => db.db().delete(key),
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

fn open_any(flavor: u8, dir: &TempDir) -> AnyDb {
    if flavor == 0 {
        AnyDb::Optimistic(
            OptimisticTransactionDb::open(dir.path(), Options::default()).expect("open"),
        )
    } else {
        AnyDb::Pessimistic(
            TransactionDb::open(dir.path(), Options::default())
                .expect("open")
                .with_lock_timeout(Duration::from_secs(10)),
        )
    }
}

/// The keys the stretches of one scan of `[start, end)` cover, worked out
/// independently of `TxnScanStream`: the snapshot holds exactly the keys in
/// `seeded`, an entry of the write buffer ends a stretch (and is yielded when
/// it is a put), a snapshot key already promoted past the begin snapshot ends
/// a stretch (and is yielded when the engine has it at its read sequence),
/// every other snapshot key extends the stretch, and the walk stops once
/// `take` entries were yielded. Called before the scan runs.
fn expected_cover(
    tx: &Transaction<'_>,
    seeded: u8,
    start: u8,
    end: u8,
    reverse: bool,
    take: usize,
) -> std::collections::BTreeSet<Vec<u8>> {
    let mut covered = std::collections::BTreeSet::new();
    let mut close = |stretch: &mut Option<(u8, u8)>| {
        if let Some((a, b)) = stretch.take() {
            for key in a.min(b)..=a.max(b) {
                covered.insert(prefix_key(DEFAULT_CF_ID, &[key]));
            }
        }
    };
    let keys: Vec<u8> = if reverse {
        (start..end).rev().collect()
    } else {
        (start..end).collect()
    };
    let mut stretch: Option<(u8, u8)> = None;
    let mut yielded = 0;
    for key in keys {
        if yielded == take {
            break;
        }
        let prefixed = prefix_key(DEFAULT_CF_ID, &[key]);
        if let Some(buffered) = tx.writes.get(&prefixed) {
            close(&mut stretch);
            yielded += usize::from(buffered.is_some());
            continue;
        }
        if key >= 6 || seeded & (1 << key) == 0 {
            continue;
        }
        let promoted = matches!(tx.mode, TxMode::Pessimistic { .. })
            .then(|| tx.tracked.get(&prefixed))
            .flatten()
            .map(|state| state.read_seq.load(Ordering::Acquire))
            .filter(|read_seq| *read_seq > tx.snapshot_seq);
        if let Some(read_seq) = promoted {
            close(&mut stretch);
            let visible = tx.engine.get_at(&prefixed, read_seq).expect("engine read");
            yielded += usize::from(visible.is_some());
            continue;
        }
        stretch = Some(stretch.map_or((key, key), |(first, _)| (first, key)));
        yielded += 1;
    }
    close(&mut stretch);
    covered
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 256, ..ProptestConfig::default() })]

    /// A transaction that scans validates exactly what a twin that reads
    /// the same snapshot keys through `get` validates, except that every
    /// written or validated key inside a stretch the scans walked is a read
    /// from the begin snapshot. The stretches are worked out by
    /// [`expected_cover`], not by the code under test.
    #[test]
    fn a_scan_validates_like_gets_of_what_it_walked(
        flavor in 0..2u8,
        level in 0..3u8,
        seeded in any::<u8>(),
        ops in proptest::collection::vec((0u8..10, 0u8..6), 0..28),
    ) {
        let (scan_dir, twin_dir) = (TempDir::new().expect("tempdir"), TempDir::new().expect("tempdir"));
        let (scan_db, twin_db) = (open_any(flavor, &scan_dir), open_any(flavor, &twin_dir));
        // Committed before the transactions begin, so the snapshot holds
        // exactly these keys; a write after begin is invisible to a scan.
        for key in (0u8..6).filter(|key| seeded & (1 << key) != 0) {
            prop_assert!(scan_db.put_external(&[key], b"s").is_ok());
            prop_assert!(twin_db.put_external(&[key], b"s").is_ok());
        }
        let mut scan_tx = scan_db.begin(isolation_level(level));
        let mut twin_tx = twin_db.begin(isolation_level(level));
        let mut covered = std::collections::BTreeSet::new();
        for (kind, key) in &ops {
            let key = [*key];
            for (db, tx) in [(&scan_db, &scan_tx), (&twin_db, &twin_tx)] {
                match kind {
                    0 => prop_assert!(tx.get(&key).is_ok()),
                    1 => prop_assert!(tx.get_for_update(&key).is_ok()),
                    2 => prop_assert!(tx.put(&key, b"v").is_ok()),
                    3 => prop_assert!(tx.delete(&key).is_ok()),
                    4 => prop_assert!(tx.merge(&key, b"op").is_ok()),
                    5 => prop_assert!(db.put_external(&key, b"v").is_ok()),
                    6 => prop_assert!(db.delete_external(&key).is_ok()),
                    _ => {}
                }
            }
            if *kind >= 7 {
                let end = [key[0] + 4];
                let reverse = *kind == 8;
                let take = if *kind == 9 { 1 } else { usize::MAX };
                covered.extend(expected_cover(&scan_tx, seeded, key[0], end[0], reverse, take));
                let direction = if reverse { ScanDirection::Reverse } else { ScanDirection::Forward };
                let mut stream = scan_tx.scan_stream_in(Some(&key), Some(&end), direction);
                let entries: Vec<Vec<u8>> = stream.by_ref().take(take).map(|(k, _)| k).collect();
                prop_assert!(stream.status().is_ok());
                drop(stream);
                for entry in entries {
                    if scan_tx.writes.get(&prefix_key(DEFAULT_CF_ID, &entry)).is_none() {
                        prop_assert!(twin_tx.get(&entry).is_ok());
                    }
                }
            }
        }

        let settle = |tx: &mut Transaction<'_>| {
            let mut writes: BTreeMap<Vec<u8>, Option<Vec<u8>>> = BTreeMap::new();
            for (key, value) in tx.writes.drain() {
                writes.entry(key).or_insert(value);
            }
            let merges = drain(&tx.merges);
            let tracked = tx.tracked.drain();
            let mut checks = tx.validation_set(tracked, &writes, &merges);
            if let Some(runs) = tx.scan_runs.take() {
                let runs = drain(&runs);
                scan_range::cover(&mut checks.reads, &runs, &writes, &merges, tx.snapshot_seq);
            }
            let written: std::collections::BTreeSet<Vec<u8>> =
                writes.keys().chain(merges.iter().map(|(key, _)| key)).cloned().collect();
            (expand(&checks, &writes, &merges), written)
        };
        let (scan_set, written) = settle(&mut scan_tx);
        let (twin_set, _) = settle(&mut twin_tx);
        let begin_seq = scan_tx.snapshot_seq;
        let mut want = twin_set.clone();
        for key in &covered {
            let read = twin_set.get(key).is_some_and(|(_, read)| *read);
            if written.contains(key) || read {
                want.insert(key.clone(), (begin_seq, true));
            }
        }
        prop_assert_eq!(scan_set, want);
        drop(scan_tx);
        drop(twin_tx);
    }
}
