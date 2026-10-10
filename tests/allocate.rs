//! `Db::allocate`: ranges of a `u64` counter that never repeat, only grow,
//! never conflict, never wait on a stall, and survive a reopen.
//!
//! These are the configurations of `Allocate.tla` run against the code. The
//! crash half (a surviving use keeps its allocation) is in
//! `append_allocate_power_loss.rs`.

// Native-only. wasm-pack builds every test target for wasm32, and these use
// threads and the filesystem. The browser suite lives in tests/wasm_opfs*.rs.
#![cfg(not(target_arch = "wasm32"))]

use std::collections::BTreeSet;
use std::ops::Range;
use std::path::Path;
use std::sync::Arc;
use std::thread;

use proptest::prelude::*;
use regolith::prelude::*;
use regolith::{Db, DurabilityMode, Error, MemEnv, TransactionDb};
use tempfile::TempDir;

fn counter(db: &Db, key: &[u8]) -> Option<u64> {
    db.get(key)
        .unwrap()
        .map(|bytes| u64::from_be_bytes(bytes.try_into().expect("the counter is eight bytes")))
}

fn mem_options(env: &MemEnv) -> Options {
    Options::default()
        .env(Arc::new(env.clone()))
        .max_background_compactions(0)
}

#[test]
fn a_new_counter_starts_at_one_and_ranges_follow_each_other() {
    let dir = TempDir::new().unwrap();
    let db = Db::open(dir.path(), Options::default()).unwrap();
    assert_eq!(counter(&db, b"ids"), None, "absent means zero");
    assert_eq!(db.allocate(b"ids", 3).unwrap(), 1..4);
    assert_eq!(
        counter(&db, b"ids"),
        Some(3),
        "the key holds the last value reserved"
    );
    assert_eq!(db.allocate(b"ids", 2).unwrap(), 4..6);
    assert_eq!(db.allocate(b"ids", 1).unwrap(), 6..7);
    assert_eq!(counter(&db, b"ids"), Some(6));
    assert_eq!(
        db.get(b"ids").unwrap().unwrap().len(),
        8,
        "eight big-endian bytes"
    );
}

#[test]
fn counters_at_different_keys_are_independent() {
    let dir = TempDir::new().unwrap();
    let db = Db::open(dir.path(), Options::default()).unwrap();
    assert_eq!(db.allocate(b"a", 5).unwrap(), 1..6);
    assert_eq!(db.allocate(b"b", 1).unwrap(), 1..2);
    assert_eq!(db.allocate(b"a", 1).unwrap(), 6..7);
}

#[test]
fn reserving_nothing_returns_an_empty_range_and_writes_nothing() {
    let dir = TempDir::new().unwrap();
    let db = Db::open(dir.path(), Options::default()).unwrap();
    let empty = db.allocate(b"ids", 0).unwrap();
    assert!(empty.is_empty());
    assert_eq!(empty.start, 1, "the next value to be reserved");
    assert_eq!(counter(&db, b"ids"), None);
    db.allocate(b"ids", 4).unwrap();
    let before = db.latest_sequence();
    let empty = db.allocate(b"ids", 0).unwrap();
    assert!(empty.is_empty());
    assert_eq!(empty.start, 5);
    assert_eq!(db.latest_sequence(), before, "nothing was written");
    assert_eq!(db.allocate(b"ids", 1).unwrap(), 5..6);
}

#[test]
fn a_counter_that_is_not_eight_bytes_is_refused_and_left_alone() {
    let dir = TempDir::new().unwrap();
    let db = Db::open(dir.path(), Options::default()).unwrap();
    for bad in [&b""[..], b"1234567", b"123456789"] {
        db.put(b"ids", bad).unwrap();
        for n in [0, 1] {
            let err = db.allocate(b"ids", n).unwrap_err();
            assert!(matches!(err, Error::InvalidArgument(_)), "{err:?}");
            assert!(
                !err.to_string().contains("1234567"),
                "no value bytes in the message: {err}"
            );
        }
        assert_eq!(db.get(b"ids").unwrap().as_deref(), Some(bad));
    }
}

#[test]
fn the_counter_stops_below_the_largest_value_and_reserves_nothing_past_it() {
    let dir = TempDir::new().unwrap();
    let db = Db::open(dir.path(), Options::default()).unwrap();
    db.put(b"ids", &(u64::MAX - 3).to_be_bytes()).unwrap();
    assert_eq!(db.allocate(b"ids", 2).unwrap(), u64::MAX - 2..u64::MAX);
    assert_eq!(counter(&db, b"ids"), Some(u64::MAX - 1));
    for n in [1, 2, u64::MAX] {
        assert!(matches!(
            db.allocate(b"ids", n),
            Err(Error::InvalidArgument(_))
        ));
    }
    assert_eq!(counter(&db, b"ids"), Some(u64::MAX - 1), "unchanged");
    assert!(matches!(
        db.allocate(b"fresh", u64::MAX),
        Err(Error::InvalidArgument(_))
    ));
    assert_eq!(db.allocate(b"fresh", u64::MAX - 1).unwrap(), 1..u64::MAX);
}

#[test]
fn a_key_past_the_key_limit_and_a_closed_or_read_only_handle_are_refused() {
    let dir = TempDir::new().unwrap();
    let db = Db::open(dir.path(), Options::default().max_key_size(4)).unwrap();
    assert!(matches!(
        db.allocate(b"too-long", 1),
        Err(Error::InvalidArgument(_))
    ));
    assert_eq!(db.allocate(b"ok", 1).unwrap(), 1..2);
    db.close().unwrap();
    assert!(matches!(db.allocate(b"ok", 1), Err(Error::Closed)));
    drop(db);

    let read_only = Db::open_read_only(dir.path(), Options::default()).unwrap();
    assert!(matches!(read_only.allocate(b"ok", 1), Err(Error::ReadOnly)));
    assert!(matches!(read_only.allocate(b"ok", 0), Err(Error::ReadOnly)));
}

#[test]
fn both_transaction_databases_share_the_counter_with_their_database() {
    let dir = TempDir::new().unwrap();
    let optimistic = OptimisticTransactionDb::open(dir.path(), Options::default()).unwrap();
    assert_eq!(optimistic.allocate(b"ids", 2).unwrap(), 1..3);
    assert_eq!(optimistic.db().allocate(b"ids", 1).unwrap(), 3..4);
    drop(optimistic);

    let dir = TempDir::new().unwrap();
    let pessimistic = TransactionDb::open(dir.path(), Options::default()).unwrap();
    assert_eq!(pessimistic.allocate(b"ids", 2).unwrap(), 1..3);
    assert_eq!(pessimistic.db().allocate(b"ids", 1).unwrap(), 3..4);
}

#[test]
fn the_counter_continues_after_a_reopen_by_replay_and_from_a_table() {
    let env = MemEnv::new();
    let path = Path::new("/ids-db");
    {
        let db = Db::open(path, mem_options(&env)).unwrap();
        assert_eq!(db.allocate(b"ids", 10).unwrap(), 1..11);
    }
    {
        let db = Db::open(path, mem_options(&env)).unwrap();
        assert_eq!(
            db.allocate(b"ids", 5).unwrap(),
            11..16,
            "recovered from the log"
        );
        db.flush().unwrap();
        assert_eq!(db.allocate(b"ids", 1).unwrap(), 16..17);
    }
    let db = Db::open(path, mem_options(&env)).unwrap();
    assert_eq!(db.allocate(b"ids", 1).unwrap(), 17..18);

    for durability in [DurabilityMode::Immediate, DurabilityMode::Eventual] {
        let dir = TempDir::new().unwrap();
        let options = || Options::default().durability(durability);
        {
            let db = Db::open(dir.path(), options()).unwrap();
            db.allocate(b"ids", 7).unwrap();
            db.close().unwrap();
        }
        let db = Db::open(dir.path(), options()).unwrap();
        assert_eq!(db.allocate(b"ids", 1).unwrap(), 8..9, "{durability:?}");
    }
}

/// An allocation is not part of any transaction, so a transaction that aborts
/// after allocating leaves its values unused: a gap, and no value is reissued.
#[test]
fn values_reserved_by_a_transaction_that_aborts_are_skipped() {
    let dir = TempDir::new().unwrap();
    let db = OptimisticTransactionDb::open(dir.path(), Options::default()).unwrap();
    let aborted = db.begin(&TxnOptions::new());
    let skipped = db.allocate(b"ids", 3).unwrap();
    aborted
        .put(format!("doc/{}", skipped.start).as_bytes(), b"x")
        .unwrap();
    aborted.rollback();

    let kept = db.begin(&TxnOptions::new());
    let used = db.allocate(b"ids", 2).unwrap();
    for v in used.clone() {
        kept.put(format!("doc/{v}").as_bytes(), b"x").unwrap();
    }
    kept.commit().unwrap();
    assert_eq!((skipped, used), (1..4, 4..6));
    assert_eq!(db.db().get(b"doc/1").unwrap(), None);
    assert!(db.db().get(b"doc/4").unwrap().is_some());
}

/// A write under a hard stall that compaction cannot relieve fails with
/// `Busy` (with inline compaction on and no queue, the write runs the steps
/// itself and finds none relieves it); allocation is not a write the stall
/// applies to.
#[test]
fn allocation_does_not_wait_while_writes_are_stalled() {
    let dir = TempDir::new().unwrap();
    let db = Db::open(
        dir.path(),
        Options::default()
            .write_buffer_size(32 * 1024)
            .block_size(4 * 1024)
            .block_cache_size(64 * 1024)
            .target_file_size(64 * 1024)
            .level_base_bytes(128 * 1024)
            // Nothing can leave L0 while a snapshot pins the data and the
            // stop trigger is this low, so the stall is a dead end.
            .level0_stop_writes_trigger(2)
            .level0_slowdown_writes_trigger(2)
            .l0_compaction_trigger(64)
            .max_background_compactions(0)
            .inline_compaction(true),
    )
    .unwrap();
    let _pin = db.snapshot();
    let value = vec![7u8; 512];
    let mut stalled = false;
    for i in 0..4_000usize {
        if let Err(Error::Busy(_)) = db.put(format!("key{i:06}").as_bytes(), &value) {
            stalled = true;
            break;
        }
    }
    assert!(stalled, "the writes never stalled, so this proves nothing");

    for expected in 1..=20u64 {
        assert_eq!(db.allocate(b"ids", 1).unwrap(), expected..expected + 1);
    }
    assert!(matches!(db.put(b"another", &value), Err(Error::Busy(_))));
}

/// Eight threads allocate and use what they get. No value is returned twice,
/// each thread sees its own ranges grow, no allocation or commit that uses its
/// values conflicts, and the counter is where the last range left it, also
/// after a reopen.
#[test]
fn eight_threads_get_unique_growing_ranges_and_never_conflict() {
    const THREADS: usize = 8;
    const ROUNDS: usize = 150;
    let dir = TempDir::new().unwrap();
    let db = Arc::new(OptimisticTransactionDb::open(dir.path(), Options::default()).unwrap());
    let handles: Vec<_> = (0..THREADS)
        .map(|t| {
            let db = Arc::clone(&db);
            thread::spawn(move || {
                let mut mine: Vec<Range<u64>> = Vec::new();
                for round in 0..ROUNDS {
                    let n = 1 + ((t + round) % 4) as u64;
                    let range = db.allocate(b"ids", n).unwrap();
                    if let Some(previous) = mine.last() {
                        assert!(previous.end <= range.start, "a thread's ranges only grow");
                    }
                    // Half the threads use their values in a transaction that
                    // touches nothing else in common: it must commit.
                    if t % 2 == 0 {
                        let tx = db.begin(&TxnOptions::new());
                        for v in range.clone() {
                            tx.put(format!("used/{v:020}").as_bytes(), &v.to_be_bytes())
                                .unwrap();
                        }
                        tx.commit()
                            .unwrap_or_else(|e| panic!("a commit using its values failed: {e}"));
                    }
                    mine.push(range);
                }
                mine
            })
        })
        .collect();
    let ranges: Vec<Range<u64>> = handles
        .into_iter()
        .flat_map(|h| h.join().unwrap())
        .collect();

    let mut values = BTreeSet::new();
    for range in &ranges {
        for v in range.clone() {
            assert!(values.insert(v), "value {v} was returned twice");
        }
    }
    let total = values.len() as u64;
    assert_eq!(
        values,
        (1..=total).collect::<BTreeSet<_>>(),
        "with no aborts the values are 1 to the total, no gaps"
    );
    assert_eq!(counter(db.db(), b"ids"), Some(total));
    drop(db);

    let db = Db::open(dir.path(), Options::default()).unwrap();
    assert_eq!(db.allocate(b"ids", 1).unwrap(), total + 1..total + 2);
    let used = db.scan(Some(b"used/"), Some(b"used0")).unwrap().len() as u64;
    assert!(used > 0 && used <= total);
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 64, ..ProptestConfig::default() })]

    /// Any sequence of allocations, a reopen between some, hands out each
    /// value once and in order.
    #[test]
    fn any_sequence_of_allocations_hands_out_each_value_once_in_order(
        steps in prop::collection::vec((0u64..6, prop::bool::weighted(0.2), 0u8..2), 1..40)
    ) {
        let env = MemEnv::new();
        let path = Path::new("/prop-ids");
        let mut db = Some(Db::open(path, mem_options(&env)).unwrap());
        let (mut next, mut odd_last) = (1u64, 0u64);
        for (n, reopen, which) in steps {
            if reopen {
                drop(db.take());
                db = Some(Db::open(path, mem_options(&env)).unwrap());
            }
            // Two counters interleave without touching each other.
            let key: &[u8] = if which == 0 { b"even" } else { b"odd" };
            let range = db.as_ref().unwrap().allocate(key, n).unwrap();
            prop_assert_eq!(range.end - range.start, n);
            if which == 0 {
                prop_assert_eq!(range.start, next);
                next = range.end;
            } else {
                prop_assert_eq!(range.start, odd_last + 1);
                odd_last += n;
                prop_assert_eq!(counter(db.as_ref().unwrap(), key).unwrap_or(0), odd_last);
            }
        }
        prop_assert_eq!(counter(db.as_ref().unwrap(), b"even").unwrap_or(0) + 1, next);
    }
}
