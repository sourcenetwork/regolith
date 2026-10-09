//! Plan execution against real databases: which appends go in as merge
//! operands, what a read returns around them, and what a read-only
//! `get_for_update` does to commit validation at each level.

use std::path::PathBuf;

use super::*;

/// A database directory under the crate's gitignored `target/`, removed
/// when the test ends. Declare it before the database so the database is
/// dropped first.
struct Scratch(PathBuf);

impl Scratch {
    fn new(name: &str) -> Self {
        let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("target/test-scratch")
            .join(format!("{}-{name}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        Self(dir)
    }

    fn open(&self, isolation: Isolation) -> TxDb {
        TxDb::open(&self.0, isolation, Options::default()).unwrap()
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn plan(mops: Vec<PlannedMop>) -> TxnPlan {
    TxnPlan { mops }
}

fn append(key: i64, val: i64) -> PlannedMop {
    PlannedMop::Append { key, val }
}

fn read(key: i64) -> PlannedMop {
    PlannedMop::Read { key }
}

fn read_for_update(key: i64) -> PlannedMop {
    PlannedMop::ReadForUpdate { key }
}

fn stored(db: &TxDb, key: i64) -> Option<Vec<u8>> {
    db.db().get(&key_bytes(key)).unwrap()
}

fn conflicted(result: TxResult<()>) -> bool {
    matches!(result, Err(TransactionError::Conflict { .. }))
}

/// Begin two transactions on `db`, run `first` and `second` in them, then
/// commit `second` before `first`.
fn commit_second_then_first(
    db: &TxDb,
    blind: bool,
    first: &TxnPlan,
    second: &TxnPlan,
) -> TxResult<()> {
    let (mut a, mut b) = (db.begin(), db.begin());
    first.execute(Model::ListAppend, blind, &mut a).unwrap();
    second.execute(Model::ListAppend, blind, &mut b).unwrap();
    b.commit().unwrap();
    a.commit()
}

#[test]
fn blind_appends_to_one_key_both_commit_in_commit_order() {
    let scratch = Scratch::new("blind");
    let db = scratch.open(Isolation::DefraLevel);
    assert!(db.blind_appends());
    let committed = commit_second_then_first(
        &db,
        db.blind_appends(),
        &plan(vec![append(0, 1)]),
        &plan(vec![append(0, 2)]),
    );
    committed.unwrap();
    assert_eq!(stored(&db, 0).as_deref(), Some(&b"2,1"[..]));
}

#[test]
fn read_modify_write_appends_to_one_key_do_not_both_commit() {
    let scratch = Scratch::new("rmw");
    let db = scratch.open(Isolation::DefraLevel);
    let committed = commit_second_then_first(
        &db,
        false,
        &plan(vec![append(0, 1)]),
        &plan(vec![append(0, 2)]),
    );
    assert!(conflicted(committed));
}

#[test]
fn an_append_to_a_key_the_transaction_read_conflicts_with_a_concurrent_append() {
    let scratch = Scratch::new("read-then-append");
    let db = scratch.open(Isolation::DefraLevel);
    let committed = commit_second_then_first(
        &db,
        true,
        &plan(vec![read(0), append(0, 5)]),
        &plan(vec![append(0, 6)]),
    );
    assert!(conflicted(committed));
}

#[test]
fn only_defra_level_appends_blind() {
    for isolation in [
        Isolation::ReadCommitted,
        Isolation::Snapshot,
        Isolation::RepeatableRead,
        Isolation::Serializable,
    ] {
        let scratch = Scratch::new(&format!("flavour-{isolation:?}"));
        assert!(!scratch.open(isolation).blind_appends());
    }
}

#[test]
fn a_read_after_a_blind_append_includes_the_transactions_own_elements() {
    let scratch = Scratch::new("own-elements");
    let db = scratch.open(Isolation::DefraLevel);
    db.db().put(&key_bytes(0), b"1,2").unwrap();

    let mut tx = db.begin();
    let observed = plan(vec![
        append(0, 7),
        read(0),
        append(0, 8),
        read(0),
        append(1, 9),
        read(1),
    ])
    .execute(Model::ListAppend, true, &mut tx)
    .unwrap();
    assert_eq!(observed[1].2, MopVal::List(vec![1, 2, 7]));
    assert_eq!(observed[3].2, MopVal::List(vec![1, 2, 7, 8]));
    assert_eq!(observed[5].2, MopVal::List(vec![9]));
    tx.commit().unwrap();

    assert_eq!(stored(&db, 0).as_deref(), Some(&b"1,2,7,8"[..]));
    assert_eq!(stored(&db, 1).as_deref(), Some(&b"9"[..]));
}

#[test]
fn a_read_before_an_append_sees_the_append_through_the_write_buffer() {
    let scratch = Scratch::new("read-first");
    let db = scratch.open(Isolation::DefraLevel);
    db.db().put(&key_bytes(0), b"1,2").unwrap();

    let mut tx = db.begin();
    let observed = plan(vec![read(0), append(0, 7), read(0), append(0, 8), read(0)])
        .execute(Model::ListAppend, true, &mut tx)
        .unwrap();
    assert_eq!(observed[0].2, MopVal::List(vec![1, 2]));
    assert_eq!(observed[2].2, MopVal::List(vec![1, 2, 7]));
    assert_eq!(observed[4].2, MopVal::List(vec![1, 2, 7, 8]));
    tx.commit().unwrap();
    assert_eq!(stored(&db, 0).as_deref(), Some(&b"1,2,7,8"[..]));
}

#[test]
fn only_read_committed_plans_hold_a_read_for_update() {
    let held = |model, isolation| {
        let (mut rng, values) = (Rng::new(7), ValueSource::new(1));
        (0..200)
            .flat_map(|_| TxnPlan::generate(model, isolation, 4, &mut rng, &values).mops)
            .filter(|mop| matches!(mop, PlannedMop::ReadForUpdate { .. }))
            .count()
    };
    for model in [Model::ListAppend, Model::RwRegister] {
        assert!(held(model, Isolation::ReadCommitted) > 0);
        for isolation in [
            Isolation::Snapshot,
            Isolation::RepeatableRead,
            Isolation::Serializable,
            Isolation::DefraLevel,
        ] {
            assert_eq!(held(model, isolation), 0);
        }
    }
}

#[test]
fn a_read_for_update_is_recorded_as_a_read() {
    let invoke = plan(vec![read_for_update(3)]).invoke_value();
    assert_eq!((invoke[0].0.as_str(), invoke[0].1), ("r", 3));
    assert_eq!(invoke[0].2, MopVal::Null);

    let scratch = Scratch::new("recorded");
    let db = scratch.open(Isolation::ReadCommitted);
    db.db().put(&key_bytes(3), b"4,5").unwrap();
    let mut tx = db.begin();
    let observed = plan(vec![read_for_update(3)])
        .execute(Model::ListAppend, false, &mut tx)
        .unwrap();
    assert_eq!(observed[0].2, MopVal::List(vec![4, 5]));
}

/// The two levels differ in exactly this: a key read through
/// `get_for_update` and never written is validated at `SnapshotIsolation`
/// and not at `ReadCommitted`. Same flavour, same schedule, same plan.
#[test]
fn a_read_for_update_is_validated_at_snapshot_isolation_and_not_at_read_committed() {
    for (level, commits) in [
        (IsolationLevel::ReadCommitted, true),
        (IsolationLevel::SnapshotIsolation, false),
    ] {
        let scratch = Scratch::new(&format!("validated-{level:?}"));
        let db = TransactionDb::open(&scratch.0, Options::default())
            .unwrap()
            .with_isolation(level);
        let mut tx = db.begin(&TxnOptions::new());
        plan(vec![read_for_update(0)])
            .execute(Model::ListAppend, false, &mut tx)
            .unwrap();
        // Written around the lock manager, after the read.
        db.db().put(&key_bytes(0), b"1").unwrap();
        assert_eq!(tx.commit().is_ok(), commits, "{level:?}");
    }
}
