//! Plan execution against real databases: which appends go in as merge
//! operands, what a read returns around them, what a read-only
//! `get_for_update` does to commit validation at each level, and what each
//! shape writes, reads back and is refused by.

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
        self.open_shaped(isolation, Shape::Point)
    }

    fn open_shaped(&self, isolation: Isolation, shape: Shape) -> TxDb {
        TxDb::open(&self.0, isolation, shape, Options::default()).unwrap()
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn plan(mops: Vec<PlannedMop>) -> TxnPlan {
    TxnPlan {
        mops,
        keys: 4,
        nonce: None,
    }
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

fn conflicted<T>(result: TxResult<T>) -> bool {
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
    first
        .execute(Model::ListAppend, Shape::Point, blind, &mut a)
        .unwrap();
    second
        .execute(Model::ListAppend, Shape::Point, blind, &mut b)
        .unwrap();
    b.commit().unwrap();
    a.commit().map(|_| ())
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
    .execute(Model::ListAppend, Shape::Point, true, &mut tx)
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
        .execute(Model::ListAppend, Shape::Point, true, &mut tx)
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
            .flat_map(|_| {
                TxnPlan::generate(model, isolation, Shape::Point, 4, &mut rng, &values).mops
            })
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
        .execute(Model::ListAppend, Shape::Point, false, &mut tx)
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
            .execute(Model::ListAppend, Shape::Point, false, &mut tx)
            .unwrap();
        // Written around the lock manager, after the read.
        db.db().put(&key_bytes(0), b"1").unwrap();
        assert_eq!(tx.commit().is_ok(), commits, "{level:?}");
    }
}

// ---- the shapes ----

fn write(key: i64, val: i64) -> PlannedMop {
    PlannedMop::Write { key, val }
}

/// Run `plan` in a transaction of its own and commit it.
fn commit(db: &TxDb, model: Model, shape: Shape, plan: &TxnPlan) -> TxResult<Vec<Mop>> {
    let mut tx = db.begin();
    let observed = plan.execute(model, shape, db.blind_appends(), &mut tx)?;
    tx.commit().map(|_| observed)
}

/// Begin two transactions on `db`, run `first` and `second` in them, commit
/// `second`, then commit `first` and return what that made of it.
fn overtaken(
    db: &TxDb,
    model: Model,
    shape: Shape,
    first: &TxnPlan,
    second: &TxnPlan,
) -> TxResult<()> {
    let (mut a, mut b) = (db.begin(), db.begin());
    first
        .execute(model, shape, db.blind_appends(), &mut a)
        .unwrap();
    second
        .execute(model, shape, db.blind_appends(), &mut b)
        .unwrap();
    b.commit().unwrap();
    a.commit().map(|_| ())
}

#[test]
fn every_shape_names_itself_and_only_two_fix_the_model() {
    for (shape, model) in [
        (Shape::Point, None),
        (Shape::Classified, None),
        (Shape::Appends, Some(Model::ListAppend)),
        (Shape::Parts, Some(Model::ListAppend)),
        (Shape::Scan, None),
    ] {
        assert_eq!(shape.model(), model, "{}", shape.as_str());
    }
}

#[test]
fn a_classified_transaction_writes_a_key_of_each_class_and_two_commit_side_by_side() {
    let scratch = Scratch::new("classified");
    let db = scratch.open_shaped(Isolation::DefraLevel, Shape::Classified);
    let side = |nonce| TxnPlan {
        mops: vec![append(0, nonce)],
        keys: 4,
        nonce: Some(nonce),
    };
    // Both begin before either commits: each read the same block as missing
    // and stored it, scanned the same heads and added one, and appended to
    // the same journal. None of that may refuse the second commit.
    overtaken(
        &db,
        Model::ListAppend,
        Shape::Classified,
        &side(2),
        &side(4),
    )
    .unwrap();
    assert!(db.db().get(b"b/even").unwrap().is_some());
    assert_eq!(
        db.db()
            .scan(Some(b"h/own/"), Some(b"h/own0"))
            .unwrap()
            .len(),
        2
    );
    side_keys_agree(db.db()).unwrap();

    // A head with no journal entry is what a commit applied by halves would
    // leave, and the check says so.
    db.db().put(b"h/own/stray", b"head").unwrap();
    let disagreement = side_keys_agree(db.db()).unwrap_err();
    assert!(disagreement.contains("3 transactions left a head and 2 a journal entry"));
}

#[test]
fn the_same_side_keys_refuse_the_second_commit_without_the_classifier() {
    // The `point` shape at the same level has no classifier, so the block
    // both stored after reading it as missing is an ordinary lost race.
    let scratch = Scratch::new("unclassified");
    let db = scratch.open(Isolation::DefraLevel);
    let side = |nonce| TxnPlan {
        mops: Vec::new(),
        keys: 4,
        nonce: Some(nonce),
    };
    let (mut a, mut b) = (db.begin(), db.begin());
    // A log needs no classifier, so the same keys can be written here.
    side(2)
        .execute(Model::ListAppend, Shape::Point, true, &mut a)
        .unwrap();
    side(4)
        .execute(Model::ListAppend, Shape::Point, true, &mut b)
        .unwrap();
    b.commit().unwrap();
    assert!(conflicted(a.commit()));
}

#[test]
fn appends_to_one_log_both_commit_and_a_read_returns_them_in_commit_order() {
    for isolation in [
        Isolation::ReadCommitted,
        Isolation::Snapshot,
        Isolation::DefraLevel,
    ] {
        let scratch = Scratch::new(&format!("appends-{isolation:?}"));
        let db = scratch.open_shaped(isolation, Shape::Appends);
        // 5 is appended under no once key and 6 under one: both land.
        overtaken(
            &db,
            Model::ListAppend,
            Shape::Appends,
            &plan(vec![append(0, 5), append(1, 7)]),
            &plan(vec![append(0, 6)]),
        )
        .unwrap();
        let observed = commit(
            &db,
            Model::ListAppend,
            Shape::Appends,
            &plan(vec![read(0), read(1), read(2)]),
        )
        .unwrap();
        assert_eq!(observed[0].2, MopVal::List(vec![6, 5]), "{isolation:?}");
        assert_eq!(observed[1].2, MopVal::List(vec![7]), "{isolation:?}");
        assert_eq!(observed[2].2, MopVal::Null, "{isolation:?}");
    }
}

#[test]
fn a_log_read_is_one_snapshot_of_the_log() {
    let scratch = Scratch::new("log-snapshot");
    let db = scratch.open_shaped(Isolation::DefraLevel, Shape::Appends);
    commit(
        &db,
        Model::ListAppend,
        Shape::Appends,
        &plan(vec![append(0, 1)]),
    )
    .unwrap();

    let mut reader = db.begin();
    commit(
        &db,
        Model::ListAppend,
        Shape::Appends,
        &plan(vec![append(0, 2)]),
    )
    .unwrap();
    let observed = plan(vec![read(0)])
        .execute(Model::ListAppend, Shape::Appends, true, &mut reader)
        .unwrap();
    assert_eq!(observed[0].2, MopVal::List(vec![1]));
    // A read of a log is never validated, so the reader commits.
    reader.commit().unwrap();
}

#[test]
fn only_log_plans_keep_appends_and_reads_apart() {
    let (mut rng, values) = (Rng::new(11), ValueSource::new(1));
    for _ in 0..200 {
        let mops = TxnPlan::generate(
            Model::ListAppend,
            Isolation::DefraLevel,
            Shape::Appends,
            4,
            &mut rng,
            &values,
        )
        .mops;
        let appends = mops
            .iter()
            .filter(|mop| matches!(mop, PlannedMop::Append { .. }))
            .count();
        assert!(appends == 0 || appends == mops.len(), "{mops:?}");
        assert!(
            mops.iter()
                .all(|mop| matches!(mop, PlannedMop::Append { .. } | PlannedMop::Read { .. }))
        );
    }
}

#[test]
fn a_part_read_is_refused_by_an_append_to_its_part_and_by_no_other() {
    // Keys 0 and 1 are the two parts of one document.
    for (appended, refused) in [(1, false), (0, true)] {
        let scratch = Scratch::new(&format!("parts-{appended}"));
        let db = scratch.open_shaped(Isolation::DefraLevel, Shape::Parts);
        commit(
            &db,
            Model::ListAppend,
            Shape::Parts,
            &plan(vec![append(0, 1), append(1, 2)]),
        )
        .unwrap();
        // The reader decides on part 0 and appends to another document.
        let outcome = overtaken(
            &db,
            Model::ListAppend,
            Shape::Parts,
            &plan(vec![read(0), append(2, 3)]),
            &plan(vec![append(appended, 9)]),
        );
        assert_eq!(conflicted(outcome), refused, "an append to part {appended}");
    }
}

/// A locking read of a part reads the part's document, as a plain read of it
/// does: `--shape parts` runs at `read-committed`, the one level whose plans
/// hold locking reads. Before, it read the point key of the same number,
/// which no parts append writes, and recorded a list that was there as
/// nothing.
#[test]
fn a_locking_read_of_a_part_reads_its_document() {
    let scratch = Scratch::new("parts-locking-read");
    let db = scratch.open_shaped(Isolation::ReadCommitted, Shape::Parts);
    commit(
        &db,
        Model::ListAppend,
        Shape::Parts,
        &plan(vec![append(0, 7)]),
    )
    .unwrap();
    let observed = commit(
        &db,
        Model::ListAppend,
        Shape::Parts,
        &plan(vec![read_for_update(0), read_for_update(1), read(0)]),
    )
    .unwrap();
    let lists: Vec<&MopVal> = observed.iter().map(|mop| &mop.2).collect();
    assert_eq!(
        lists,
        [
            &MopVal::List(vec![7]),
            &MopVal::Null,
            &MopVal::List(vec![7])
        ],
        "the append in part 0, nothing in part 1, and a locking read that agrees with a plain one"
    );
    assert_eq!(stored(&db, 0), None, "a parts plan wrote a point key");
}

#[test]
fn appends_to_one_part_both_commit_and_do_not_reach_its_neighbour() {
    let scratch = Scratch::new("parts-read");
    let db = scratch.open_shaped(Isolation::DefraLevel, Shape::Parts);
    // Neither read the part, so the two operands commute.
    overtaken(
        &db,
        Model::ListAppend,
        Shape::Parts,
        &plan(vec![append(0, 5)]),
        &plan(vec![append(0, 6), append(3, 8)]),
    )
    .unwrap();
    let observed = commit(
        &db,
        Model::ListAppend,
        Shape::Parts,
        &plan(vec![
            read(0),
            append(0, 7),
            read(0),
            read(1),
            read(2),
            read(3),
        ]),
    )
    .unwrap();
    let lists: Vec<&MopVal> = observed.iter().map(|mop| &mop.2).collect();
    assert_eq!(
        lists,
        [
            &MopVal::List(vec![6, 5]),
            &MopVal::Int(7),
            &MopVal::List(vec![6, 5, 7]),
            &MopVal::Null,
            &MopVal::Null,
            &MopVal::List(vec![8]),
        ],
        "commit order in part 0, its own operand read back, and nothing in parts never appended to"
    );
}

#[test]
fn a_scan_is_recorded_as_a_read_of_every_key_and_refused_by_a_write_among_them() {
    for isolation in [Isolation::RepeatableRead, Isolation::DefraLevel] {
        let scratch = Scratch::new(&format!("scan-{isolation:?}"));
        let db = scratch.open_shaped(isolation, Shape::Scan);
        commit(
            &db,
            Model::RwRegister,
            Shape::Scan,
            &plan(vec![write(1, 5)]),
        )
        .unwrap();

        let scan_then_write = plan(vec![PlannedMop::ScanAll, write(0, 6)]);
        let invoked = scan_then_write.invoke_value();
        let keys: Vec<i64> = invoked.iter().map(|mop| mop.1).collect();
        assert_eq!(
            keys,
            [0, 1, 2, 3, 0],
            "a read of each of the four keys, then the write"
        );

        let mut tx = db.begin();
        let observed = scan_then_write
            .execute(Model::RwRegister, Shape::Scan, db.blind_appends(), &mut tx)
            .unwrap();
        assert_eq!(observed[0].2, MopVal::Null);
        assert_eq!(observed[1].2, MopVal::Int(5));
        tx.commit().unwrap();

        // Write skew through a scan: each scans, sees the other's key as it
        // was, and writes its own. A key that appears where the scan found
        // none is a write inside the range too, so the second is refused.
        let outcome = overtaken(
            &db,
            Model::RwRegister,
            Shape::Scan,
            &plan(vec![PlannedMop::ScanAll, write(2, 7)]),
            &plan(vec![PlannedMop::ScanAll, write(3, 8)]),
        );
        assert!(conflicted(outcome), "{isolation:?}");
    }
}

#[test]
fn an_append_after_a_scan_builds_on_the_list_the_scan_returned() {
    let scratch = Scratch::new("scan-append");
    let db = scratch.open_shaped(Isolation::DefraLevel, Shape::Scan);
    commit(
        &db,
        Model::ListAppend,
        Shape::Scan,
        &plan(vec![append(0, 1)]),
    )
    .unwrap();
    let observed = commit(
        &db,
        Model::ListAppend,
        Shape::Scan,
        &plan(vec![
            PlannedMop::ScanAll,
            append(0, 2),
            append(0, 3),
            append(1, 4),
        ]),
    )
    .unwrap();
    assert_eq!(observed[0].2, MopVal::List(vec![1]));
    assert_eq!(stored(&db, 0).as_deref(), Some(&b"1,2,3"[..]));
    assert_eq!(stored(&db, 1).as_deref(), Some(&b"4"[..]));
}
