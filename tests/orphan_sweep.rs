//! A writable open removes SSTables the manifest does not reference.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use regolith::{Db, Options};

fn table_ids(dir: &Path) -> BTreeSet<u64> {
    std::fs::read_dir(dir.join("sst"))
        .unwrap()
        .filter_map(|e| {
            let path = e.unwrap().path();
            if path.extension()? != "sst" {
                return None;
            }
            path.file_stem()?.to_str()?.parse().ok()
        })
        .collect()
}

fn table_path(dir: &Path, id: u64) -> PathBuf {
    dir.join("sst").join(format!("{id:06}.sst"))
}

fn key(i: u32) -> Vec<u8> {
    format!("key{i:08}").into_bytes()
}

/// A closed store with several flushed tables, and the ids that are live.
fn seeded_store() -> (tempfile::TempDir, BTreeSet<u64>) {
    let dir = tempfile::tempdir().unwrap();
    let db = Db::open(
        dir.path(),
        Options {
            l0_compaction_trigger: 1_000,
            ..Options::default()
        },
    )
    .unwrap();
    for batch in 0..4u32 {
        for i in 0..500u32 {
            db.put(&key(batch * 500 + i), b"value").unwrap();
        }
        db.flush().unwrap();
    }
    db.close().unwrap();
    drop(db);
    let live = table_ids(dir.path());
    assert!(live.len() >= 4);
    (dir, live)
}

/// Copy a live table to an unused id below the highest live one, so it
/// carries real data but no manifest record names it.
fn plant_orphan(dir: &Path, live: &BTreeSet<u64>) -> u64 {
    let max = *live.iter().max().unwrap();
    let id = (1..max).find(|id| !live.contains(id)).unwrap();
    std::fs::copy(
        table_path(dir, *live.iter().next().unwrap()),
        table_path(dir, id),
    )
    .unwrap();
    id
}

fn assert_all_keys(db: &Db) {
    for i in 0..2_000u32 {
        assert!(db.get(&key(i)).unwrap().is_some(), "key {i} lost");
    }
}

#[test]
fn a_writable_open_removes_unreferenced_tables() {
    let (dir, live) = seeded_store();
    let orphan = plant_orphan(dir.path(), &live);
    let far_ahead = 999_999;
    std::fs::copy(
        table_path(dir.path(), orphan),
        table_path(dir.path(), far_ahead),
    )
    .unwrap();
    std::fs::write(dir.path().join("sst").join("scratch.tmp"), b"x").unwrap();

    let db = Db::open(dir.path(), Options::default()).unwrap();

    let after = table_ids(dir.path());
    assert!(
        !after.contains(&orphan),
        "orphan {orphan} survived the open"
    );
    assert!(live.is_subset(&after), "a live table was removed");
    assert!(
        after.contains(&far_ahead),
        "an id at or past next_file_id must be left alone"
    );
    assert!(dir.path().join("sst").join("scratch.tmp").exists());
    assert_all_keys(&db);
}

#[test]
fn a_read_only_open_removes_nothing() {
    let (dir, live) = seeded_store();
    let orphan = plant_orphan(dir.path(), &live);

    let db = Db::open_read_only(dir.path(), Options::default()).unwrap();

    assert!(table_ids(dir.path()).contains(&orphan));
    assert_all_keys(&db);
}

#[test]
fn a_torn_manifest_suppresses_the_sweep() {
    let (dir, live) = seeded_store();
    let orphan = plant_orphan(dir.path(), &live);
    let manifest = dir.path().join("MANIFEST");
    let mut bytes = std::fs::read(&manifest).unwrap();
    bytes.extend_from_slice(&[0xAB; 7]);
    std::fs::write(&manifest, bytes).unwrap();

    let db = Db::open(dir.path(), Options::default()).unwrap();

    assert!(
        table_ids(dir.path()).contains(&orphan),
        "a replay that lost records must not judge what is unreferenced"
    );
    assert_all_keys(&db);
}
