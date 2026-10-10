use std::fs;

use super::*;
use crate::Options;
use tempfile::TempDir;

fn tiny_flush_opts() -> Options {
    Options::default().write_buffer_size(4 * 1024)
}

fn populate(db: &Db, prefix: &str, n: usize) {
    let filler = vec![0u8; 256];
    for i in 0..n {
        let k = format!("{}_{:05}", prefix, i);
        let mut v = filler.clone();
        v.extend_from_slice(k.as_bytes());
        db.put(k.as_bytes(), &v).unwrap();
    }
}

fn assert_has(db: &Db, prefix: &str, n: usize) {
    let filler = vec![0u8; 256];
    for i in 0..n {
        let k = format!("{}_{:05}", prefix, i);
        let mut expected = filler.clone();
        expected.extend_from_slice(k.as_bytes());
        assert_eq!(db.get(k.as_bytes()).unwrap(), Some(expected));
    }
}

fn shared_bytes(dir: &Path) -> u64 {
    let shared = dir.join("shared");
    let mut total = 0u64;
    if let Ok(entries) = fs::read_dir(&shared) {
        for entry in entries.flatten() {
            if let Ok(md) = entry.metadata() {
                total += md.len();
            }
        }
    }
    total
}

fn shared_count(dir: &Path) -> usize {
    let shared = dir.join("shared");
    fs::read_dir(&shared)
        .map(|it| it.flatten().count())
        .unwrap_or(0)
}

fn shared_file_paths(dir: &Path) -> Vec<PathBuf> {
    let shared = dir.join("shared");
    let mut paths: Vec<_> = fs::read_dir(&shared)
        .unwrap()
        .flatten()
        .map(|entry| entry.path())
        .collect();
    paths.sort();
    paths
}

fn corrupt_file_same_size(path: &Path) {
    let mut bytes = fs::read(path).unwrap();
    assert!(!bytes.is_empty());
    bytes[0] ^= 0xFF;
    fs::write(path, bytes).unwrap();
}

#[test]
fn backup_and_restore_roundtrip() {
    let src_dir = TempDir::new().unwrap();
    let bkp_dir = TempDir::new().unwrap();
    let tgt_dir = TempDir::new().unwrap();

    let db = Db::open(src_dir.path(), tiny_flush_opts()).unwrap();
    populate(&db, "k", 300);

    let mut engine = BackupEngine::open(bkp_dir.path()).unwrap();
    let id = engine.create_backup(&db).unwrap();
    let infos = engine.list_backups();
    assert_eq!(infos.len(), 1);
    assert_eq!(infos[0].id, id);
    assert!(infos[0].file_count >= 1);

    engine.restore(id, tgt_dir.path(), None).unwrap();
    drop(db);

    let reopened = Db::open(tgt_dir.path(), Options::default()).unwrap();
    assert_has(&reopened, "k", 300);
}

#[test]
fn an_ingested_table_restores_at_its_recorded_sequence() {
    let src_dir = TempDir::new().unwrap();
    let bkp_dir = TempDir::new().unwrap();
    let tgt_dir = TempDir::new().unwrap();
    let db = Db::open(src_dir.path(), Options::default()).unwrap();
    db.put(b"k", b"old").unwrap();
    db.compact_range(None, None).wait().unwrap();
    let source = src_dir.path().join("source.sst");
    let mut writer = crate::SstFileWriter::create(&source, &Options::default()).unwrap();
    writer.put(b"k", b"new").unwrap();
    writer.finish().unwrap();
    // Lands above the old table, and stays uncompacted, so the restore
    // reads it through the sequence its manifest record carries.
    db.ingest_external_files(&[source], crate::IngestOptions::default())
        .wait()
        .unwrap();

    let mut engine = BackupEngine::open(bkp_dir.path()).unwrap();
    let id = engine.create_backup(&db).unwrap();
    engine.restore(id, tgt_dir.path(), None).unwrap();
    let restored = Db::open(tgt_dir.path(), Options::default()).unwrap();
    assert_eq!(restored.get(b"k").unwrap().as_deref(), Some(&b"new"[..]));
}

#[test]
fn incremental_backup_dedupes() {
    let src_dir = TempDir::new().unwrap();
    let bkp_dir = TempDir::new().unwrap();
    let db = Db::open(src_dir.path(), tiny_flush_opts()).unwrap();
    populate(&db, "x", 400);
    db.compact_range(None, None).wait().unwrap();

    let mut engine = BackupEngine::open(bkp_dir.path()).unwrap();
    let _id1 = engine.create_backup(&db).unwrap();
    let shared_bytes_1 = shared_bytes(bkp_dir.path());
    let shared_count_1 = shared_count(bkp_dir.path());

    // No writes between backups - second backup must add no
    // shared files.
    let _id2 = engine.create_backup(&db).unwrap();
    let shared_bytes_2 = shared_bytes(bkp_dir.path());
    let shared_count_2 = shared_count(bkp_dir.path());

    assert_eq!(shared_bytes_1, shared_bytes_2);
    assert_eq!(shared_count_1, shared_count_2);
    assert_eq!(engine.list_backups().len(), 2);
}

#[test]
fn create_backup_replaces_corrupt_existing_shared_object() {
    let src_dir = TempDir::new().unwrap();
    let bkp_dir = TempDir::new().unwrap();
    let tgt_dir = TempDir::new().unwrap();
    let db = Db::open(src_dir.path(), tiny_flush_opts()).unwrap();
    populate(&db, "r", 400);
    db.compact_range(None, None).wait().unwrap();

    let mut engine = BackupEngine::open(bkp_dir.path()).unwrap();
    let _id1 = engine.create_backup(&db).unwrap();
    let shared_files = shared_file_paths(bkp_dir.path());
    assert!(!shared_files.is_empty());
    let original_sizes: Vec<u64> = shared_files
        .iter()
        .map(|path| fs::metadata(path).unwrap().len())
        .collect();
    for path in &shared_files {
        corrupt_file_same_size(path);
    }

    let id2 = engine.create_backup(&db).unwrap();

    for (path, original_size) in shared_files.iter().zip(original_sizes) {
        assert_eq!(fs::metadata(path).unwrap().len(), original_size);
    }
    engine.restore(id2, tgt_dir.path(), None).unwrap();
    drop(db);
    let restored = Db::open(tgt_dir.path(), Options::default()).unwrap();
    assert_has(&restored, "r", 400);
}

#[test]
fn restore_rejects_corrupt_shared_object() {
    let src_dir = TempDir::new().unwrap();
    let bkp_dir = TempDir::new().unwrap();
    let tgt_dir = TempDir::new().unwrap();
    let db = Db::open(src_dir.path(), tiny_flush_opts()).unwrap();
    populate(&db, "bad", 300);
    db.compact_range(None, None).wait().unwrap();

    let mut engine = BackupEngine::open(bkp_dir.path()).unwrap();
    let id = engine.create_backup(&db).unwrap();
    let shared_files = shared_file_paths(bkp_dir.path());
    assert!(!shared_files.is_empty());
    corrupt_file_same_size(&shared_files[0]);

    let kind = match engine.restore(id, tgt_dir.path(), None) {
        Err(Error::Corruption(e)) => e.kind(),
        Err(e) => panic!("expected corruption error, got {e:?}"),
        Ok(()) => panic!("expected restore to reject corrupt shared object"),
    };
    assert_eq!(kind, io::ErrorKind::InvalidData);
}

#[test]
fn delete_backup_gcs_unreferenced_files() {
    let src_dir = TempDir::new().unwrap();
    let bkp_dir = TempDir::new().unwrap();
    let db = Db::open(src_dir.path(), tiny_flush_opts()).unwrap();
    populate(&db, "a", 200);
    db.compact_range(None, None).wait().unwrap();

    let mut engine = BackupEngine::open(bkp_dir.path()).unwrap();
    let id1 = engine.create_backup(&db).unwrap();
    let shared_after_1 = shared_count(bkp_dir.path());
    assert!(shared_after_1 >= 1);

    // New data that doesn't overlap prior SSTs.
    populate(&db, "z", 200);
    db.compact_range(None, None).wait().unwrap();
    let id2 = engine.create_backup(&db).unwrap();
    let shared_after_2 = shared_count(bkp_dir.path());

    // Remove the first backup - any file it held that backup 2
    // does not also reference should be gone.
    engine.delete_backup(id1).unwrap();
    let shared_after_delete = shared_count(bkp_dir.path());
    assert!(shared_after_delete <= shared_after_2);
    assert_eq!(engine.list_backups().len(), 1);

    // backup 2 still restores cleanly.
    let tgt_dir = TempDir::new().unwrap();
    engine.restore(id2, tgt_dir.path(), None).unwrap();
    drop(db);
    let reopened = Db::open(tgt_dir.path(), Options::default()).unwrap();
    assert_has(&reopened, "z", 200);
}

#[test]
fn delete_only_backup_removes_all_shared() {
    let src_dir = TempDir::new().unwrap();
    let bkp_dir = TempDir::new().unwrap();
    let db = Db::open(src_dir.path(), tiny_flush_opts()).unwrap();
    populate(&db, "q", 300);
    db.compact_range(None, None).wait().unwrap();

    let mut engine = BackupEngine::open(bkp_dir.path()).unwrap();
    let id = engine.create_backup(&db).unwrap();
    assert!(shared_count(bkp_dir.path()) > 0);

    engine.delete_backup(id).unwrap();
    assert_eq!(shared_count(bkp_dir.path()), 0);
    assert_eq!(engine.list_backups().len(), 0);
}

#[test]
fn purge_keeps_newest() {
    let src_dir = TempDir::new().unwrap();
    let bkp_dir = TempDir::new().unwrap();
    let db = Db::open(src_dir.path(), tiny_flush_opts()).unwrap();

    populate(&db, "g1", 100);
    db.compact_range(None, None).wait().unwrap();
    let mut engine = BackupEngine::open(bkp_dir.path()).unwrap();
    let _b1 = engine.create_backup(&db).unwrap();

    populate(&db, "g2", 100);
    db.compact_range(None, None).wait().unwrap();
    let _b2 = engine.create_backup(&db).unwrap();

    populate(&db, "g3", 100);
    db.compact_range(None, None).wait().unwrap();
    let b3 = engine.create_backup(&db).unwrap();

    engine.purge_old_backups(1).unwrap();
    let infos = engine.list_backups();
    assert_eq!(infos.len(), 1);
    assert_eq!(infos[0].id, b3);
}

#[test]
fn restore_independent_of_source() {
    let src_dir = TempDir::new().unwrap();
    let bkp_dir = TempDir::new().unwrap();
    let tgt_dir = TempDir::new().unwrap();

    let db = Db::open(src_dir.path(), tiny_flush_opts()).unwrap();
    populate(&db, "ind", 250);

    let mut engine = BackupEngine::open(bkp_dir.path()).unwrap();
    let id = engine.create_backup(&db).unwrap();

    db.close().unwrap();
    drop(db);
    fs::remove_dir_all(src_dir.path()).unwrap();

    engine.restore(id, tgt_dir.path(), None).unwrap();
    let reopened = Db::open(tgt_dir.path(), Options::default()).unwrap();
    assert_has(&reopened, "ind", 250);
}
