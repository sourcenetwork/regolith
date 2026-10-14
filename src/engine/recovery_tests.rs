#![cfg(not(target_arch = "wasm32"))]

mod recording_env;

use std::sync::Arc;

use recording_env::{Recording, RecordingEnv};

use super::{MemTable, Wal, WalEntry, rewrite_recovered_memtable_to_wal};

#[test]
fn recovery_groups_preserve_versions_and_all_record_types() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("recovered.wal");
    let memtable = MemTable::new(&Default::default()).unwrap();
    let mut expected = Vec::new();
    for seq in 1..=100u64 {
        let key = seq.to_be_bytes().to_vec();
        let value = vec![seq as u8; if seq == 50 { 128 * 1024 } else { 2048 }];
        memtable.put(&key, &value, seq);
        expected.push(WalEntry::Put { key, value, seq });
    }
    memtable.put(b"versioned", b"old", 101);
    memtable.put(b"versioned", b"new", 102);
    expected.push(WalEntry::Put {
        key: b"versioned".to_vec(),
        value: b"old".to_vec(),
        seq: 101,
    });
    expected.push(WalEntry::Put {
        key: b"versioned".to_vec(),
        value: b"new".to_vec(),
        seq: 102,
    });
    memtable.delete(b"deleted", 103);
    expected.push(WalEntry::Delete {
        key: b"deleted".to_vec(),
        seq: 103,
    });
    memtable.merge(b"merged", b"operand", 104);
    expected.push(WalEntry::Merge {
        key: b"merged".to_vec(),
        operand: b"operand".to_vec(),
        seq: 104,
    });
    memtable.delete_range(b"start", b"stop", 105);
    expected.push(WalEntry::DeleteRange {
        start: b"start".to_vec(),
        end: b"stop".to_vec(),
        seq: 105,
    });
    let mut wal = Wal::create(&path).unwrap();
    rewrite_recovered_memtable_to_wal(&memtable, &mut wal).unwrap();
    drop(wal);
    let actual = Wal::replay(&path).unwrap();
    assert_eq!(actual.len(), expected.len());
    for record in expected {
        assert!(actual.contains(&record), "missing recovered record");
    }
}

#[test]
fn recovery_sync_failure_keeps_original_logs_for_retry() {
    let dir = tempfile::tempdir().unwrap();
    let wal_dir = dir.path().join("wal");
    let db = crate::Db::open(dir.path(), crate::Options::default()).unwrap();
    for seq in 1..=100u64 {
        db.put(&seq.to_be_bytes(), &[42; 2048]).unwrap();
    }
    drop(db);
    let originals: Vec<_> = std::fs::read_dir(&wal_dir)
        .unwrap()
        .map(|entry| {
            let path = entry.unwrap().path();
            let bytes = std::fs::read(&path).unwrap();
            (path, bytes)
        })
        .collect();
    assert!(!originals.is_empty());
    super::wal::fault::arm_sync_failure(dir.path());
    let result = crate::Db::open(dir.path(), crate::Options::default());
    super::wal::fault::disarm_sync_failure(dir.path());
    assert!(result.is_err(), "recovery must propagate the sync failure");
    for (path, bytes) in originals {
        assert_eq!(std::fs::read(path).unwrap(), bytes);
    }
    let db = crate::Db::open(dir.path(), crate::Options::default()).unwrap();
    for seq in 1..=100u64 {
        assert_eq!(
            db.get(&seq.to_be_bytes()).unwrap().unwrap().as_slice(),
            &[42; 2048]
        );
    }
}

fn framed_put(memtable: &MemTable, key: &[u8], seq: u64, size: usize) -> Vec<u8> {
    let value = vec![seq as u8; size - super::wal::put_record_len(key, &[])];
    memtable.put(key, &value, seq);
    let mut record = Vec::new();
    super::wal::encode_put_record(&mut record, key, &value, seq);
    assert_eq!(record.len(), size);
    record
}

fn recording_wal(path: &std::path::Path) -> (Wal, Arc<RecordingEnv>) {
    let recording = Arc::new(RecordingEnv::default());
    let env: Arc<dyn crate::env::Env> = recording.clone();
    let wal = Wal::create_in(&env, path).unwrap();
    *recording.events.lock().unwrap() = Recording::default();
    (wal, recording)
}

#[test]
fn recovery_groups_bound_writes_and_keep_large_records_separate() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("recovered.wal");
    let memtable = MemTable::new(&Default::default()).unwrap();
    let sizes = [
        16_384, 16_384, 32_768, 16_384, 49_153, 131_072, 32_768, 32_768,
    ];
    let records: Vec<_> = sizes
        .into_iter()
        .enumerate()
        .map(|(index, size)| framed_put(&memtable, &[index as u8], index as u64 + 1, size))
        .collect();
    let (mut wal, recording) = recording_wal(&path);
    rewrite_recovered_memtable_to_wal(&memtable, &mut wal).unwrap();
    let expected = vec![
        records[..3].concat(),
        records[3].clone(),
        records[4].clone(),
        records[5].clone(),
        records[6..].concat(),
    ];
    let events = recording.events.lock().unwrap();
    assert_eq!(events.writes, expected);
    assert_eq!(events.data_syncs, 1);
    assert_eq!(Wal::replay(&path).unwrap().len(), records.len());
}

#[test]
fn recovery_packs_small_records_into_four_host_writes() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("recovered.wal");
    let memtable = MemTable::new(&Default::default()).unwrap();
    let records: Vec<_> = (1..=256u64)
        .map(|seq| framed_put(&memtable, &seq.to_be_bytes(), seq, 1024))
        .collect();
    let (mut wal, recording) = recording_wal(&path);
    rewrite_recovered_memtable_to_wal(&memtable, &mut wal).unwrap();
    let events = recording.events.lock().unwrap();
    assert_eq!(events.writes.len(), 4);
    assert!(events.writes.iter().all(|write| write.len() == 64 * 1024));
    assert_eq!(events.writes.concat(), records.concat());
    assert_eq!(events.data_syncs, 1);
}

#[test]
fn empty_recovery_does_not_append_or_sync() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("recovered.wal");
    let memtable = MemTable::new(&Default::default()).unwrap();
    let (mut wal, recording) = recording_wal(&path);
    rewrite_recovered_memtable_to_wal(&memtable, &mut wal).unwrap();
    let events = recording.events.lock().unwrap();
    assert!(events.writes.is_empty());
    assert_eq!(events.data_syncs, 0);
}

#[test]
fn partial_recovery_write_keeps_original_logs_for_retry() {
    let dir = tempfile::tempdir().unwrap();
    let wal_dir = dir.path().join("wal");
    let recording = Arc::new(RecordingEnv::default());
    let options = crate::Options::default()
        .env(recording.clone())
        .max_background_compactions(0);
    let db = crate::Db::open(dir.path(), options.clone()).unwrap();
    for seq in 1..=100u64 {
        db.put(&seq.to_be_bytes(), &[42; 2048]).unwrap();
    }
    drop(db);
    let originals: Vec<_> = std::fs::read_dir(&wal_dir)
        .unwrap()
        .map(|entry| {
            let path = entry.unwrap().path();
            let bytes = std::fs::read(&path).unwrap();
            (path, bytes)
        })
        .collect();
    assert!(!originals.is_empty());
    *recording.events.lock().unwrap() = Recording {
        // The stamp and first data group succeed before the partial write.
        fail_on_write: Some(3),
        ..Default::default()
    };
    let result = crate::Db::open(dir.path(), options.clone());
    assert!(result.is_err(), "recovery must propagate the write failure");
    for (path, bytes) in &originals {
        assert_eq!(&std::fs::read(path).unwrap(), bytes);
    }
    let events = recording.events.lock().unwrap();
    assert_eq!(events.partial_failures, 1);
    assert_eq!(events.writes.len(), 3);
    assert_eq!(events.data_syncs, 0);
    let replacement_len = events.writes[0].len() + events.writes[1].len() + 7;
    drop(events);
    let replacements: Vec<_> = std::fs::read_dir(&wal_dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| !originals.iter().any(|(original, _)| original == path))
        .collect();
    assert_eq!(replacements.len(), 1);
    assert_eq!(
        std::fs::metadata(&replacements[0]).unwrap().len(),
        replacement_len as u64
    );
    let db = crate::Db::open(dir.path(), options).unwrap();
    for seq in 1..=100u64 {
        assert_eq!(
            db.get(&seq.to_be_bytes()).unwrap().unwrap().as_slice(),
            &[42; 2048]
        );
    }
    db.put(b"after-retry", b"ok").unwrap();
    assert_eq!(db.get(b"after-retry").unwrap().unwrap().as_slice(), b"ok");
}
