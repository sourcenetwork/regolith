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
