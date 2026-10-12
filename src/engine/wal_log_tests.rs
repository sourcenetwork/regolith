//! A log written by position holds the same records, replays the same way
//! and refuses the same things as one written by appending.

use std::path::Path;
use std::sync::Arc;

use proptest::prelude::*;
use tempfile::TempDir;

use super::super::seal::{Keyring, test_keys};
use super::super::wal::{Wal, WalEntry, encode_put_record, fault};
use super::super::wal_frame::KIND_GROUP;
use super::super::wal_replay::{WalPosition, WalReplayIter};
use super::{Log, Place};
use crate::env::{Env, std_env};

/// The record of one put at `seq`, placed at `offset` of `log`, as the bytes
/// a writer hands to [`Log::write_record`].
fn put_record(log: &Log, offset: u64, key: &[u8], value: &[u8], seq: u64) -> (Place, Vec<u8>) {
    let mut buf = vec![0u8; log.prefix_len()];
    encode_put_record(&mut buf, key, value, seq);
    let place = log.place(offset, buf.len() - log.prefix_len()).unwrap();
    log.finish_record(KIND_GROUP, &place, &mut buf).unwrap();
    (place, buf)
}

fn replay(path: &Path, keyring: Option<&Keyring>) -> std::io::Result<Vec<WalEntry>> {
    let mut iter = WalReplayIter::open(&std_env(), path, WalPosition::Newest, keyring)?;
    let mut entries = Vec::new();
    while let Some(entry) = iter.next_entry()? {
        entries.push(entry);
    }
    Ok(entries)
}

fn put(key: &[u8], value: &[u8], seq: u64) -> WalEntry {
    WalEntry::Put {
        key: key.to_vec(),
        value: value.to_vec(),
        seq,
    }
}

#[test]
fn records_written_out_of_order_replay_in_offset_order() {
    let dir = TempDir::new().unwrap();
    let path = dir.path().join("wal_000001.log");
    let log = Log::create(&path).unwrap();
    let (first, a) = put_record(&log, log.stamp_len(), b"a", b"1", 1);
    let (second, b) = put_record(&log, first.end(), b"b", b"2", 2);
    let (third, c) = put_record(&log, second.end(), b"c", b"3", 3);
    assert!(log.write_record(&third, &c).unwrap());
    assert!(log.write_record(&first, &a).unwrap());
    assert!(log.write_record(&second, &b).unwrap());
    // A helper writing a record its owner already wrote changes nothing.
    assert!(log.write_record(&second, &b).unwrap());
    log.sync_through(third.end()).unwrap();
    assert_eq!(log.durable(), third.end());
    assert_eq!(
        replay(&path, None).unwrap(),
        vec![put(b"a", b"1", 1), put(b"b", b"2", 2), put(b"c", b"3", 3)]
    );
}

#[test]
fn a_record_is_stamped_with_what_a_sync_covered_and_never_more_than_its_offset() {
    let dir = TempDir::new().unwrap();
    let log = Log::create(&dir.path().join("wal_000001.log")).unwrap();
    let (first, a) = put_record(&log, log.stamp_len(), b"a", b"1", 1);
    assert_eq!(first.synced_through, 0, "nothing is durable before a sync");
    log.write_record(&first, &a).unwrap();
    log.sync_through(first.end()).unwrap();
    let (second, _) = put_record(&log, first.end(), b"b", b"2", 2);
    assert_eq!(second.synced_through, first.end());
    // Decided before the sync, written after it: it still claims only what
    // was durable when it was decided.
    assert_eq!(first.synced_through, 0);
}

#[test]
fn the_bytes_of_a_record_are_the_same_whoever_frames_it() {
    let dir = TempDir::new().unwrap();
    for keyring in [None, Some(test_keys::keyring(&[1]))] {
        let env = std_env();
        let path = dir.path().join(match keyring {
            None => "wal_000001.log",
            Some(_) => "wal_000002.log",
        });
        let log = Log::create_in(&env, &path, keyring.as_deref()).unwrap();
        let mut one = vec![0u8; log.prefix_len()];
        encode_put_record(&mut one, b"key", b"value", 9);
        let mut two = one.clone();
        let place = log
            .place(log.stamp_len(), one.len() - log.prefix_len())
            .unwrap();
        log.finish_record(KIND_GROUP, &place, &mut one).unwrap();
        log.finish_record(KIND_GROUP, &place, &mut two).unwrap();
        assert_eq!(one, two, "two helpers must write identical bytes");
        assert_eq!(one.len() as u64, place.len);
        log.write_record(&place, &one).unwrap();
        log.sync_through(place.end()).unwrap();
        assert_eq!(
            replay(&path, keyring.as_deref()).unwrap(),
            vec![put(b"key", b"value", 9)]
        );
    }
}

#[test]
fn a_sealed_record_holds_no_plaintext_and_opens_only_under_its_key() {
    let dir = TempDir::new().unwrap();
    let path = dir.path().join("wal_000001.log");
    let keyring = test_keys::keyring(&[1]);
    let log = Log::create_in(&std_env(), &path, Some(&keyring)).unwrap();
    assert_eq!(log.seal_key(), Some(crate::KeyId(1)));
    let (place, record) = put_record(&log, log.stamp_len(), b"secret-key", b"secret-value", 1);
    assert!(!record.windows(6).any(|w| w == b"secret"));
    log.write_record(&place, &record).unwrap();
    log.sync_through(place.end()).unwrap();
    assert_eq!(
        replay(&path, Some(&keyring)).unwrap(),
        vec![put(b"secret-key", b"secret-value", 1)]
    );
    assert!(replay(&path, Some(&test_keys::wrong_keyring(&[1]))).is_err());
}

#[test]
fn a_write_decided_before_a_rollback_is_not_made_after_it() {
    let dir = TempDir::new().unwrap();
    let path = dir.path().join("wal_000001.log");
    let log = Log::create(&path).unwrap();
    let (kept, a) = put_record(&log, log.stamp_len(), b"kept", b"1", 1);
    log.write_record(&kept, &a).unwrap();
    let (stale, b) = put_record(&log, kept.end(), b"stale", b"2", 2);
    log.poison(std::io::Error::other("the device said no"));
    assert!(log.is_poisoned());
    assert!(
        log.sync_through(kept.end()).is_err(),
        "a poisoned log is not vouched for"
    );
    let (cause, cut) = log.rollback_to(kept.end());
    cut.unwrap();
    assert!(cause.unwrap().to_string().contains("said no"));
    assert!(!log.is_poisoned());
    // The discarded commit's record, held by a thread that was slow.
    assert!(!log.write_record(&stale, &b).unwrap());
    // The offset is taken by the next commit.
    let (next, c) = put_record(&log, kept.end(), b"next", b"3", 2);
    assert!(log.write_record(&next, &c).unwrap());
    assert!(!log.write_record(&stale, &b).unwrap());
    log.sync_through(next.end()).unwrap();
    assert_eq!(
        replay(&path, None).unwrap(),
        vec![put(b"kept", b"1", 1), put(b"next", b"3", 2)]
    );
}

#[test]
fn a_failed_sync_does_not_move_the_durable_offset() {
    let dir = TempDir::new().unwrap();
    let path = dir.path().join("wal_000001.log");
    let log = Log::create(&path).unwrap();
    let (place, record) = put_record(&log, log.stamp_len(), b"k", b"v", 1);
    log.write_record(&place, &record).unwrap();
    fault::arm_sync_failure(dir.path());
    let failed = log.sync_through(place.end());
    fault::disarm_sync_failure(dir.path());
    assert!(failed.unwrap_err().to_string().contains("injected"));
    assert_eq!(log.durable(), 0);
}

#[test]
fn a_closed_log_replays_whole_and_is_vouched_for_by_close() {
    let dir = TempDir::new().unwrap();
    for keyring in [None, Some(test_keys::keyring(&[1]))] {
        let path = dir.path().join(match keyring {
            None => "wal_000001.log",
            Some(_) => "wal_000002.log",
        });
        let log = Log::create_in(&std_env(), &path, keyring.as_deref()).unwrap();
        let (place, record) = put_record(&log, log.stamp_len(), b"k", b"v", 1);
        log.write_record(&place, &record).unwrap();
        log.close(place.end()).unwrap();
        assert_eq!(
            replay(&path, keyring.as_deref()).unwrap(),
            vec![put(b"k", b"v", 1)]
        );
        // CLOSE proves the whole file durable: damage in it refuses the open
        // instead of being dropped as a tail.
        let mut bytes = std::fs::read(&path).unwrap();
        let at = place.offset as usize + 30;
        bytes[at] ^= 0xFF;
        std::fs::write(&path, bytes).unwrap();
        assert!(replay(&path, keyring.as_deref()).is_err());
    }
}

/// One step of a writer: which record it writes.
fn order(records: usize) -> impl Strategy<Value = Vec<usize>> {
    proptest::collection::vec(0..records, 0..records * 3)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// Whatever order the records are written in, and however often, the log
    /// replays exactly as one the same records were appended to.
    #[test]
    fn a_positional_log_replays_as_the_appended_one_does(
        puts in proptest::collection::vec(
            (proptest::collection::vec(any::<u8>(), 1..12), proptest::collection::vec(any::<u8>(), 0..48)),
            1..16,
        ),
        extra in order(16),
        sealed in any::<bool>(),
    ) {
        let dir = TempDir::new().unwrap();
        let env: Arc<dyn Env> = std_env();
        let keyring = sealed.then(|| test_keys::keyring(&[1]));

        let appended = dir.path().join("wal_000001.log");
        let mut wal = Wal::create_in(&env, &appended, keyring.as_deref()).unwrap();
        for (i, (key, value)) in puts.iter().enumerate() {
            wal.append_put(key, value, i as u64 + 1).unwrap();
        }
        wal.sync_data().unwrap();

        let positional = dir.path().join("wal_000002.log");
        let log = Log::create_in(&env, &positional, keyring.as_deref()).unwrap();
        let mut offset = log.stamp_len();
        let mut records = Vec::new();
        for (i, (key, value)) in puts.iter().enumerate() {
            let (place, bytes) = put_record(&log, offset, key, value, i as u64 + 1);
            offset = place.end();
            records.push((place, bytes));
        }
        for pick in extra {
            if let Some((place, bytes)) = records.get(pick) {
                log.write_record(place, bytes).unwrap();
            }
        }
        for (place, bytes) in records.iter().rev() {
            log.write_record(place, bytes).unwrap();
        }
        log.sync_through(offset).unwrap();

        prop_assert_eq!(
            replay(&positional, keyring.as_deref()).unwrap(),
            replay(&appended, keyring.as_deref()).unwrap()
        );
        prop_assert_eq!(
            std::fs::metadata(&positional).unwrap().len(),
            std::fs::metadata(&appended).unwrap().len(),
            "the two logs frame every record the same way"
        );
    }
}
