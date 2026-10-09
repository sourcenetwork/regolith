//! The tail judgment on manifests built byte by byte.

use std::path::Path;

use super::super::{ManifestRecord, VersionSet};
use super::{DroppedTail, batch_at, judge};

fn stamp() -> Vec<u8> {
    VersionSet::encode_stamp().to_vec()
}

/// A plain batch: the offset it lands at binds only a sealed one.
fn batch(records: &[ManifestRecord]) -> Vec<u8> {
    VersionSet::encode_records(records, 0, None).unwrap().0
}

/// A batch that only reserves a file id: never synced on its own.
fn reservation(id: u64) -> Vec<u8> {
    batch(&[ManifestRecord::SetNextFileId(id)])
}

/// A batch that needs a sync, as a flush's does.
fn synced(seq: u64) -> Vec<u8> {
    batch(&[
        ManifestRecord::SetLastSeq(seq),
        ManifestRecord::SetMinWalId(seq),
    ])
}

fn path() -> &'static Path {
    Path::new("/db/MANIFEST")
}

/// Every batch in `parts` after a stamp, and the offset each begins at.
fn manifest(parts: &[Vec<u8>]) -> (Vec<u8>, Vec<usize>) {
    let mut data = stamp();
    let mut starts = Vec::new();
    for part in parts {
        starts.push(data.len());
        data.extend_from_slice(part);
    }
    (data, starts)
}

/// Flip a byte of the payload of the batch beginning at `at`, so its
/// checksum fails while its length still reads.
fn damage_payload(data: &mut [u8], at: usize) {
    data[at + 4] ^= 0xFF;
}

#[test]
fn a_batch_reads_back_whole_only_where_its_checksum_holds() {
    let (data, starts) = manifest(&[synced(1), reservation(9)]);
    let first = batch_at(&data, starts[0]).expect("the first batch reads back");
    assert_eq!(first.end, starts[1]);
    assert_eq!(batch_at(&data, starts[1]).unwrap().end, data.len());
    assert!(batch_at(&data, starts[0] + 1).is_none());
    assert!(batch_at(&data, data.len()).is_none());
    assert!(batch_at(&data[..data.len() - 1], starts[1]).is_none());
}

#[test]
fn a_length_past_the_end_of_the_file_is_no_batch() {
    let mut data = stamp();
    data.extend_from_slice(&u32::MAX.to_le_bytes());
    data.extend_from_slice(&[0; 16]);
    assert!(batch_at(&data, 12).is_none());
}

#[test]
fn a_torn_last_batch_is_a_tail_to_drop() {
    let (data, starts) = manifest(&[synced(1), synced(2)]);
    let cut = &data[..data.len() - 3];
    assert_eq!(
        judge(cut, starts[1], path()).unwrap(),
        DroppedTail {
            offset: starts[1] as u64,
            bytes: (cut.len() - starts[1]) as u64,
        }
    );
}

#[test]
fn reservations_after_the_damage_prove_nothing() {
    let (mut data, starts) = manifest(&[reservation(2), reservation(3), reservation(4)]);
    damage_payload(&mut data, starts[0]);
    let tail = judge(&data, starts[0], path()).expect("only reservations follow the damage");
    assert_eq!(tail.offset, starts[0] as u64);
}

#[test]
fn a_synced_batch_written_last_proves_nothing() {
    // The batch whose sync was under way at the cut: whole, but nothing was
    // written after it, so nothing shows its sync completed.
    let (mut data, starts) = manifest(&[reservation(2), synced(1)]);
    damage_payload(&mut data, starts[0]);
    assert!(judge(&data, starts[0], path()).is_ok());
}

#[test]
fn a_synced_batch_with_bytes_after_it_proves_the_damage_durable() {
    let (mut data, starts) = manifest(&[synced(1), synced(2), reservation(9)]);
    damage_payload(&mut data, starts[0]);
    let err = judge(&data, starts[0], path()).expect_err("the damage lies below a proof");
    let message = err.to_string();
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
    assert!(message.contains("/db/MANIFEST"), "{message}");
    assert!(
        message.contains(&format!("offset {}", starts[0])),
        "{message}"
    );
    assert!(
        message.contains(&format!("offset {}", starts[2])),
        "{message}"
    );
}

#[test]
fn a_proof_is_found_past_a_damaged_length() {
    let (mut data, starts) = manifest(&[synced(1), synced(2), synced(3)]);
    data[starts[0]..starts[0] + 4].copy_from_slice(&0xDEAD_BEEFu32.to_le_bytes());
    let err = judge(&data, starts[0], path()).expect_err("the scan finds the later batches");
    assert!(err.to_string().contains(&format!("offset {}", starts[2])));
}

#[test]
fn a_tail_of_zeros_or_unrelated_bytes_is_dropped() {
    let (data, _) = manifest(&[synced(1)]);
    let end = data.len();
    for fill in [0u8, 0xAB] {
        let mut torn = data.clone();
        torn.extend(std::iter::repeat_n(fill, 4096));
        let tail = judge(&torn, end, path()).expect("a crash leaves such a tail");
        assert_eq!(tail.bytes, 4096);
    }
    let mut torn = data.clone();
    let mut x = 0x9E37_79B9_7F4A_7C15u64;
    for _ in 0..4096 {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        torn.push(x as u8);
    }
    assert!(judge(&torn, end, path()).is_ok());
}

#[test]
fn a_batch_this_build_cannot_decode_counts_as_needing_a_sync() {
    let mut unknown = vec![0u8; 4];
    unknown.extend_from_slice(&[0xEE; 9]);
    let len = (unknown.len() - 4) as u32;
    unknown[..4].copy_from_slice(&len.to_le_bytes());
    let check = crate::engine::checksum::manifest_record(len, &unknown[4..]);
    unknown.extend_from_slice(&check.to_le_bytes());

    let (mut data, starts) = manifest(&[synced(1), unknown, reservation(9)]);
    damage_payload(&mut data, starts[0]);
    assert!(judge(&data, starts[0], path()).is_err());
}

#[test]
fn every_record_but_reservations_and_retirements_needs_a_sync() {
    use crate::engine::sstable::SsTableMeta;
    let meta = SsTableMeta {
        file_id: 3,
        smallest_key: b"a".to_vec(),
        largest_key: b"b".to_vec(),
        file_size: 1,
        num_entries: 1,
        global_seq: None,
    };
    let needs = [
        ManifestRecord::AddFile { level: 0, meta },
        ManifestRecord::RemoveFile {
            level: 0,
            file_id: 3,
        },
        ManifestRecord::SetLastSeq(1),
        ManifestRecord::Reset {
            next_file_id: 2,
            min_wal_id: 1,
        },
    ];
    assert!(needs.iter().all(ManifestRecord::requires_sync));
    assert!(!ManifestRecord::SetNextFileId(1).requires_sync());
    assert!(!ManifestRecord::SetMinWalId(1).requires_sync());
}
