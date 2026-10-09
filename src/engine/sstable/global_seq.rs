//! An ingested table, read at the one sequence its manifest record carries.
//!
//! An ingest installs an external table as it is, copied or linked, and
//! records in the manifest the sequence it drew for it (D48). The file's own
//! entries keep whatever sequence they were written with (`SstFileWriter`
//! writes 0); every read sees the recorded one instead. Three seams carry
//! that, so no read path has to know:
//!
//! - a data block is rebuilt with the recorded sequence when it is decoded,
//!   before the block cache holds it, so every walk, iterator, validation and
//!   compaction input reads the recorded sequence;
//! - an index seek, whose keys are the file's own last keys, is steered by
//!   the target's user key and by whether the recorded sequence is visible to
//!   it, never by the stored sequences;
//! - the range tombstones, held in memory, are rewritten when the reader is
//!   bound to the sequence.
//!
//! The rewrite needs the file to hold at most one entry per user key, which
//! the ingest checks: two entries of one key at one sequence have no order.
//! A compaction reads the file through these seams and writes what it reads,
//! so its output carries the sequence in its entries and no record of its own.

use super::super::block::{Block, BlockBuilder, RESTART_INTERVAL, decode_entry_at};
use super::super::internal_key::{INTERNAL_KEY_SUFFIX_LEN, decode_internal_key};
use super::super::range_tombstone::RangeTombstone;

/// The trailer that sorts before every entry of a user key.
const BEFORE_KEY: [u8; INTERNAL_KEY_SUFFIX_LEN] = [0; INTERNAL_KEY_SUFFIX_LEN];

/// The trailer that sorts after every entry of a user key.
const AFTER_KEY: [u8; INTERNAL_KEY_SUFFIX_LEN] = [0xFF; INTERNAL_KEY_SUFFIX_LEN];

/// Where an index seek for `target` lands in a table read at `seq`, as a
/// user key and the trailer to seek it with. `None` when `target` is too
/// short to be an internal key, which only the unit tests' raw blocks are.
///
/// Every entry of the target's user key reads as `(user_key, seq)`. With
/// `seq` at or below the target's sequence the seek goes to the key's first
/// entry, which is then at or after the target (at equal sequences the value
/// type decides, and the block walk that follows compares each entry in
/// full). With `seq` above it, every entry of the key reads as newer than the
/// target, so the seek goes past them all. The stored sequences never enter
/// into it, which is what keeps a file written at sequences above `seq` from
/// steering the seek into the wrong block.
pub(super) fn steer(target: &[u8], seq: u64) -> Option<(&[u8], [u8; INTERNAL_KEY_SUFFIX_LEN])> {
    if target.len() < INTERNAL_KEY_SUFFIX_LEN {
        return None;
    }
    let (user_key, target_seq, _) = decode_internal_key(target);
    Some((
        user_key,
        if seq <= target_seq {
            BEFORE_KEY
        } else {
            AFTER_KEY
        },
    ))
}

/// `block` with every entry's sequence replaced by `seq`, value types and
/// values unchanged.
///
/// The block was validated when it was decoded, so every key is at least an
/// internal-key trailer long. Prefix compression is rebuilt rather than
/// patched: a key's trailer can be part of the prefix the next key shares.
pub(super) fn rebuild(block: &Block, seq: u64) -> Block {
    let stamp = (!seq).to_be_bytes();
    let data = block.entry_data();
    let mut builder = BlockBuilder::new(RESTART_INTERVAL);
    let mut stored = Vec::new();
    let mut read_as = Vec::new();
    let mut pos = 0;
    while pos < data.len() {
        let (consumed, value_offset, value_len) = decode_entry_at(data, pos, &mut stored);
        pos += consumed;
        let user_end = stored.len() - INTERNAL_KEY_SUFFIX_LEN;
        read_as.clear();
        read_as.extend_from_slice(&stored[..user_end]);
        read_as.extend_from_slice(&stamp);
        read_as.push(stored[stored.len() - 1]);
        builder.add(&read_as, &data[value_offset..value_offset + value_len]);
    }
    Block::from_builder(builder)
}

/// `tombstones` with every sequence replaced by `seq`.
pub(super) fn tombstones_at(tombstones: &[RangeTombstone], seq: u64) -> Vec<RangeTombstone> {
    tombstones
        .iter()
        .map(|rt| RangeTombstone::new(rt.start.clone(), rt.end.clone(), seq))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::internal_key::{
        VALUE_TYPE_DELETION, VALUE_TYPE_MERGE, VALUE_TYPE_VALUE, compare_internal_keys,
        compare_internal_split, encode_internal_key,
    };
    use proptest::prelude::*;

    fn block_of(entries: &[(Vec<u8>, Vec<u8>)]) -> Block {
        let mut builder = BlockBuilder::new(RESTART_INTERVAL);
        for (key, value) in entries {
            builder.add(key, value);
        }
        Block::decode_data_block(builder.finish()).unwrap()
    }

    fn entries_of(block: &Block) -> Vec<(Vec<u8>, Vec<u8>)> {
        let data = block.entry_data();
        let mut key = Vec::new();
        let mut out = Vec::new();
        let mut pos = 0;
        while pos < data.len() {
            let (consumed, off, len) = decode_entry_at(data, pos, &mut key);
            pos += consumed;
            out.push((key.clone(), data[off..off + len].to_vec()));
        }
        out
    }

    #[test]
    fn a_rebuilt_block_reads_every_entry_at_the_sequence_and_keeps_the_rest() {
        // `ab` is a prefix of `ab\xff...`: the second key shares bytes of the
        // first one's trailer, so a patch in place would corrupt it.
        let stored = vec![
            (
                encode_internal_key(b"ab", 0, VALUE_TYPE_VALUE),
                b"1".to_vec(),
            ),
            (
                encode_internal_key(b"ab\xff\xff", 0, VALUE_TYPE_DELETION),
                Vec::new(),
            ),
            (
                encode_internal_key(b"b", 900, VALUE_TYPE_MERGE),
                b"3".to_vec(),
            ),
        ];
        let rebuilt = entries_of(&rebuild(&block_of(&stored), 42));
        let expected: Vec<_> = stored
            .iter()
            .map(|(key, value)| {
                let (user_key, _, value_type) = decode_internal_key(key);
                (encode_internal_key(user_key, 42, value_type), value.clone())
            })
            .collect();
        assert_eq!(rebuilt, expected);
    }

    #[test]
    fn a_rebuilt_block_answers_a_seek_like_a_block_written_at_the_sequence() {
        let keys: Vec<Vec<u8>> = (0..40u32)
            .map(|i| format!("k{i:03}").into_bytes())
            .collect();
        let stored: Vec<_> = keys
            .iter()
            .map(|k| (encode_internal_key(k, 0, VALUE_TYPE_VALUE), k.clone()))
            .collect();
        let written: Vec<_> = keys
            .iter()
            .map(|k| (encode_internal_key(k, 7, VALUE_TYPE_VALUE), k.clone()))
            .collect();
        let rebuilt = rebuild(&block_of(&stored), 7);
        let reference = block_of(&written);
        assert_eq!(rebuilt.restart_count(), reference.restart_count());
        for k in &keys {
            for snapshot in [6, 7, 8] {
                let target = encode_internal_key(k, snapshot, VALUE_TYPE_DELETION);
                let first = |block: &Block| {
                    let mut buf = Vec::new();
                    block.scan_from(&target, &mut buf, |key, _, _| {
                        std::ops::ControlFlow::Break(key.to_vec())
                    })
                };
                assert_eq!(first(&rebuilt), first(&reference));
            }
        }
    }

    #[test]
    fn a_bound_reader_answers_every_lookup_at_the_recorded_sequence() {
        use crate::engine::block_cache::BlockCache;
        use crate::engine::lookup_key::LookupKey;
        use crate::engine::sstable::{LookupResult, SsTableReader, SsTableWriter};
        use crate::options::CompressionType;

        let dir = tempfile::TempDir::new().unwrap();
        let path = dir.path().join("bound.sst");
        let mut writer =
            SsTableWriter::new(&path, 64, 10, CompressionType::None, None, true, 64).unwrap();
        let keys: Vec<Vec<u8>> = (0..30u32)
            .map(|i| format!("k{i:02}").into_bytes())
            .collect();
        for (i, key) in keys.iter().enumerate() {
            let value_type = if i == 3 {
                VALUE_TYPE_DELETION
            } else {
                VALUE_TYPE_VALUE
            };
            writer
                .add(
                    &encode_internal_key(key, 1_000 + i as u64, value_type),
                    b"v",
                )
                .unwrap();
        }
        writer.add_range_tombstone(b"x", b"z", 2_000);
        writer.finish().unwrap().unwrap();
        let reader = SsTableReader::open(&path, 1)
            .unwrap()
            .with_global_seq(Some(50));
        let cache = BlockCache::new(1 << 20);
        let mut buf = Vec::new();

        for (i, key) in keys.iter().enumerate() {
            let mut at =
                |snapshot| reader.get(&LookupKey::from_prefixed(key, snapshot), &mut buf, &cache);
            assert_eq!(at(49).unwrap(), LookupResult::NotInTable);
            for snapshot in [50, u64::MAX] {
                match at(snapshot).unwrap() {
                    LookupResult::FoundTombstone { seq } => assert!(i == 3 && seq == 50),
                    LookupResult::Found { seq, .. } => assert!(i != 3 && seq == 50),
                    LookupResult::NotInTable => panic!("k{i:02} missing at {snapshot}"),
                }
            }
            let newest = reader
                .latest_version(&LookupKey::from_prefixed(key, u64::MAX), &mut buf, &cache)
                .unwrap();
            assert_eq!(newest.map(|(seq, _)| seq), Some(50));
        }
        assert_eq!(reader.covering_range_tombstone_seq(b"y", 49), 0);
        assert_eq!(reader.covering_range_tombstone_seq(b"y", 50), 50);
        for (ik, _) in reader.iter_internal(&cache).unwrap() {
            assert_eq!(decode_internal_key(&ik).1, 50);
        }
    }

    #[test]
    fn tombstones_take_the_sequence() {
        let rewritten = tombstones_at(&[RangeTombstone::new(b"a".to_vec(), b"c".to_vec(), 3)], 9);
        assert_eq!(rewritten.len(), 1);
        assert_eq!(
            (
                rewritten[0].start.as_slice(),
                rewritten[0].end.as_slice(),
                rewritten[0].seq
            ),
            (&b"a"[..], &b"c"[..], 9)
        );
    }

    proptest! {
        /// The steered seek and a seek on the file as if it were written at
        /// `seq` agree on every stored key: an index key, which is a stored
        /// key, sorts below the steered target exactly when the same key
        /// written at `seq` sorts below the real target, whatever sequence it
        /// was stored at. That is the whole contract an index seek needs.
        #[test]
        fn a_steered_seek_orders_every_stored_key_as_if_written_at_the_sequence(
            stored_key in proptest::collection::vec(0u8..4, 0..4),
            stored_seq in any::<u64>(),
            target_key in proptest::collection::vec(0u8..4, 0..4),
            target_seq in any::<u64>(),
            seq in 1u64..u64::MAX,
            value_type in prop_oneof![
                Just(VALUE_TYPE_DELETION), Just(VALUE_TYPE_VALUE), Just(VALUE_TYPE_MERGE)
            ],
        ) {
            prop_assume!(seq != target_seq);
            let stored = encode_internal_key(&stored_key, stored_seq, value_type);
            let read_as = encode_internal_key(&stored_key, seq, value_type);
            let target = encode_internal_key(&target_key, target_seq, VALUE_TYPE_DELETION);
            let (user_key, trailer) = steer(&target, seq).unwrap();
            prop_assert_eq!(
                compare_internal_split(&stored, user_key, &trailer).is_lt(),
                compare_internal_keys(&read_as, &target).is_lt()
            );
        }
    }

    #[test]
    fn at_an_equal_sequence_the_seek_starts_at_the_key() {
        let target = encode_internal_key(b"k", 5, VALUE_TYPE_VALUE);
        let (user_key, trailer) = steer(&target, 5).unwrap();
        for stored_seq in [0, 5, u64::MAX] {
            let stored = encode_internal_key(b"k", stored_seq, VALUE_TYPE_DELETION);
            assert!(
                !compare_internal_split(&stored, user_key, &trailer).is_lt(),
                "every entry of the key sorts at or after the steered target"
            );
        }
        assert!(steer(b"short", 5).is_none());
    }
}
