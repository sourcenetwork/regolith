//! Which tombstones a compaction pass drops from its outputs (E27).
//!
//! A tombstone deletes the versions older than it of the keys it covers: a
//! range tombstone every key of its range, a point deletion its own key.
//! Once a pass has nothing left for one to delete, carrying it on costs
//! every later pass over its keys and deletes nothing, and what a dropped
//! column family leaves (a range tombstone over the family's keys, a point
//! deletion of its name in the metadata family) would otherwise pile up for
//! the life of the database. A pass drops a tombstone, retires it, when both
//! hold:
//!
//! - the pass writes the deepest level holding a key it covers, so every
//!   version it covers is in the pass's inputs: an older version of a key is
//!   never above the tombstone that covers it in read order (LsmOrder.tla),
//!   and nothing below the output level holds those keys;
//! - no live snapshot is below its sequence, so each covered version shares
//!   its snapshot stripe and the pass drops it (`Stripes::shadowed` for a
//!   range tombstone, `Stripes::reduce_group` beneath a point deletion). A
//!   snapshot registered after the live list was read is at or above every
//!   sequence in the inputs (E5), the tombstone's included. A transaction's
//!   commit check reads from its own snapshot, which is registered, so it
//!   never misses a write it has to see.
//!
//! The pass still shadows with every range tombstone of its inputs; only the
//! outputs leave the retired ones out. A point deletion retires only as the
//! oldest entry of its key, with no merge operand on it. A pass writing L0
//! retires nothing: older L0 tables outside it may hold what a tombstone
//! covers. TombstoneRetirement.tla checks the rule (a point deletion is a
//! range tombstone over one key); its RED cases retire a tombstone a
//! snapshot still needs, or one above data it covers.

use std::sync::Arc;

use super::super::internal_key::{VALUE_TYPE_DELETION, VALUE_TYPE_MERGE, decode_internal_key};
use super::super::manifest::{Version, covering, overlapping};
use super::super::range_tombstone::RangeTombstoneSet;
use super::super::sstable::LiveSst;

/// What one pass may retire, fixed once its inputs are: the levels below
/// its output and the oldest live snapshot.
pub(super) struct Retirement<'v> {
    /// Every level below the output, deepest last; empty for a pass
    /// writing L0, which retires nothing.
    deeper: &'v [Vec<Arc<LiveSst>>],
    oldest_live: Option<u64>,
    retires: bool,
}

impl<'v> Retirement<'v> {
    /// A pass writing `target_level` over `version`, with `oldest_live` the
    /// oldest live snapshot, if any.
    pub(super) fn new(target_level: usize, version: &'v Version, oldest_live: Option<u64>) -> Self {
        Self {
            deeper: version.levels.get(target_level + 1..).unwrap_or(&[]),
            oldest_live,
            retires: target_level > 0,
        }
    }

    /// No live snapshot is below `seq`.
    fn clear_of_snapshots(&self, seq: u64) -> bool {
        self.oldest_live.is_none_or(|oldest| seq <= oldest)
    }

    /// The range tombstones of `merged` the pass writes out.
    pub(super) fn carried_tombstones(&self, merged: &RangeTombstoneSet) -> RangeTombstoneSet {
        if !self.retires || merged.is_empty() {
            return merged.clone();
        }
        let carried = merged
            .iter()
            .filter(|rt| {
                !self.clear_of_snapshots(rt.seq)
                    || self.deeper.iter().any(|files| {
                        // `overlapping` takes a closed range; a table starting
                        // at the tombstone's exclusive end holds none of it.
                        overlapping(files, &rt.start, &rt.end)
                            .iter()
                            .any(|file| file.meta.smallest_key < rt.end)
                    })
            })
            .cloned()
            .collect();
        RangeTombstoneSet::from_vec(carried)
    }

    /// Drop the point deletion that ends `reduced`, one key's versions
    /// newest first as the pass writes them, when it retires.
    pub(super) fn retire_deletion(&self, reduced: &mut Vec<(Vec<u8>, Vec<u8>)>) {
        if !self.retires {
            return;
        }
        let Some((last, _)) = reduced.last() else {
            return;
        };
        let (user_key, seq, value_type) = decode_internal_key(last);
        let on_an_operand = reduced
            .len()
            .checked_sub(2)
            .is_some_and(|i| decode_internal_key(&reduced[i].0).2 == VALUE_TYPE_MERGE);
        if value_type == VALUE_TYPE_DELETION
            && !on_an_operand
            && self.clear_of_snapshots(seq)
            && self
                .deeper
                .iter()
                .all(|files| covering(files, user_key).is_empty())
        {
            reduced.pop();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::internal_key::{VALUE_TYPE_VALUE, encode_internal_key};
    use crate::engine::manifest::MAX_LEVELS;
    use crate::engine::range_tombstone::RangeTombstone;
    use crate::engine::sstable::{LiveSst, SsTableMeta, SsTableReader, SsTableWriter};
    use crate::options::CompressionType;
    use std::sync::Arc;
    use tempfile::TempDir;

    /// A table holding `smallest` and `largest`.
    fn table(dir: &TempDir, smallest: &[u8], largest: &[u8]) -> Arc<LiveSst> {
        let path = dir.path().join("table.sst");
        let mut writer =
            SsTableWriter::new(&path, 4096, 10, CompressionType::None, None, false, 4096).unwrap();
        for key in [smallest, largest] {
            writer
                .add(&encode_internal_key(key, 1, VALUE_TYPE_VALUE), b"v")
                .unwrap();
        }
        writer.finish().unwrap().unwrap();
        LiveSst::new(
            SsTableMeta {
                file_id: 1,
                smallest_key: smallest.to_vec(),
                largest_key: largest.to_vec(),
                file_size: 1,
                num_entries: 2,
                global_seq: None,
            },
            Arc::new(SsTableReader::open(&path, 1).unwrap()),
        )
    }

    fn set(tombstones: &[(&[u8], &[u8], u64)]) -> RangeTombstoneSet {
        RangeTombstoneSet::from_vec(
            tombstones
                .iter()
                .map(|(start, end, seq)| RangeTombstone::new(start.to_vec(), end.to_vec(), *seq))
                .collect(),
        )
    }

    fn kept(carried: &RangeTombstoneSet) -> Vec<(Vec<u8>, u64)> {
        carried
            .iter()
            .map(|rt| (rt.start.clone(), rt.seq))
            .collect()
    }

    #[test]
    fn a_tombstone_retires_only_below_its_range_and_every_snapshot_under_it() {
        let dir = TempDir::new().unwrap();
        let mut version = Version::new();
        // L6 holds [m, p]; the pass writes L5.
        version.levels[MAX_LEVELS - 1].push(table(&dir, b"m", b"p"));
        let merged = set(&[(b"a", b"c", 10), (b"n", b"o", 10), (b"q", b"r", 20)]);

        let none = Retirement::new(MAX_LEVELS - 2, &version, None).carried_tombstones(&merged);
        assert_eq!(
            kept(&none),
            vec![(b"n".to_vec(), 10)],
            "only the tombstone above data it covers stays"
        );

        let snapshot =
            Retirement::new(MAX_LEVELS - 2, &version, Some(15)).carried_tombstones(&merged);
        assert_eq!(
            kept(&snapshot),
            vec![(b"n".to_vec(), 10), (b"q".to_vec(), 20)],
            "a snapshot below a tombstone holds it"
        );

        // A table starting at a tombstone's exclusive end holds none of it.
        let touching = set(&[(b"k", b"m", 10)]);
        assert!(
            Retirement::new(MAX_LEVELS - 2, &version, None)
                .carried_tombstones(&touching)
                .is_empty()
        );

        // The bottom level has nothing below it; L0 retires nothing.
        assert!(
            Retirement::new(MAX_LEVELS - 1, &version, None)
                .carried_tombstones(&merged)
                .is_empty()
        );
        assert_eq!(
            Retirement::new(0, &version, None)
                .carried_tombstones(&merged)
                .iter()
                .count(),
            3
        );
    }

    #[test]
    fn a_point_deletion_retires_only_as_its_keys_oldest_entry_below_it_and_every_snapshot() {
        use crate::engine::internal_key::{VALUE_TYPE_DELETION, VALUE_TYPE_MERGE};

        let dir = TempDir::new().unwrap();
        let mut version = Version::new();
        version.levels[MAX_LEVELS - 1].push(table(&dir, b"m", b"p"));
        let entry =
            |key: &[u8], seq, value_type| (encode_internal_key(key, seq, value_type), Vec::new());
        let after = |level, oldest, mut reduced: Vec<(Vec<u8>, Vec<u8>)>| {
            Retirement::new(level, &version, oldest).retire_deletion(&mut reduced);
            reduced.len()
        };
        let pass = MAX_LEVELS - 2;

        assert_eq!(
            after(pass, None, vec![entry(b"a", 10, VALUE_TYPE_DELETION)]),
            0
        );
        assert_eq!(
            after(pass, None, vec![entry(b"n", 10, VALUE_TYPE_DELETION)]),
            1,
            "a deeper table holds the key"
        );
        assert_eq!(
            after(pass, Some(5), vec![entry(b"a", 10, VALUE_TYPE_DELETION)]),
            1,
            "a snapshot is below the deletion"
        );
        assert_eq!(
            after(
                pass,
                Some(10),
                vec![
                    entry(b"a", 11, VALUE_TYPE_VALUE),
                    entry(b"a", 10, VALUE_TYPE_DELETION)
                ]
            ),
            1,
            "a snapshot at the deletion reads the key as absent either way"
        );
        assert_eq!(
            after(
                pass,
                None,
                vec![
                    entry(b"a", 11, VALUE_TYPE_MERGE),
                    entry(b"a", 10, VALUE_TYPE_DELETION)
                ]
            ),
            2,
            "a merge operand rests on it"
        );
        assert_eq!(
            after(pass, None, vec![entry(b"a", 10, VALUE_TYPE_VALUE)]),
            1,
            "only a deletion retires"
        );
        assert_eq!(
            after(0, None, vec![entry(b"a", 10, VALUE_TYPE_DELETION)]),
            1
        );
    }
}
