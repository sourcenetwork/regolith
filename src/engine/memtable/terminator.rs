//! The in-place walk commit validation uses to find where a key's merge
//! operands end. It reads sequences and value types straight from the skip
//! list nodes, so it slices no value and clones no arena `Arc`.

use super::{LookupKey, MemTable, VALUE_TYPE_MERGE, decode_internal_key};

impl MemTable {
    /// Skips `lk`'s merge operands above `floor`, newest first among the
    /// entries at or below the lookup's snapshot, and returns the sequence
    /// of the entry the skip stops at: a value or deletion above `floor`,
    /// or any entry at or below it. `None` when every such entry here is an
    /// operand above `floor`, or there is none.
    ///
    /// Reads sequences and value types in place: no value is sliced and no
    /// arena `Arc` is cloned.
    pub(crate) fn skip_merges_above(&self, lk: &LookupKey, floor: u64) -> Option<u64> {
        let snapshot_seq = lk.snapshot_seq();
        let mut node = self.list.seek_ge(lk.internal());
        while let Some(current) = node {
            let (user_key, seq, value_type) = decode_internal_key(current.key());
            if user_key != lk.prefixed_user_key() {
                return None;
            }
            if seq <= snapshot_seq && (seq <= floor || value_type != VALUE_TYPE_MERGE) {
                return Some(seq);
            }
            node = current.next();
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::memtable::MemTableConfig;
    use proptest::prelude::*;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Kind {
        Put,
        Delete,
        Merge,
    }

    /// An empty memtable on the default configuration.
    fn memtable() -> MemTable {
        MemTable::new(&MemTableConfig::default()).expect("memtable")
    }

    /// Record one write of `kind` to `key` at `seq`.
    fn write(mt: &MemTable, key: &[u8], seq: u64, kind: Kind) {
        match kind {
            Kind::Put => mt.put(key, b"v", seq),
            Kind::Delete => mt.delete(key, seq),
            Kind::Merge => mt.merge(key, b"op", seq),
        }
    }

    /// `skip_merges_above` for `key` read at `snapshot_seq`.
    fn skip(mt: &MemTable, key: &[u8], snapshot_seq: u64, floor: u64) -> Option<u64> {
        mt.skip_merges_above(&LookupKey::from_prefixed(key, snapshot_seq), floor)
    }

    #[test]
    fn the_skip_runs_down_to_the_base_when_the_floor_is_below_it() {
        let mt = memtable();
        write(&mt, b"k", 1, Kind::Put);
        write(&mt, b"k", 2, Kind::Merge);
        write(&mt, b"k", 3, Kind::Merge);
        assert_eq!(skip(&mt, b"k", u64::MAX, 0), Some(1));
    }

    #[test]
    fn the_skip_stops_at_the_first_entry_at_or_below_the_floor() {
        let mt = memtable();
        write(&mt, b"k", 1, Kind::Put);
        for seq in 2..=10 {
            write(&mt, b"k", seq, Kind::Merge);
        }
        assert_eq!(skip(&mt, b"k", u64::MAX, 5), Some(5));
        assert_eq!(skip(&mt, b"k", u64::MAX, 10), Some(10));
        assert_eq!(skip(&mt, b"k", u64::MAX, 40), Some(10));
    }

    #[test]
    fn a_deletion_above_the_floor_ends_the_skip() {
        let mt = memtable();
        write(&mt, b"k", 1, Kind::Put);
        write(&mt, b"k", 2, Kind::Merge);
        write(&mt, b"k", 3, Kind::Delete);
        write(&mt, b"k", 4, Kind::Merge);
        assert_eq!(skip(&mt, b"k", u64::MAX, 1), Some(3));
    }

    #[test]
    fn only_operands_above_the_floor_find_nothing() {
        let mt = memtable();
        write(&mt, b"k", 3, Kind::Merge);
        write(&mt, b"k", 4, Kind::Merge);
        assert_eq!(skip(&mt, b"k", u64::MAX, 2), None);
    }

    #[test]
    fn a_missing_key_finds_nothing() {
        let mt = memtable();
        assert_eq!(skip(&mt, b"k", u64::MAX, 0), None);
        write(&mt, b"j", 1, Kind::Put);
        assert_eq!(skip(&mt, b"k", u64::MAX, 0), None);
    }

    #[test]
    fn neighbouring_keys_never_leak_in() {
        let mt = memtable();
        write(&mt, b"j", 1, Kind::Put);
        write(&mt, b"k", 3, Kind::Merge);
        write(&mt, b"k", 4, Kind::Merge);
        write(&mt, b"ka", 5, Kind::Put);
        write(&mt, b"l", 6, Kind::Delete);
        assert_eq!(skip(&mt, b"k", u64::MAX, 2), None);
        assert_eq!(skip(&mt, b"k", u64::MAX, 0), None);
    }

    #[test]
    fn entries_above_the_lookup_snapshot_are_ignored() {
        let mt = memtable();
        write(&mt, b"k", 1, Kind::Put);
        write(&mt, b"k", 2, Kind::Merge);
        write(&mt, b"k", 9, Kind::Put);
        assert_eq!(skip(&mt, b"k", 5, 0), Some(1));
        assert_eq!(skip(&mt, b"k", u64::MAX, 0), Some(9));
    }

    const KEYS: [&[u8]; 3] = [b"a", b"ab", b"b"];

    /// Writes as `(key index, kind)` in sequence order from 1, a floor and
    /// a lookup snapshot, both drawn from just past the last sequence, the
    /// snapshot sometimes unbounded.
    fn scenario() -> impl Strategy<Value = (Vec<(usize, Kind)>, u64, u64)> {
        let kind = prop_oneof![Just(Kind::Put), Just(Kind::Delete), Just(Kind::Merge)];
        proptest::collection::vec((0..KEYS.len(), kind), 0..48).prop_flat_map(|writes| {
            let past_last = writes.len() as u64 + 1;
            (
                Just(writes),
                0..=past_last,
                prop_oneof![0..=past_last, Just(u64::MAX)],
            )
        })
    }

    proptest! {
        #[test]
        fn skip_merges_above_matches_a_linear_model(
            (writes, floor, snapshot_seq) in scenario(),
        ) {
            let mt = memtable();
            for (index, &(key, kind)) in writes.iter().enumerate() {
                write(&mt, KEYS[key], index as u64 + 1, kind);
            }
            for (key, name) in KEYS.iter().enumerate() {
                // Sequences rise with the index, so the reversed log is
                // the key's entries newest first.
                let expected = writes
                    .iter()
                    .enumerate()
                    .rev()
                    .map(|(index, &(k, kind))| (k, index as u64 + 1, kind))
                    .filter(|&(k, seq, _)| k == key && seq <= snapshot_seq)
                    .find(|&(_, seq, kind)| seq <= floor || kind != Kind::Merge)
                    .map(|(_, seq, _)| seq);
                prop_assert_eq!(skip(&mt, name, snapshot_seq, floor), expected);
            }
        }
    }
}
