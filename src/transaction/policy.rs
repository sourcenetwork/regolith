//! Caller-declared key classes that [`IsolationLevel::DefraLevel`] applies.
//!
//! regolith knows nothing about what a caller's keys mean. A caller whose
//! keyspace makes some conflicts harmless says so through a
//! [`KeyClassifier`], and the level relaxes validation for those keys on the
//! caller's word: a scan inside a commutative prefix is not validated as a
//! read, and a content-addressed key is not validated at all. Anything else
//! is validated as at [`IsolationLevel::RepeatableRead`]. The classifier does
//! not govern blind merges, which commute at this level for every key.

use std::collections::BTreeMap;

use crate::engine::ValidationSet;
use crate::transaction::IsolationLevel;

use super::scan_range::ScanRun;

/// Length of the column-family prefix on the keys a transaction buffers.
const CF_PREFIX_LEN: usize = 4;

/// What a caller declares about one key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KeyClass {
    /// No declaration: a scan over the key is recorded as at
    /// [`IsolationLevel::RepeatableRead`], and a read or write of it is
    /// validated as there.
    Ordinary,
    /// The key lies in a prefix the caller declares commutative. `len` is
    /// the prefix length: every key that starts with this key's first
    /// `len` bytes is in the same class.
    ///
    /// This class has an effect only for an optimistic transaction at
    /// [`IsolationLevel::DefraLevel`]. There, the commit disregards a scan
    /// stretch that stays inside one such prefix. The keys that scan
    /// returned are not validated as reads, as for any scan at
    /// [`IsolationLevel::RepeatableRead`]. A write or merge the transaction
    /// makes inside that stretch is validated as a blind write instead of
    /// as a read: an identical rewrite of a key's current value commits,
    /// and a merge there is blind. A write still conflicts with a newer
    /// commit to its key, a removal included, unless the key already holds
    /// exactly what the write would store. A stretch that leaves the prefix
    /// is recorded as at `RepeatableRead`.
    ///
    /// Declare a prefix commutative only when nothing the transaction
    /// writes outside it depends on which keys of the prefix the scan
    /// returned, and its writes inside it are unique keys or identical
    /// rewrites. A transaction that writes something elsewhere only when a
    /// prefix scan finds a key absent breaks the first condition: two such
    /// transactions can both commit where a serial order would let only one
    /// act.
    CommutativePrefix {
        /// Length of the shared prefix, in bytes of the caller's key.
        len: usize,
    },
    /// The key determines its bytes, as a content hash does: whoever writes
    /// the key writes the same value.
    ///
    /// This class has an effect only for an optimistic transaction at
    /// [`IsolationLevel::DefraLevel`] with a [`KeyClassifier`] installed.
    /// There, no read or write of such a key is ever validated. A `get`, a
    /// `get_for_update` or a scan that returns it records no read of it, and
    /// a put, delete or merge of it is never checked against newer writes, so
    /// two transactions that touch the same such key both commit. Other
    /// levels, and transactions without a classifier, are unchanged.
    ///
    /// The caller's contract is that the bytes under the key never differ.
    /// regolith cannot check it: a transaction that writes other bytes under
    /// the key commits as well, and the last commit to land decides what the
    /// key holds.
    ContentAddressed,
}

/// Classifies keys for [`IsolationLevel::DefraLevel`].
///
/// `classify` sees the key as the caller wrote it, without regolith's
/// column-family prefix, and must be pure, deterministic and cheap: commit
/// calls it while holding the transaction, once per scan stretch and once for
/// each key the transaction reads, writes or merges.
pub trait KeyClassifier: Send + Sync {
    /// The class `key` belongs to.
    fn classify(&self, key: &[u8]) -> KeyClass;
}

/// Whether `run` stays inside one commutative prefix of one column family.
/// A run that was never closed reaches the end of the keyspace, so it never
/// does.
pub(super) fn run_is_commutative(classifier: &dyn KeyClassifier, run: &ScanRun) -> bool {
    let (first, Some(last)) = run.bounds() else {
        return false;
    };
    if first.len() < CF_PREFIX_LEN
        || last.len() < CF_PREFIX_LEN
        || first[..CF_PREFIX_LEN] != last[..CF_PREFIX_LEN]
    {
        return false;
    }
    let (first, last) = (&first[CF_PREFIX_LEN..], &last[CF_PREFIX_LEN..]);
    match classifier.classify(first) {
        KeyClass::CommutativePrefix { len } => {
            first.len() >= len && last.len() >= len && first[..len] == last[..len]
        }
        KeyClass::Ordinary | KeyClass::ContentAddressed => false,
    }
}

/// What `classifier` says about `key`, which carries the column-family
/// prefix. A key too short to carry it is ordinary.
fn class_of(classifier: &dyn KeyClassifier, key: &[u8]) -> KeyClass {
    key.get(CF_PREFIX_LEN..)
        .map_or(KeyClass::Ordinary, |key| classifier.classify(key))
}

/// Take the content-addressed keys out of `checks`, which holds the commit's
/// reads once the transaction's scans are folded in: drop their reads, and
/// list the ones the commit writes or merges in `checks.exempt`, so the engine
/// validates none of them.
///
/// The listing is a sorted copy of those keys, built here before the commit
/// takes the write pipeline. The engine finds a written key in it by binary
/// search, which neither hashes nor allocates, and skips the key's lookup
/// outright, where a lookup is what validating it would cost. A commit whose
/// classifier names no written key leaves the list empty and pays nothing.
pub(super) fn exempt_content_addressed(
    classifier: &dyn KeyClassifier,
    checks: &mut ValidationSet,
    writes: &BTreeMap<Vec<u8>, Option<Vec<u8>>>,
    merges: &[(Vec<u8>, Vec<u8>)],
) {
    let exempt = |key: &[u8]| class_of(classifier, key) == KeyClass::ContentAddressed;
    checks.reads.retain(|read| !exempt(read.key.as_slice()));
    checks.exempt = writes
        .keys()
        .chain(merges.iter().map(|(key, _)| key))
        .filter(|key| exempt(key.as_slice()))
        .cloned()
        .collect();
    checks.exempt.sort_unstable();
    checks.exempt.dedup();
}

impl IsolationLevel {
    /// Whether a key the commit only merges into, and did not read, is
    /// validated against the newest write that replaced it instead of the
    /// newest write of any kind.
    pub(crate) fn blind_merges_commute(self) -> bool {
        self == Self::DefraLevel
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::column_family::{DEFAULT_CF_ID, prefix_key};
    use crate::engine::ConflictKey;

    /// Keys that start with `c` are content-addressed, those with `p` are in a
    /// commutative prefix, the rest are ordinary.
    struct ByFirstByte;

    impl KeyClassifier for ByFirstByte {
        fn classify(&self, key: &[u8]) -> KeyClass {
            match key.first() {
                Some(b'c') => KeyClass::ContentAddressed,
                Some(b'p') => KeyClass::CommutativePrefix { len: 1 },
                _ => KeyClass::Ordinary,
            }
        }
    }

    fn key(name: &[u8]) -> Vec<u8> {
        prefix_key(DEFAULT_CF_ID, name)
    }

    fn read(name: &[u8]) -> ConflictKey {
        ConflictKey {
            key: key(name),
            observed_seq: 3,
        }
    }

    #[test]
    fn exempting_drops_the_reads_of_content_addressed_keys_and_lists_the_ones_written() {
        let mut checks = ValidationSet {
            reads: vec![read(b"a"), read(b"c1"), read(b"c3"), read(b"p")],
            writes_at: Some(3),
            blind_merges_commute: true,
            exempt: Vec::new(),
        };
        let writes: BTreeMap<Vec<u8>, Option<Vec<u8>>> = [
            (key(b"b"), Some(b"v".to_vec())),
            (key(b"c2"), None),
            (key(b"c3"), Some(b"v".to_vec())),
        ]
        .into_iter()
        .collect();
        let merges = [
            (key(b"c9"), b"op".to_vec()),
            (key(b"c2"), b"op".to_vec()),
            (key(b"c9"), b"op".to_vec()),
            (key(b"m"), b"op".to_vec()),
        ];

        exempt_content_addressed(&ByFirstByte, &mut checks, &writes, &merges);

        let read_keys: Vec<Vec<u8>> = checks.reads.iter().map(|read| read.key.clone()).collect();
        assert_eq!(read_keys, [key(b"a"), key(b"p")]);
        assert_eq!(
            checks.exempt,
            [key(b"c2"), key(b"c3"), key(b"c9")],
            "only the content-addressed keys, sorted, each once"
        );
    }

    #[test]
    fn a_commit_that_names_no_content_addressed_key_exempts_nothing() {
        let mut checks = ValidationSet {
            reads: vec![read(b"a"), read(b"p")],
            writes_at: Some(3),
            blind_merges_commute: true,
            exempt: Vec::new(),
        };
        let writes = BTreeMap::from([(key(b"b"), Some(b"v".to_vec()))]);

        exempt_content_addressed(&ByFirstByte, &mut checks, &writes, &[]);

        assert_eq!(checks.reads.len(), 2);
        assert!(checks.exempt.is_empty());
    }

    #[test]
    fn a_key_too_short_to_carry_the_prefix_is_ordinary() {
        assert_eq!(class_of(&ByFirstByte, b"c"), KeyClass::Ordinary);
        assert_eq!(
            class_of(&ByFirstByte, &key(b"c")),
            KeyClass::ContentAddressed
        );
    }
}
