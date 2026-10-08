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
use std::sync::Arc;

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

/// The classifier a transaction at `isolation` consults: only
/// [`IsolationLevel::DefraLevel`] does, and only when the database installed
/// one. Every place that asks takes the answer from here.
pub(super) fn classifier_for(
    policy: &Option<Arc<dyn KeyClassifier>>,
    isolation: IsolationLevel,
) -> Option<&dyn KeyClassifier> {
    policy
        .as_deref()
        .filter(|_| isolation == IsolationLevel::DefraLevel)
}

/// Apply the content-addressed rule to `checks`, which holds the commit's
/// reads once the transaction's scans are folded in.
///
/// A key the commit puts or merges is listed in `checks.exempt`, so the
/// engine validates neither the write nor any read of it. The newest write of
/// a key decides: `settle` keeps an operand only when it is newer than the
/// key's newest put or delete, so a key with an operand is merged, and one
/// without is put or deleted by its point write. A deleted key is not listed:
/// its delete is validated as for any key, and a read of it that found a value
/// is validated for presence only, so a concurrent delete or put of the key
/// still decides the commit.
///
/// Every other read of a content-addressed key that found a value is marked
/// presence-only, and one that found nothing stays a read like any other.
///
/// The listing is a sorted copy of the exempt keys, built here before the
/// commit takes the write pipeline. The engine finds a written key in it by
/// binary search, which neither hashes nor allocates, and skips the key's
/// lookup outright, where a lookup is what validating it would cost. A commit
/// whose classifier names no such key leaves the list empty and pays nothing.
pub(super) fn exempt_content_addressed(
    classifier: &dyn KeyClassifier,
    checks: &mut ValidationSet,
    writes: &BTreeMap<Vec<u8>, Option<Vec<u8>>>,
    merges: &[(Vec<u8>, Vec<u8>)],
) {
    let content_addressed = |key: &[u8]| class_of(classifier, key) == KeyClass::ContentAddressed;
    checks.exempt = writes
        .iter()
        .filter(|(_, value)| value.is_some())
        .map(|(key, _)| key)
        .chain(merges.iter().map(|(key, _)| key))
        .filter(|key| content_addressed(key.as_slice()))
        .cloned()
        .collect();
    checks.exempt.sort_unstable();
    checks.exempt.dedup();
    let exempt = &checks.exempt;
    checks.reads.retain_mut(|read| {
        if exempt
            .binary_search_by(|key| key.as_slice().cmp(&read.key))
            .is_ok()
        {
            return false;
        }
        read.presence_only = read.found && content_addressed(&read.key);
        true
    });
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

    fn read(name: &[u8], found: bool) -> ConflictKey {
        ConflictKey {
            key: key(name),
            observed_seq: 3,
            found,
            presence_only: false,
        }
    }

    fn checks_of(reads: Vec<ConflictKey>) -> ValidationSet {
        ValidationSet {
            reads,
            writes_at: Some(3),
            blind_merges_commute: true,
            exempt: Vec::new(),
        }
    }

    /// Each read left in `checks`, with whether it is presence-only.
    fn kept(checks: &ValidationSet) -> Vec<(Vec<u8>, bool)> {
        checks
            .reads
            .iter()
            .map(|read| (read.key.clone(), read.presence_only))
            .collect()
    }

    #[test]
    fn exempting_lists_the_content_addressed_keys_put_or_merged_and_drops_their_reads() {
        let mut checks = checks_of(vec![
            read(b"a", true),
            read(b"c1", true),
            read(b"c3", true),
            read(b"c4", false),
            read(b"c5", true),
            read(b"p", true),
        ]);
        let writes: BTreeMap<Vec<u8>, Option<Vec<u8>>> = [
            (key(b"b"), Some(b"v".to_vec())),
            (key(b"c2"), None),
            (key(b"c3"), Some(b"v".to_vec())),
            (key(b"c5"), None),
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

        assert_eq!(
            checks.exempt,
            [key(b"c2"), key(b"c3"), key(b"c9")],
            "the content-addressed keys put or merged, sorted, each once; c5 is only deleted"
        );
        assert_eq!(
            kept(&checks),
            [
                (key(b"a"), false),
                (key(b"c1"), true),
                (key(b"c4"), false),
                (key(b"c5"), true),
                (key(b"p"), false),
            ],
            "c3 is put, so its read is gone; a content-addressed read that found a value is \
             presence-only, one that found nothing is an ordinary read, and c5 is deleted but \
             not exempt"
        );
    }

    #[test]
    fn a_commit_that_names_no_content_addressed_key_exempts_nothing() {
        let mut checks = checks_of(vec![read(b"a", true), read(b"p", true)]);
        let writes = BTreeMap::from([(key(b"b"), Some(b"v".to_vec()))]);

        exempt_content_addressed(&ByFirstByte, &mut checks, &writes, &[]);

        assert_eq!(kept(&checks), [(key(b"a"), false), (key(b"p"), false)]);
        assert!(checks.exempt.is_empty());
    }

    #[test]
    fn only_a_defra_transaction_with_a_policy_has_a_classifier() {
        let policy: Option<Arc<dyn KeyClassifier>> = Some(Arc::new(ByFirstByte));
        for level in [
            IsolationLevel::ReadCommitted,
            IsolationLevel::SnapshotIsolation,
            IsolationLevel::RepeatableRead,
            IsolationLevel::Serializable,
        ] {
            assert!(classifier_for(&policy, level).is_none(), "{level:?}");
        }
        assert!(classifier_for(&policy, IsolationLevel::DefraLevel).is_some());
        assert!(classifier_for(&None, IsolationLevel::DefraLevel).is_none());
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
