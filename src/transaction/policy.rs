//! Caller-declared key classes that [`IsolationLevel::DefraLevel`] applies.
//!
//! regolith knows nothing about what a caller's keys mean. A caller whose
//! keyspace makes some conflicts harmless says so through a
//! [`KeyClassifier`], and the level relaxes validation for those keys on the
//! caller's word: a scan inside a commutative prefix is not validated as a
//! read, a put or merge of a content-addressed key is not validated, and a
//! read of one that found it is validated for its presence only. Anything
//! else is validated as at [`IsolationLevel::RepeatableRead`]. The classifier
//! does not govern blind merges, which commute at this level for every key.

use std::collections::BTreeMap;
use std::sync::Arc;

use crate::Access;
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
    /// [`IsolationLevel::DefraLevel`] with a [`KeyClassifier`] installed.
    /// There, the commit disregards a scan
    /// stretch that stays inside one such prefix. The keys that scan
    /// returned are not validated as reads, as for any scan at
    /// [`IsolationLevel::RepeatableRead`]. A write or merge the transaction
    /// makes inside that stretch, before or after the scan, is validated as
    /// a blind write instead of as a read: an identical rewrite of a key's
    /// current value commits, and a merge there is blind. A write still
    /// conflicts with a newer commit to its key, a removal included, unless
    /// the key already holds exactly what the write would store. A stretch
    /// that leaves the prefix is recorded as at `RepeatableRead`.
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
    /// There:
    ///
    /// - A put or merge of the key never conflicts with a newer write, and
    ///   neither does a read of a key the transaction puts or merges, so two
    ///   transactions that create the same key both commit. The newest write
    ///   of a key decides: a key the transaction deletes and then puts or
    ///   merges counts as put or merged.
    /// - A delete of the key is validated like a delete of any other key: it
    ///   conflicts with a commit to the key since the transaction began,
    ///   unless the key already holds what the delete would leave.
    /// - A `get`, a `get_slice` or a `get_for_update` that found the key is
    ///   validated for its presence only. It conflicts at commit when the key
    ///   is gone, because a delete or a range delete over it is the newest
    ///   write, and not when a newer put or merge left it there. One that
    ///   found nothing is validated like a read of any other key, so a newer
    ///   put conflicts.
    /// - A scan that returns the key records no read of it, as for any scan at
    ///   [`IsolationLevel::RepeatableRead`]. A key the transaction puts or
    ///   merges inside a scanned stretch is not validated as a read either,
    ///   while one it deletes there is, as for any key.
    ///
    /// Other levels, and transactions without a classifier, are unchanged.
    ///
    /// The caller's contract is that the bytes under the key never differ.
    /// regolith checks it where that costs nothing on the common path. When
    /// a commit made after the transaction began left the key a value, and
    /// the transaction puts different bytes, the commit applies nothing and
    /// fails with [`crate::Error::ContentMismatch`]. A put of the same bytes
    /// commits. The check does not look at a key whose newest version is a
    /// delete or a merge operand, at a merge, or at bytes that were already
    /// different before the transaction began, so the contract still rests on
    /// the caller.
    ContentAddressed,
}

/// Classifies keys for [`IsolationLevel::DefraLevel`].
///
/// `classify` sees the key as the caller wrote it, without regolith's
/// column-family prefix. It must be pure, deterministic and allocation-free:
/// commit calls it while it holds the transaction and before it takes the
/// write pipeline, at most once for the start of each scan stretch and at
/// most once for each distinct key the transaction reads, puts or merges. A
/// key it only deletes is not classified.
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
///
/// A key is classified at most once, however many operands the commit merges
/// into it or whether it is also read, and only the exempt keys are copied.
pub(super) fn exempt_content_addressed(
    classifier: &dyn KeyClassifier,
    checks: &mut ValidationSet,
    writes: &BTreeMap<Vec<u8>, Option<Vec<u8>>>,
    merges: &[(Vec<u8>, Vec<u8>)],
) {
    let content_addressed = |key: &[u8]| class_of(classifier, key) == KeyClass::ContentAddressed;
    let is_put = |key: &[u8]| matches!(writes.get(key), Some(Some(_)));
    // The keys merged into, each once however many operands they got.
    let mut merged: Vec<&[u8]> = merges.iter().map(|(key, _)| key.as_slice()).collect();
    merged.sort_unstable();
    merged.dedup();
    // The exempt keys as references, so only those are copied below: the
    // content-addressed ones put, already in the map's order, then the ones
    // merged that are not also put, which were classified with the puts.
    let mut exempt: Vec<&[u8]> = writes
        .iter()
        .filter(|(_, value)| value.is_some())
        .map(|(key, _)| key.as_slice())
        .filter(|key| content_addressed(key))
        .collect();
    let puts = exempt.len();
    exempt.extend(
        merged
            .iter()
            .copied()
            .filter(|key| !is_put(key) && content_addressed(key)),
    );
    if exempt.len() > puts {
        exempt.sort_unstable();
    }
    let exempt: Vec<Vec<u8>> = exempt.into_iter().map(<[u8]>::to_vec).collect();
    checks.reads.retain_mut(|read| {
        if exempt
            .binary_search_by(|key| key.as_slice().cmp(&read.key))
            .is_ok()
        {
            return false;
        }
        // A key the commit puts or merges was classified above, and is not
        // exempt.
        if read.found
            && !is_put(&read.key)
            && merged.binary_search(&read.key.as_slice()).is_err()
            && content_addressed(&read.key)
        {
            read.access = Access::ReadPresence;
        }
        true
    });
    checks.exempt = exempt;
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
            access: Access::Read,
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
            .map(|read| (read.key.clone(), read.presence_only()))
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

    /// Remembers how often it was asked about each key.
    struct Counting(std::sync::Mutex<BTreeMap<Vec<u8>, usize>>);

    impl KeyClassifier for Counting {
        fn classify(&self, key: &[u8]) -> KeyClass {
            *self.0.lock().unwrap().entry(key.to_vec()).or_default() += 1;
            ByFirstByte.classify(key)
        }
    }

    #[test]
    fn each_distinct_key_is_classified_once_however_often_it_is_named() {
        let mut checks = checks_of(vec![
            read(b"a", true),
            read(b"c1", true),
            read(b"c9", true),
            read(b"p", true),
        ]);
        let writes: BTreeMap<Vec<u8>, Option<Vec<u8>>> = [
            (key(b"c1"), None),
            (key(b"c3"), Some(b"v".to_vec())),
            (key(b"p"), Some(b"v".to_vec())),
        ]
        .into_iter()
        .collect();
        let merges = [
            (key(b"c9"), b"1".to_vec()),
            (key(b"p"), b"2".to_vec()),
            (key(b"c9"), b"3".to_vec()),
            (key(b"c3"), b"4".to_vec()),
            (key(b"c9"), b"5".to_vec()),
            (key(b"p"), b"6".to_vec()),
        ];
        let classifier = Counting(Default::default());

        exempt_content_addressed(&classifier, &mut checks, &writes, &merges);

        let calls = classifier.0.lock().unwrap();
        let asked: Vec<Vec<u8>> = calls.keys().cloned().collect();
        assert_eq!(
            asked,
            [
                b"a".to_vec(),
                b"c1".to_vec(),
                b"c3".to_vec(),
                b"c9".to_vec(),
                b"p".to_vec()
            ],
            "the classifier sees keys without the column-family prefix"
        );
        assert!(calls.values().all(|&times| times == 1), "{calls:?}");
        assert_eq!(checks.exempt, [key(b"c3"), key(b"c9")]);
        assert_eq!(
            kept(&checks),
            [(key(b"a"), false), (key(b"c1"), true), (key(b"p"), false)]
        );
    }

    #[test]
    fn only_a_defra_level_transaction_with_a_policy_has_a_classifier() {
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
