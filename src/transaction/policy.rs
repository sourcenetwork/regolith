//! Caller-declared key classes that [`IsolationLevel::DefraLevel`] applies.
//!
//! regolith knows nothing about what a caller's keys mean. A caller whose
//! keyspace makes some conflicts harmless says so through a
//! [`KeyClassifier`], and the level relaxes validation for exactly those
//! keys, on the caller's word. Every other key is validated as at
//! [`IsolationLevel::RepeatableRead`].

use crate::transaction::IsolationLevel;

use super::scan_range::ScanRun;

/// What a caller declares about one key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KeyClass {
    /// No declaration: validated as at [`IsolationLevel::RepeatableRead`].
    Ordinary,
    /// The key lies in a prefix the caller declares commutative. `len` is
    /// the prefix length: every key that starts with this key's first
    /// `len` bytes is in the same class.
    ///
    /// A transactional scan that stays inside one such prefix records no
    /// stretch, so a key it walked is not re-anchored at the begin snapshot
    /// when the transaction also writes it, and an identical write there
    /// still elides. The scan becomes an unvalidated read, as a plain read
    /// is at [`IsolationLevel::SnapshotIsolation`]: a concurrent commit
    /// that adds or removes a key in the prefix never aborts the scanner.
    ///
    /// That is safe only when nothing the transaction decides depends on
    /// which keys of the prefix it saw. Keys there should be added under
    /// fresh names, with any two writers of one key writing the same
    /// bytes, and a transaction that branches on a prefix scan - writing
    /// something elsewhere only when a key is absent - must not rely on
    /// this class for that prefix: two such transactions can both commit
    /// where a serial order would let only one act.
    CommutativePrefix {
        /// Length of the shared prefix, in bytes of the caller's key.
        len: usize,
    },
}

/// Classifies keys for [`IsolationLevel::DefraLevel`].
///
/// `classify` sees the key as the caller wrote it, without regolith's
/// column-family prefix, and must be pure, deterministic and cheap: commit
/// calls it while holding the transaction, once per scan stretch.
pub trait KeyClassifier: Send + Sync {
    /// The class `key` belongs to.
    fn classify(&self, key: &[u8]) -> KeyClass;
}

/// Whether `run` stays inside one commutative prefix of one column family.
/// A run that was never closed reaches the end of the keyspace, so it never
/// does.
pub(super) fn run_is_commutative(classifier: &dyn KeyClassifier, run: &ScanRun) -> bool {
    const CF: usize = 4;
    let (first, Some(last)) = run.bounds() else {
        return false;
    };
    if first.len() < CF || last.len() < CF || first[..CF] != last[..CF] {
        return false;
    }
    let (first, last) = (&first[CF..], &last[CF..]);
    match classifier.classify(first) {
        KeyClass::CommutativePrefix { len } => {
            first.len() >= len && last.len() >= len && first[..len] == last[..len]
        }
        KeyClass::Ordinary => false,
    }
}

impl IsolationLevel {
    /// Whether a key the commit only merges into, and did not read, is
    /// validated against the newest write that replaced it instead of the
    /// newest write of any kind.
    pub(crate) fn blind_merges_commute(self) -> bool {
        self == Self::DefraLevel
    }
}
