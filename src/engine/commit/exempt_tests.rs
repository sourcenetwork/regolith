//! A key listed in `ValidationSet::exempt` is never validated, as a write or
//! as a merge, and the keys beside it still are.

use std::collections::BTreeMap;

use tempfile::TempDir;

use super::super::{EngineOptions, ValidationSet};
use super::*;
use crate::WriteBatchOp;
use crate::column_family::{DEFAULT_CF_ID, prefix_key};

/// `name` as the default column family stores it.
fn key_of(name: &[u8]) -> Vec<u8> {
    prefix_key(DEFAULT_CF_ID, name)
}

/// Commit a transaction that began before `a` and `c` were written, listing
/// `exempt` as exempt, putting `puts` and merging into `merged`. A fresh
/// database each time, so one commit's writes never answer for another's.
fn commit_after_newer_writes(exempt: &[&[u8]], puts: &[&[u8]], merged: &[&[u8]]) -> CommitOutcome {
    let dir = TempDir::new().unwrap();
    let engine = RegolithEngine::open(dir.path(), EngineOptions::default()).unwrap();
    let observed = engine.snapshot_seq();
    for name in [b"a", b"c"] {
        let newer = WriteBatchOp::Put {
            key: key_of(name),
            value: b"newer".to_vec(),
        };
        engine
            .apply_batch(vec![newer], DurabilityMode::Eventual, false)
            .unwrap();
    }
    let checks = ValidationSet {
        reads: Vec::new(),
        writes_at: Some(observed),
        blind_merges_commute: false,
        exempt: exempt.iter().copied().map(key_of).collect(),
    };
    let point_ops: BTreeMap<Vec<u8>, Option<Vec<u8>>> = puts
        .iter()
        .map(|name| (key_of(name), Some(b"mine".to_vec())))
        .collect();
    let merges: Vec<(Vec<u8>, Vec<u8>)> = merged
        .iter()
        .map(|name| (key_of(name), b"op".to_vec()))
        .collect();
    engine
        .commit_optimistic(
            &checks,
            point_ops,
            Vec::new(),
            merges,
            DurabilityMode::Eventual,
        )
        .unwrap()
}

#[test]
fn an_exempt_key_is_written_beside_a_newer_write_and_an_ordinary_key_is_not() {
    let outcome = commit_after_newer_writes(&[b"c"], &[b"c"], &[]);
    assert!(matches!(outcome, CommitOutcome::Ok), "{outcome:?}");

    let outcome = commit_after_newer_writes(&[], &[b"c"], &[]);
    assert!(
        matches!(outcome, CommitOutcome::Conflict { .. }),
        "unlisted, the same write conflicts: {outcome:?}"
    );

    let outcome = commit_after_newer_writes(&[b"c"], &[b"a", b"c"], &[]);
    let CommitOutcome::Conflict { key, .. } = outcome else {
        panic!("the ordinary key beside the exempt one must conflict: {outcome:?}");
    };
    assert_eq!(key, key_of(b"a"));
}

#[test]
fn an_exempt_key_is_merged_beside_a_newer_write_and_an_ordinary_key_is_not() {
    let outcome = commit_after_newer_writes(&[b"c"], &[], &[b"c"]);
    assert!(matches!(outcome, CommitOutcome::Ok), "{outcome:?}");

    let outcome = commit_after_newer_writes(&[], &[], &[b"c"]);
    assert!(
        matches!(outcome, CommitOutcome::Conflict { .. }),
        "unlisted, the same merge conflicts: {outcome:?}"
    );

    let outcome = commit_after_newer_writes(&[b"c"], &[], &[b"a", b"c"]);
    let CommitOutcome::Conflict { key, .. } = outcome else {
        panic!("the ordinary key beside the exempt one must conflict: {outcome:?}");
    };
    assert_eq!(key, key_of(b"a"));
}
