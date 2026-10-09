//! Auto traits of the public handles, asserted at compile time.
//!
//! A handle that silently stops being `Send` or `Sync` breaks every caller that
//! moves it across a thread or shares it behind an `Arc`, and the break shows
//! up in the caller's build, not here. Each assertion below is a bound on a
//! `const fn`, so losing a bound fails to compile this file instead of passing
//! quietly.

// Native-only. wasm-pack builds every test target for wasm32, and the browser
// suite lives in tests/wasm_opfs*.rs.
#![cfg(not(target_arch = "wasm32"))]

use regolith::{
    CfIter, CommitReceipt, Conflict, Db, DbSlice, DbWithTtl, Entries, Error, Iter,
    OptimisticTransactionDb, OwnedSnapshotIter, ScanStream, Snapshot, TailingIter, Transaction,
    TransactionDb, TransactionError, TxnScanStream,
};

const fn assert_send<T: Send>() {}

const fn assert_send_sync<T: Send + Sync>() {}

#[test]
fn handles_are_send_and_sync() {
    assert_send_sync::<Transaction>();
    assert_send_sync::<Snapshot>();
    assert_send_sync::<DbSlice>();
    assert_send_sync::<Db>();
    assert_send_sync::<OptimisticTransactionDb>();
    assert_send_sync::<TransactionDb>();
    assert_send_sync::<DbWithTtl>();
    assert_send_sync::<Error>();
    assert_send_sync::<TransactionError>();
    assert_send_sync::<Conflict>();
    assert_send_sync::<CommitReceipt>();
}

#[test]
fn iterators_are_send() {
    assert_send::<Iter<'static>>();
    assert_send::<CfIter<'static>>();
    assert_send::<TailingIter>();
    assert_send::<OwnedSnapshotIter>();
    assert_send::<ScanStream>();
    assert_send::<Entries<OwnedSnapshotIter>>();
    assert_send::<TxnScanStream<'static>>();
}
