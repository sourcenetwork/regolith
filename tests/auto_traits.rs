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
    AbortReason, CfIter, CommitInfo, CommitReceipt, CompactionFilter, Conflict, Db, DbSlice,
    DbWithTtl, Entries, Env, Error, EventListener, IoBudget, IoProgress, IoQueue, IoUnit, IoWait,
    Iter, KeyClassifier, KeyProvider, LogLayout, MergeOperator, OptimisticTransactionDb,
    OwnedSnapshotIter, Page, QueueId, ReadMode, RetryPolicy, ScanCheck, ScanStream, Snapshot,
    TailingIter, TransactError, Transaction, TransactionDb, TransactionError, TransactionHooks,
    TxnCursor, TxnScanStream, WouldBlock,
};

const fn assert_send<T: Send>() {}

const fn assert_send_sync<T: Send + Sync>() {}

const fn assert_send_sync_static<T: ?Sized + Send + Sync + 'static>() {}

/// One function per trait, generic over that trait alone, so it compiles only
/// while the trait itself requires `Send + Sync + 'static` of everything that
/// implements it. An implementation then never states the bounds, and the
/// database can hold it in an `Arc` and call it from any thread.
macro_rules! requires_send_sync_static {
    ($($check:ident: $bound:path),* $(,)?) => {
        $(const fn $check<T: ?Sized + $bound>() {
            assert_send_sync_static::<T>();
        })*
    };
}

requires_send_sync_static! {
    key_classifier: KeyClassifier,
    merge_operator: MergeOperator,
    log_layout: LogLayout,
    transaction_hooks: TransactionHooks,
    event_listener: EventListener,
    key_provider: KeyProvider,
    compaction_filter: CompactionFilter,
}

/// An environment is shared across threads. It is not required to be
/// `'static`: the database holds it as an `Arc<dyn Env>`, which is.
const fn env<T: ?Sized + Env>() {
    const fn shared<T: ?Sized + Send + Sync>() {}
    shared::<T>();
}

#[test]
fn the_traits_a_caller_implements_are_send_sync_and_static() {
    key_classifier::<dyn KeyClassifier>();
    merge_operator::<dyn MergeOperator>();
    log_layout::<dyn LogLayout>();
    transaction_hooks::<dyn TransactionHooks>();
    event_listener::<dyn EventListener>();
    key_provider::<dyn KeyProvider>();
    compaction_filter::<dyn CompactionFilter>();
    env::<dyn Env>();
}

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
    assert_send_sync::<regolith::LockWait>();
    assert_send_sync::<Conflict>();
    assert_send_sync::<CommitReceipt>();
    assert_send_sync::<CommitInfo>();
    assert_send_sync::<AbortReason<'static>>();
    assert_send_sync::<RetryPolicy>();
    assert_send_sync::<ScanCheck>();
    assert_send_sync::<Page>();
    assert_send_sync::<TransactError<Error>>();
    assert_send_sync::<IoWait>();
    assert_send_sync::<WouldBlock>();
    assert_send_sync::<ReadMode>();
    assert_send_sync::<QueueId>();
    assert_send_sync::<IoBudget>();
    assert_send_sync::<IoProgress>();
    assert_send_sync::<IoUnit>();
}

/// An I/O queue moves to the thread that will own it, and only that thread
/// polls it: `Send`, and not `Sync` (the doc test on `IoQueue` fails to
/// compile a shared one).
#[test]
fn an_io_queue_is_send() {
    assert_send::<IoQueue>();
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
    assert_send::<TxnCursor>();
}
