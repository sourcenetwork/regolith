//! What a caller reads back from the handles it holds: the statistics a
//! database was opened with.

// Native-only. wasm-pack builds every test target for wasm32, and the browser
// suite lives in tests/wasm_opfs*.rs.
#![cfg(not(target_arch = "wasm32"))]

use std::sync::Arc;

use regolith::{Db, IsolationLevel, OptimisticTransactionDb, Options, Statistics, Ticker};
use regolith::{TransactionDb, TxnOptions};

#[test]
fn a_database_hands_back_the_statistics_it_was_opened_with() {
    let stats = Arc::new(Statistics::new());
    let options = Options::memory().statistics(Some(Arc::clone(&stats)));
    let db = Db::open("surface-statistics", options).unwrap();

    let handed_back = db.statistics().expect("the database was opened with one");
    assert!(
        Arc::ptr_eq(handed_back, &stats),
        "the caller's own object, not a copy"
    );
    db.put(b"k", b"v").unwrap();
    assert_eq!(handed_back.get_ticker(Ticker::KeysWritten), 1);
    assert_eq!(stats.get_ticker(Ticker::KeysWritten), 1);
}

#[test]
fn a_database_opened_without_statistics_hands_back_none() {
    let db = Db::open("surface-no-statistics", Options::memory()).unwrap();
    assert!(db.statistics().is_none());
    db.put(b"k", b"v").unwrap();
    assert!(db.statistics().is_none(), "none is made on demand");
}

/// A caller that holds only a transaction database, and never kept the
/// `Arc` it opened it with, still reads the commit tickers.
#[test]
fn both_transaction_databases_reach_their_statistics() {
    let options = || Options::memory().statistics(Some(Arc::new(Statistics::new())));

    let optimistic = OptimisticTransactionDb::open("surface-optimistic", options()).unwrap();
    let txn = optimistic.begin(&TxnOptions::new().isolation(IsolationLevel::RepeatableRead));
    txn.put(b"k", b"v").unwrap();
    txn.commit().unwrap();
    let stats = optimistic.db().statistics().unwrap();
    assert_eq!(stats.get_ticker(Ticker::CommitCount), 1);

    let pessimistic = TransactionDb::open("surface-pessimistic", options()).unwrap();
    let txn = pessimistic.begin(&TxnOptions::new());
    txn.put(b"k", b"v").unwrap();
    txn.commit().unwrap();
    let stats = pessimistic.db().statistics().unwrap();
    assert_eq!(stats.get_ticker(Ticker::CommitCount), 1);
}
