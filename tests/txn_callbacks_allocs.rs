//! What transaction callbacks cost in allocations.
//!
//! A transaction that registered nothing, under a database with no hooks, must
//! allocate nothing for them; one that registered a few allocates once, for
//! the queue box, and only the fifth callback of a kind spills to the heap.
//! Measured with a counting global allocator rather than a timer, so the
//! numbers are exact and independent of machine load.

// Native-only. wasm-pack builds every test target for wasm32, and this uses
// the filesystem.
#![cfg(not(target_arch = "wasm32"))]

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use regolith::{OptimisticTransactionDb, Options, TxnOptions};
use tempfile::TempDir;

static ARMED: AtomicBool = AtomicBool::new(false);
static COUNT: AtomicUsize = AtomicUsize::new(0);

/// The counters are process-wide, so a test holds this for its whole run.
static ONE_AT_A_TIME: Mutex<()> = Mutex::new(());

struct Counting;

fn count() {
    if ARMED.load(Ordering::Relaxed) {
        COUNT.fetch_add(1, Ordering::Relaxed);
    }
}

// SAFETY: every method forwards to `System`, which is a correct allocator, and
// only adds relaxed counter updates around it. No pointer or layout is
// altered, so the `GlobalAlloc` contract is exactly `System`'s.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        count();
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        count();
        unsafe { System.realloc(ptr, layout, new_size) }
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        count();
        unsafe { System.alloc_zeroed(layout) }
    }
}

#[global_allocator]
static ALLOC: Counting = Counting;

/// Run `f` and return how many allocations it made.
fn allocations(f: impl FnOnce()) -> usize {
    COUNT.store(0, Ordering::Relaxed);
    ARMED.store(true, Ordering::Relaxed);
    f();
    ARMED.store(false, Ordering::Relaxed);
    COUNT.load(Ordering::Relaxed)
}

fn open() -> (OptimisticTransactionDb, TempDir) {
    let dir = TempDir::new().unwrap();
    (
        OptimisticTransactionDb::open(dir.path(), Options::default()).unwrap(),
        dir,
    )
}

#[test]
fn prepare_allocates_nothing_without_callbacks() {
    let _serial = ONE_AT_A_TIME.lock().unwrap_or_else(|e| e.into_inner());
    let (db, _dir) = open();
    let mut txn = db.begin(&TxnOptions::new());
    assert_eq!(allocations(|| txn.prepare().unwrap()), 0);
}

#[test]
fn the_first_four_callbacks_of_a_kind_share_one_allocation() {
    let _serial = ONE_AT_A_TIME.lock().unwrap_or_else(|e| e.into_inner());
    let (db, _dir) = open();

    let mut txn = db.begin(&TxnOptions::new());
    let first = allocations(|| txn.on_commit(|_| {}));
    let next_three = allocations(|| {
        for _ in 0..3 {
            txn.on_commit(|_| {});
        }
    });
    let fifth = allocations(|| txn.on_commit(|_| {}));
    assert_eq!(first, 1, "the queue box");
    assert_eq!(next_three, 0, "the next three live in the box");
    assert!(fifth >= 1, "the fifth spills to the heap");
    // Dropping a transaction that registered only `on_commit` callbacks runs
    // none of them and needs no claim.
    drop(txn);

    let mut txn = db.begin(&TxnOptions::new());
    let before = allocations(|| {
        for _ in 0..4 {
            txn.before_commit(|_| Ok(()));
        }
    });
    assert_eq!(before, 1, "four before_commit callbacks, one allocation");
    assert_eq!(
        allocations(|| txn.prepare().unwrap()),
        0,
        "running them allocates nothing"
    );
}
