//! What a transaction callback costs at commit, and what a savepoint costs.
//!
//! The headline is the commit of a transaction that registered no callback:
//! it must not move when the callback machinery exists, so it is timed first
//! for both transaction flavors, once with a write and once read-only (the
//! cheapest commit there is, so the most sensitive to an extra check). Then
//! the commit with one `on_commit`, one `before_commit`, one `on_abort` and
//! under a database hook, and the cost of a savepoint against the size of the
//! write buffer: setting one and rolling back to it must not grow with the
//! buffer.
//!
//! Each figure is the median over blocks of the mean microseconds per
//! operation, with the fastest block beside it: on a loaded machine the
//! minimum is the steadier estimate of what the code itself costs. `--plain`
//! runs only the commits without callbacks, which take seconds, for many
//! interleaved rounds against another build.

mod common;

use std::time::Instant;

use regolith::{OptimisticTransactionDb, Options, TransactionDb, TxnOptions};

const BLOCKS: usize = 21;
const OPS_PER_BLOCK: usize = 4_000;
/// Savepoint operations per block times the buffer size, held about constant.
const SAVEPOINT_OPS: usize = 2_000_000;

/// Median and minimum over `blocks` blocks of the mean microseconds one `op`
/// takes.
fn micros_per_op(blocks: usize, ops_per_block: usize, op: &mut dyn FnMut(u64)) -> (f64, f64) {
    let mut samples = Vec::with_capacity(blocks);
    let mut n = 0u64;
    for _ in 0..blocks {
        let started = Instant::now();
        for _ in 0..ops_per_block {
            op(n);
            n += 1;
        }
        samples.push(started.elapsed().as_secs_f64() * 1e6 / ops_per_block as f64);
    }
    let fastest = common::min_max(&samples).0;
    (common::median(&mut samples), fastest)
}

fn open_pair(
    tag: &str,
    options: Options,
) -> (OptimisticTransactionDb, TransactionDb, [common::TempDb; 2]) {
    let dirs = [
        common::TempDb::new(&format!("txn-callbacks-opt-{tag}")),
        common::TempDb::new(&format!("txn-callbacks-pes-{tag}")),
    ];
    let opt = OptimisticTransactionDb::open(dirs[0].path(), options.clone())
        .unwrap_or_else(|e| panic!("open: {e}"));
    let pes = TransactionDb::open(dirs[1].path(), options).unwrap_or_else(|e| panic!("open: {e}"));
    opt.db().put(b"seed", b"v").expect("seed");
    pes.db().put(b"seed", b"v").expect("seed");
    (opt, pes, dirs)
}

fn main() {
    let args = common::args();
    let quick = args.iter().any(|a| a == "--quick" || a == "--test");
    let plain_only = args.iter().any(|a| a == "--plain");
    let (blocks, ops_per_block) = if quick {
        (3, 200)
    } else {
        (BLOCKS, OPS_PER_BLOCK)
    };
    let per_op = |op: &mut dyn FnMut(u64)| micros_per_op(blocks, ops_per_block, op);

    let mut rows = Vec::new();
    let mut report = |name: &str, (us, fastest): (f64, f64)| {
        println!("{name:<52} {us:>9.3} us   min {fastest:>9.3} us");
        rows.push(format!(
            "{{\"case\":\"{name}\",\"us\":{us:.3},\"min_us\":{fastest:.3}}}"
        ));
    };

    println!("txn callbacks: median microseconds per transaction");
    let (opt, pes, _dirs) = open_pair("plain", Options::default());
    report(
        "commit, no callbacks, write, optimistic",
        per_op(&mut |n| {
            let txn = opt.begin(&TxnOptions::new());
            txn.put(b"k", &n.to_le_bytes()).expect("put");
            txn.commit().expect("commit");
        }),
    );
    report(
        "commit, no callbacks, write, pessimistic",
        per_op(&mut |n| {
            let txn = pes.begin(&TxnOptions::new());
            txn.put(b"k", &n.to_le_bytes()).expect("put");
            txn.commit().expect("commit");
        }),
    );
    report(
        "commit, no callbacks, read-only, optimistic",
        per_op(&mut |_| {
            let txn = opt.begin(&TxnOptions::new());
            txn.get(b"seed").expect("get");
            txn.commit().expect("commit");
        }),
    );
    report(
        "commit, no callbacks, read-only, pessimistic",
        per_op(&mut |_| {
            let txn = pes.begin(&TxnOptions::new());
            txn.get(b"seed").expect("get");
            txn.commit().expect("commit");
        }),
    );
    if plain_only {
        return;
    }

    println!("txn savepoints: median microseconds per operation, by buffered writes");
    for buffered in [16usize, 256, 4_096, 65_536] {
        let tmp = common::TempDb::new("txn-savepoint");
        let db = OptimisticTransactionDb::open(tmp.path(), common::default_opts())
            .unwrap_or_else(|e| panic!("open: {e}"));
        let mut txn = db.begin(&TxnOptions::new());
        for i in 0..buffered {
            txn.put(format!("key/{i:08}").as_bytes(), b"value-value-value")
                .expect("put");
        }
        // Fewer operations over a bigger buffer, so a savepoint that copies the
        // buffer still finishes: the cost per operation is what is compared.
        let ops = (SAVEPOINT_OPS / buffered).clamp(20, ops_per_block);
        report(
            &format!("savepoint set + rollback, {buffered} writes buffered"),
            micros_per_op(blocks, ops, &mut |_| {
                txn.set_savepoint();
                txn.rollback_to_savepoint().expect("rollback");
            }),
        );
        report(
            &format!("savepoint set + 1 put + rollback, {buffered} buffered"),
            micros_per_op(blocks, ops, &mut |n| {
                txn.set_savepoint();
                txn.put(&n.to_be_bytes(), b"scratch").expect("put");
                txn.rollback_to_savepoint().expect("rollback");
            }),
        );
    }

    common::write_family("txn_callbacks", &format!("[{}]", rows.join(",")));
}
