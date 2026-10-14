//! Benchmarks for non-blocking reads on per-thread I/O queues (plan 4.10,
//! D53).
//!
//! `io_queue_hit` reads blocks the cache holds, through a `Blocking` and a
//! `CacheOnly` snapshot: the price of the mode on a hit, which should be the
//! two thread-local writes that set and clear it.
//!
//! `io_queue_miss_to_ready` reads blocks the cache never holds (it is
//! disabled), so every read goes to the device, and compares the two ways a
//! thread that must not block can get the block: through its own queue (the
//! read returns `WouldBlock`, the thread polls its queue, which reads the
//! block, and runs the read again) against a hop to an I/O thread (the read
//! is handed over a channel to a thread that reads blocking, and the answer
//! comes back the same way). The first is D53's design; the second is the
//! design it replaced.
//!
//! The `Blocking` read path itself is measured before and after by
//! `point_read` and `scan`.

mod common;

use std::hint::black_box;
use std::sync::mpsc;
use std::thread;
use std::time::Instant;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};
use regolith::{Db, Error, IoBudget, Options, ReadMode, WouldBlock, WriteBatch};

const N_KEYS: u64 = 100_000;
const VALUE_LEN: usize = 100;
const HOT_CACHE: usize = 256 * 1024 * 1024;
const FILL_BATCH: u64 = 1_000;

/// Fill, compact into tables, then read every key once so the OS page
/// cache holds the files and a block read costs a copy, not a disk seek.
fn build(tag: &str, block_cache_size: usize, keys: &[Vec<u8>]) -> (common::TempDb, Db) {
    let opts = Options::default()
        .write_buffer_size(8 * 1024 * 1024)
        .block_cache_size(block_cache_size);
    let (tmp, db) = common::open(tag, opts);
    let mut rng = common::Rng::new(0x10_0E0E);
    let mut i = 0u64;
    while i < N_KEYS {
        let end = (i + FILL_BATCH).min(N_KEYS);
        let mut batch = WriteBatch::new();
        while i < end {
            batch.put(&keys[i as usize], &common::rand_value(&mut rng, VALUE_LEN));
            i += 1;
        }
        db.write(batch).expect("fill write");
    }
    db.compact_range(None, None)
        .wait()
        .expect("fill compaction");
    for k in keys {
        assert!(db.get(k).expect("warm read").is_some(), "key missing");
    }
    (tmp, db)
}

fn io_queue_hit(c: &mut Criterion) {
    let keys: Vec<Vec<u8>> = (0..N_KEYS).map(common::key).collect();
    let (_dir, db) = build("io-queue-hit", HOT_CACHE, &keys);
    let queue = db.io_queue();
    let blocking = db.snapshot();
    let cache_only = db
        .snapshot()
        .with_read_mode(ReadMode::CacheOnly(queue.id()));

    let mut group = c.benchmark_group("io_queue_hit");
    group.throughput(Throughput::Elements(1));
    for (id, snapshot) in [("blocking", &blocking), ("cache_only", &cache_only)] {
        group.bench_function(id, |b| {
            let mut rng = common::Rng::new(0x41_7E57);
            b.iter(|| {
                let k = &keys[(rng.next() % N_KEYS) as usize];
                black_box(snapshot.get(k).expect("a cached read"))
            });
        });
    }
    group.finish();
}

fn io_queue_miss_to_ready(c: &mut Criterion) {
    let keys: Vec<Vec<u8>> = (0..N_KEYS).map(common::key).collect();
    let (_dir, db) = build("io-queue-miss", 0, &keys);

    let mut group = c.benchmark_group("io_queue_miss_to_ready");
    group.throughput(Throughput::Elements(1));

    let mut queue = db.io_queue();
    let snapshot = db
        .snapshot()
        .with_read_mode(ReadMode::CacheOnly(queue.id()));
    group.bench_function("own_queue", |b| {
        let mut rng = common::Rng::new(0x0E7E_0001);
        b.iter_custom(|iters| {
            let start = Instant::now();
            for _ in 0..iters {
                let k = &keys[(rng.next() % N_KEYS) as usize];
                let found = loop {
                    match snapshot.get(k) {
                        Err(Error::WouldBlock(WouldBlock::Io(_))) => {
                            queue.poll(IoBudget::ALL);
                        }
                        other => break other.expect("read"),
                    }
                };
                black_box(found);
            }
            start.elapsed()
        });
    });

    let (requests, served) = mpsc::channel::<Vec<u8>>();
    let (answers, answered) = mpsc::channel::<Option<Vec<u8>>>();
    thread::scope(|scope| {
        let db = &db;
        scope.spawn(move || {
            for k in served {
                answers.send(db.get(&k).expect("read")).expect("answer");
            }
        });
        group.bench_function("hop_to_io_thread", |b| {
            let mut rng = common::Rng::new(0x0E7E_0001);
            b.iter_custom(|iters| {
                let start = Instant::now();
                for _ in 0..iters {
                    let k = keys[(rng.next() % N_KEYS) as usize].clone();
                    requests.send(k).expect("request");
                    black_box(answered.recv().expect("answer"));
                }
                start.elapsed()
            });
        });
        drop(requests);
    });
    group.finish();
}

criterion_group!(benches, io_queue_hit, io_queue_miss_to_ready);
criterion_main!(benches);
