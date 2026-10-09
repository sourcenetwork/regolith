//! `regolith::sync` locks against `std::sync::Mutex`.
//!
//! Run with `cargo bench --bench sync`.
//!
//! - **Uncontended**: one acquire and release on one thread, for the
//!   regolith `Mutex` (both `try_lock` and a `lock()` future polled once),
//!   `RwLock` reads and writes, a one-permit `Semaphore` acquire, and
//!   `std::sync::Mutex`.
//! - **Contended throughput**: N tasks take the same lock, bump a counter
//!   and release it, for N = 2, 8 and 32; one element is one lock and
//!   unlock. Three shapes:
//!   - `std_mutex`: one thread per task, blocking in `lock()`.
//!   - `regolith_mutex_park`: one thread per task, driving its future
//!     with an executor that parks the thread while the future is pending
//!     and is unparked by the waker.
//!   - `regolith_mutex_spin`: the same, but a waiting thread spins on its
//!     wake flag (yielding after a short spin) instead of parking, as a
//!     pinned-thread pool does when it keeps polling.
//!   - `regolith_mutex_one_thread`: all N tasks on one thread, each
//!     holding the lock across one suspension, so every lock is a queued
//!     handoff and nothing leaves the thread. `std::sync::Mutex` has no
//!     equivalent: held across a suspension on one thread it deadlocks.
//!
//! Strict FIFO handoff means a release hands the lock to a waiter that is
//! not running yet, so under contention with parked waiters every
//! acquisition costs a wake-up and a context switch; `std::sync::Mutex`
//! lets the releasing thread take the lock straight back instead. The
//! shapes above separate that cost from the primitive's own.
//!
//! No async runtime is involved: the executors are the functions below.

use std::future::Future;
use std::hint::black_box;
use std::pin::{Pin, pin};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::task::{Context, Poll, Wake, Waker};
use std::time::{Duration, Instant};

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use regolith::sync::{Mutex, RwLock, Semaphore};

struct Unpark(std::thread::Thread);

impl Wake for Unpark {
    fn wake(self: Arc<Self>) {
        self.0.unpark();
    }

    fn wake_by_ref(self: &Arc<Self>) {
        self.0.unpark();
    }
}

struct Flag(AtomicBool);

impl Wake for Flag {
    fn wake(self: Arc<Self>) {
        self.0.store(true, Ordering::Release);
    }

    fn wake_by_ref(self: &Arc<Self>) {
        self.0.store(true, Ordering::Release);
    }
}

/// How a task's thread waits for its waker.
#[derive(Clone, Copy)]
enum Executor {
    Park,
    Spin,
}

/// Drives `future` on this thread, waiting the `executor` way while it
/// is pending.
fn block_on<F: Future>(future: F, waker: &Waker, flag: &Flag, executor: Executor) -> F::Output {
    let mut future = pin!(future);
    let mut cx = Context::from_waker(waker);
    loop {
        if let Poll::Ready(output) = future.as_mut().poll(&mut cx) {
            return output;
        }
        match executor {
            Executor::Park => std::thread::park(),
            Executor::Spin => {
                let mut spins = 0u32;
                while !flag.0.swap(false, Ordering::Acquire) {
                    if spins < 128 {
                        std::hint::spin_loop();
                    } else {
                        std::thread::yield_now();
                    }
                    spins += 1;
                }
            }
        }
    }
}

fn uncontended(c: &mut Criterion) {
    let mut group = c.benchmark_group("sync_uncontended");
    let waker = Waker::noop();
    let mutex = Mutex::new(0u64);
    group.bench_function("regolith_mutex_try_lock", |b| {
        b.iter(|| *black_box(&mutex).try_lock().expect("free") += 1)
    });
    group.bench_function("regolith_mutex_lock_future", |b| {
        b.iter(|| {
            let mut lock = pin!(black_box(&mutex).lock());
            match lock.as_mut().poll(&mut Context::from_waker(waker)) {
                Poll::Ready(mut guard) => *guard += 1,
                Poll::Pending => unreachable!("uncontended"),
            }
        })
    });
    let rwlock = RwLock::new(0u64);
    group.bench_function("regolith_rwlock_read", |b| {
        b.iter(|| *black_box(&rwlock).try_read().expect("free"))
    });
    group.bench_function("regolith_rwlock_write", |b| {
        b.iter(|| *black_box(&rwlock).try_write().expect("free") += 1)
    });
    let semaphore = Semaphore::new(1);
    group.bench_function("regolith_semaphore_acquire", |b| {
        b.iter(|| drop(black_box(&semaphore).try_acquire(1).expect("free")))
    });
    let std_mutex = std::sync::Mutex::new(0u64);
    group.bench_function("std_mutex_lock", |b| {
        b.iter(|| *black_box(&std_mutex).lock().expect("unpoisoned") += 1)
    });
    group.finish();
}

/// Runs `per_task` ops on each of `tasks` threads and returns the wall
/// time from a common start.
fn on_threads(
    tasks: usize,
    per_task: u64,
    op: impl Fn(&Waker, &Flag) + Send + Sync + 'static,
    park: bool,
) -> Duration {
    let op = Arc::new(op);
    let start = Arc::new(std::sync::Barrier::new(tasks + 1));
    let threads: Vec<_> = (0..tasks)
        .map(|_| {
            let (op, start) = (Arc::clone(&op), Arc::clone(&start));
            std::thread::spawn(move || {
                let flag = Arc::new(Flag(AtomicBool::new(false)));
                let waker = if park {
                    Waker::from(Arc::new(Unpark(std::thread::current())))
                } else {
                    Waker::from(Arc::clone(&flag))
                };
                start.wait();
                for _ in 0..per_task {
                    op(&waker, &flag);
                }
            })
        })
        .collect();
    start.wait();
    let began = Instant::now();
    for thread in threads {
        thread.join().expect("worker");
    }
    began.elapsed()
}

/// Returns `Pending` once, waking itself, so a task suspends while it
/// holds the lock.
struct YieldOnce(bool);

impl Future for YieldOnce {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        if self.0 {
            return Poll::Ready(());
        }
        self.0 = true;
        cx.waker().wake_by_ref();
        Poll::Pending
    }
}

/// Runs `tasks` tasks of `per_task` locks each on this thread, polling
/// only the tasks whose waker fired.
fn on_one_thread(mutex: &Mutex<u64>, tasks: usize, per_task: u64) -> Duration {
    let flags: Vec<_> = (0..tasks)
        .map(|_| Arc::new(Flag(AtomicBool::new(true))))
        .collect();
    let wakers: Vec<_> = flags.iter().map(|f| Waker::from(Arc::clone(f))).collect();
    let mut futures: Vec<Pin<Box<dyn Future<Output = ()> + '_>>> = (0..tasks)
        .map(|_| {
            Box::pin(async move {
                for _ in 0..per_task {
                    let mut guard = mutex.lock().await;
                    YieldOnce(false).await;
                    *guard += 1;
                }
            }) as Pin<Box<dyn Future<Output = ()> + '_>>
        })
        .collect();
    let mut live = tasks;
    let began = Instant::now();
    while live > 0 {
        for i in 0..tasks {
            if !flags[i].0.swap(false, Ordering::Acquire) {
                continue;
            }
            if futures[i]
                .as_mut()
                .poll(&mut Context::from_waker(&wakers[i]))
                .is_ready()
            {
                live -= 1;
            }
        }
    }
    began.elapsed()
}

fn contended(c: &mut Criterion) {
    let mut group = c.benchmark_group("sync_contended");
    group.sample_size(20);
    group.measurement_time(Duration::from_secs(4));
    group.throughput(Throughput::Elements(1));
    for tasks in [2usize, 8, 32] {
        for (name, executor) in [
            ("regolith_mutex_park", Executor::Park),
            ("regolith_mutex_spin", Executor::Spin),
        ] {
            group.bench_with_input(BenchmarkId::new(name, tasks), &tasks, |b, &tasks| {
                b.iter_custom(|iters| {
                    let mutex = Arc::new(Mutex::new(0u64));
                    let per_task = (iters / tasks as u64).max(1);
                    let park = matches!(executor, Executor::Park);
                    on_threads(
                        tasks,
                        per_task,
                        move |waker, flag| {
                            *block_on(mutex.lock(), waker, flag, executor) += 1;
                        },
                        park,
                    )
                })
            });
        }
        group.bench_with_input(
            BenchmarkId::new("regolith_mutex_one_thread", tasks),
            &tasks,
            |b, &tasks| {
                b.iter_custom(|iters| {
                    let mutex = Mutex::new(0u64);
                    on_one_thread(&mutex, tasks, (iters / tasks as u64).max(1))
                })
            },
        );
        group.bench_with_input(BenchmarkId::new("std_mutex", tasks), &tasks, |b, &tasks| {
            b.iter_custom(|iters| {
                let mutex = Arc::new(std::sync::Mutex::new(0u64));
                let per_task = (iters / tasks as u64).max(1);
                on_threads(
                    tasks,
                    per_task,
                    move |_, _| {
                        *mutex.lock().expect("unpoisoned") += 1;
                    },
                    true,
                )
            })
        });
    }
    group.finish();
}

criterion_group!(benches, uncontended, contended);
criterion_main!(benches);
