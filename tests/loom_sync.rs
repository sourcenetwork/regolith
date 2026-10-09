//! Loom models for `regolith::sync`.
//!
//! ```text
//! RUSTFLAGS="--cfg loom" cargo test --release --test loom_sync
//! ```
//!
//! Under `--cfg loom` every atomic and protocol cell in the primitives is
//! loom's instrumented one, so these models check the wait protocol itself
//! (the arrival stack, the drain role, the waiter state machine, the
//! waker slot and the per-primitive state words) under every interleaving
//! loom reaches within the preemption bound. What each model proves:
//!
//! - **Mutual exclusion**: the guarded value is a `loom::cell::UnsafeCell`,
//!   so two holders at once fail the model as a data race.
//! - **No lost wakeup**: every wait goes through `loom::future::block_on`,
//!   which parks the loom thread until its waker fires; a wakeup that is
//!   never delivered leaves every thread parked and loom reports the
//!   deadlock.
//! - **FIFO handoff and phase fairness**: waiters queue in a known order
//!   (each one's first poll is seen to return `Pending` before the next
//!   starts) and record the order they are granted in.
//! - **Cancellation at every await point**: a future polled once and then
//!   dropped races the release that may hand it the lock; whatever it was
//!   given must reach the next waiter.
//! - **Reentrancy depth**: an owner nests and unwinds while another owner
//!   waits.
//!
//! The waiter-node free list is a pass-through to the allocator under
//! loom (see `Pool`), so node recycling itself is covered by miri and the
//! unit tests rather than here. Two calibration models deliberately get
//! something wrong and must fail; without them a search that never
//! reached the bad interleaving would pass for the same reason a broken
//! one does.

#![cfg(loom)]

use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicUsize as StdAtomicUsize, Ordering as StdOrdering};
use std::task::{Context, Poll};

use loom::cell::UnsafeCell;
use loom::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use loom::sync::{Arc, Notify as Park};
use loom::thread;

use regolith::sync::{
    Barrier, Event, Latch, Mutex, Notify, OnceCell, Owner, ReentrantMutex, ReentrantRwLock, RwLock,
    Semaphore,
};

/// Runs `model` under loom with at most `preemptions` preemptions per
/// schedule (`LOOM_MAX_PREEMPTIONS` overrides it) and fails it if the
/// search was implausibly small. Three-thread models take two
/// preemptions, two-thread models three: past that the searches run for
/// hours without reaching a new kind of interleaving.
fn explore(
    name: &str,
    preemptions: usize,
    min_interleavings: usize,
    model: impl Fn() + Sync + Send + 'static,
) {
    let runs = std::sync::Arc::new(StdAtomicUsize::new(0));
    let counted = {
        let runs = std::sync::Arc::clone(&runs);
        move || {
            model();
            runs.fetch_add(1, StdOrdering::Relaxed);
        }
    };
    let mut builder = loom::model::Builder::new();
    builder.preemption_bound = builder.preemption_bound.or(Some(preemptions));
    builder.check(counted);
    let explored = runs.load(StdOrdering::Relaxed);
    println!("loom model {name}: {explored} interleavings explored");
    assert!(
        explored >= min_interleavings,
        "{name} explored only {explored} interleavings, below the {min_interleavings} floor"
    );
}

struct Unpark(Park);

impl std::task::Wake for Unpark {
    fn wake(self: std::sync::Arc<Self>) {
        self.0.notify();
    }

    fn wake_by_ref(self: &std::sync::Arc<Self>) {
        self.0.notify();
    }
}

/// Drives `future` on this loom thread, parking it between polls until
/// its waker fires. A wakeup that never comes parks it for good, which
/// loom reports as a deadlock.
fn block_on<F: Future>(future: F) -> F::Output {
    let park = std::sync::Arc::new(Unpark(Park::new()));
    let waker = std::task::Waker::from(std::sync::Arc::clone(&park));
    let mut cx = Context::from_waker(&waker);
    let mut future = std::pin::pin!(future);
    loop {
        if let Poll::Ready(output) = future.as_mut().poll(&mut cx) {
            return output;
        }
        park.0.wait();
    }
}

/// Raises `flag` once the wrapped future's first poll returned `Pending`,
/// so another thread can queue strictly behind it.
struct FlagWhenQueued<F> {
    inner: Pin<Box<F>>,
    flag: Arc<AtomicBool>,
    polled: bool,
}

impl<F: Future> Future for FlagWhenQueued<F> {
    type Output = F::Output;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<F::Output> {
        let out = self.inner.as_mut().poll(cx);
        if !self.polled {
            self.polled = true;
            if out.is_pending() {
                self.flag.store(true, Ordering::Release);
            }
        }
        out
    }
}

fn flag_when_queued<F: Future>(inner: F, flag: &Arc<AtomicBool>) -> FlagWhenQueued<F> {
    FlagWhenQueued {
        inner: Box::pin(inner),
        flag: Arc::clone(flag),
        polled: false,
    }
}

fn wait_for(flag: &AtomicBool) {
    while !flag.load(Ordering::Acquire) {
        thread::yield_now();
    }
}

/// Polls `future` once with a waker that does nothing, then drops it.
fn poll_once_then_drop<F: Future>(future: F) -> bool {
    let mut future = Box::pin(future);
    let pending = future
        .as_mut()
        .poll(&mut Context::from_waker(std::task::Waker::noop()))
        .is_pending();
    drop(future);
    pending
}

fn bump(cell: &UnsafeCell<usize>) {
    cell.with_mut(|value| unsafe { *value += 1 });
}

fn read(cell: &UnsafeCell<usize>) -> usize {
    cell.with(|value| unsafe { *value })
}

#[test]
fn mutex_excludes_and_loses_no_wakeup() {
    explore("mutex_excludes_and_loses_no_wakeup", 2, 10, || {
        let mutex = Arc::new(Mutex::new(UnsafeCell::new(0usize)));
        let others: Vec<_> = (0..2)
            .map(|_| {
                let mutex = Arc::clone(&mutex);
                thread::spawn(move || bump(&block_on(mutex.lock())))
            })
            .collect();
        bump(&block_on(mutex.lock()));
        for other in others {
            other.join().expect("locker");
        }
        assert_eq!(read(&mutex.try_lock().expect("free at the end")), 3);
    });
}

#[test]
fn mutex_hands_off_in_arrival_order() {
    explore("mutex_hands_off_in_arrival_order", 2, 5, || {
        let mutex = Arc::new(Mutex::new(Vec::new()));
        let held = mutex.try_lock().expect("free");
        let (first_queued, second_queued) = (
            Arc::new(AtomicBool::new(false)),
            Arc::new(AtomicBool::new(false)),
        );
        let first = {
            let (mutex, flag) = (Arc::clone(&mutex), Arc::clone(&first_queued));
            thread::spawn(move || block_on(flag_when_queued(mutex.lock(), &flag)).push(1))
        };
        wait_for(&first_queued);
        let second = {
            let (mutex, flag) = (Arc::clone(&mutex), Arc::clone(&second_queued));
            thread::spawn(move || block_on(flag_when_queued(mutex.lock(), &flag)).push(2))
        };
        wait_for(&second_queued);
        assert!(mutex.try_lock().is_none(), "try_lock overtook the queue");
        drop(held);
        first.join().expect("first");
        second.join().expect("second");
        assert_eq!(*mutex.try_lock().expect("free"), vec![1, 2]);
    });
}

#[test]
fn a_cancelled_mutex_waiter_racing_the_handoff_loses_nothing() {
    explore(
        "a_cancelled_mutex_waiter_racing_the_handoff_loses_nothing",
        2,
        10,
        || {
            let mutex = Arc::new(Mutex::new(UnsafeCell::new(0usize)));
            let held = mutex.try_lock().expect("free");
            let canceller = {
                let mutex = Arc::clone(&mutex);
                thread::spawn(move || poll_once_then_drop(mutex.lock()))
            };
            let waiter = {
                let mutex = Arc::clone(&mutex);
                thread::spawn(move || bump(&block_on(mutex.lock())))
            };
            drop(held);
            canceller.join().expect("canceller");
            waiter.join().expect("waiter");
            assert_eq!(read(&mutex.try_lock().expect("the lock was not leaked")), 1);
        },
    );
}

#[test]
fn a_semaphore_serves_a_large_request_before_a_smaller_one_behind_it() {
    explore(
        "a_semaphore_serves_a_large_request_before_a_smaller_one_behind_it",
        2,
        5,
        || {
            let sem = Arc::new(Semaphore::new(2));
            let order = Arc::new(std::sync::Mutex::new(Vec::new()));
            let held = sem.try_acquire(2).expect("free");
            let queued = Arc::new(AtomicBool::new(false));
            let big = {
                let (sem, order, flag) =
                    (Arc::clone(&sem), Arc::clone(&order), Arc::clone(&queued));
                thread::spawn(move || {
                    let permit = block_on(flag_when_queued(sem.acquire(2), &flag));
                    order.lock().expect("order").push(2);
                    drop(permit);
                })
            };
            wait_for(&queued);
            let small = {
                let (sem, order) = (Arc::clone(&sem), Arc::clone(&order));
                thread::spawn(move || {
                    let _permit = block_on(sem.acquire(1));
                    order.lock().expect("order").push(1);
                })
            };
            drop(held);
            big.join().expect("big");
            small.join().expect("small");
            assert_eq!(*order.lock().expect("order"), vec![2, 1]);
            assert_eq!(sem.available_permits(), 2);
        },
    );
}

#[test]
fn a_rwlock_admits_waiting_readers_before_the_next_writer() {
    explore(
        "a_rwlock_admits_waiting_readers_before_the_next_writer",
        2,
        5,
        || {
            let lock = Arc::new(RwLock::new(UnsafeCell::new(0usize)));
            let order = Arc::new(std::sync::Mutex::new(Vec::new()));
            let held = lock.try_write().expect("free");
            let reader_queued = Arc::new(AtomicBool::new(false));
            let reader = {
                let (lock, order, flag) = (
                    Arc::clone(&lock),
                    Arc::clone(&order),
                    Arc::clone(&reader_queued),
                );
                thread::spawn(move || {
                    let guard = block_on(flag_when_queued(lock.read(), &flag));
                    order.lock().expect("order").push("read");
                    read(&guard);
                })
            };
            wait_for(&reader_queued);
            let writer = {
                let (lock, order) = (Arc::clone(&lock), Arc::clone(&order));
                thread::spawn(move || {
                    let guard = block_on(lock.write());
                    order.lock().expect("order").push("write");
                    bump(&guard);
                })
            };
            drop(held);
            reader.join().expect("reader");
            writer.join().expect("writer");
            let order = order.lock().expect("order").clone();
            // The writer may have arrived after the handoff, but it never
            // overtakes the reader that waited through the writer phase.
            assert_eq!(order[0], "read", "{order:?}");
            assert_eq!(read(&lock.try_read().expect("free")), 1);
        },
    );
}

#[test]
fn a_rwlock_writer_and_readers_exclude_each_other() {
    explore(
        "a_rwlock_writer_and_readers_exclude_each_other",
        2,
        10,
        || {
            let lock = Arc::new(RwLock::new(UnsafeCell::new(0usize)));
            let writer = {
                let lock = Arc::clone(&lock);
                thread::spawn(move || bump(&block_on(lock.write())))
            };
            let reader = {
                let lock = Arc::clone(&lock);
                thread::spawn(move || {
                    let _ = read(&block_on(lock.read()));
                })
            };
            let _ = read(&block_on(lock.read()));
            writer.join().expect("writer");
            reader.join().expect("reader");
            assert_eq!(read(&lock.try_write().expect("free")), 1);
        },
    );
}

#[test]
fn a_reentrant_mutex_unwinds_its_depth_before_another_owner_enters() {
    explore(
        "a_reentrant_mutex_unwinds_its_depth_before_another_owner_enters",
        3,
        5,
        || {
            let lock = Arc::new(ReentrantMutex::new(UnsafeCell::new(0usize)));
            let other = {
                let lock = Arc::clone(&lock);
                thread::spawn(move || {
                    let owner = Owner::new();
                    bump(&block_on(lock.lock(&owner)));
                })
            };
            let owner = Owner::new();
            let outer = block_on(lock.lock(&owner));
            let inner = block_on(lock.lock(&owner));
            bump(&inner);
            drop(inner);
            bump(&outer);
            drop(outer);
            other.join().expect("other owner");
            assert_eq!(read(&lock.try_lock(&owner).expect("free")), 3);
        },
    );
}

#[test]
fn a_reentrant_reader_never_waits_behind_a_writer_waiting_for_it() {
    explore(
        "a_reentrant_reader_never_waits_behind_a_writer_waiting_for_it",
        3,
        5,
        || {
            let lock = Arc::new(ReentrantRwLock::new(AtomicUsize::new(0)));
            let owner = Owner::new();
            let first = lock.try_read(&owner).expect("free");
            let writer = {
                let lock = Arc::clone(&lock);
                thread::spawn(move || {
                    let owner = Owner::new();
                    block_on(lock.write(&owner)).fetch_add(1, Ordering::Relaxed);
                })
            };
            let second = block_on(lock.read(&owner));
            drop(first);
            drop(second);
            writer.join().expect("writer");
            assert_eq!(
                lock.try_read(&owner).expect("free").load(Ordering::Relaxed),
                1
            );
        },
    );
}

#[test]
fn notify_one_is_never_lost() {
    explore("notify_one_is_never_lost", 3, 5, || {
        let notify = Arc::new(Notify::new());
        let waiter = {
            let notify = Arc::clone(&notify);
            thread::spawn(move || block_on(notify.notified()))
        };
        notify.notify_one();
        waiter.join().expect("waiter");
    });
}

#[test]
fn notify_waiters_reaches_a_registered_waiter() {
    explore("notify_waiters_reaches_a_registered_waiter", 3, 3, || {
        let notify = Arc::new(Notify::new());
        let queued = Arc::new(AtomicBool::new(false));
        let waiter = {
            let (notify, flag) = (Arc::clone(&notify), Arc::clone(&queued));
            thread::spawn(move || block_on(flag_when_queued(notify.notified(), &flag)))
        };
        wait_for(&queued);
        notify.notify_waiters();
        waiter.join().expect("waiter");
    });
}

#[test]
fn a_dropped_notified_passes_its_notify_one_on() {
    explore("a_dropped_notified_passes_its_notify_one_on", 2, 5, || {
        let notify = Arc::new(Notify::new());
        // Returns true when its one poll completed, which consumes the
        // notification legitimately rather than dropping it.
        let canceller = {
            let notify = Arc::clone(&notify);
            thread::spawn(move || !poll_once_then_drop(notify.notified()))
        };
        let waiter = {
            let notify = Arc::clone(&notify);
            thread::spawn(move || block_on(notify.notified()))
        };
        notify.notify_one();
        if canceller.join().expect("canceller") {
            notify.notify_one();
        }
        waiter.join().expect("waiter");
    });
}

#[test]
fn an_event_set_concurrently_with_waits_wakes_them() {
    explore(
        "an_event_set_concurrently_with_waits_wakes_them",
        2,
        5,
        || {
            let event = Arc::new(Event::new());
            let waiters: Vec<_> = (0..2)
                .map(|_| {
                    let event = Arc::clone(&event);
                    thread::spawn(move || block_on(event.wait()))
                })
                .collect();
            event.set();
            for waiter in waiters {
                waiter.join().expect("waiter");
            }
        },
    );
}

#[test]
fn a_latch_opens_after_concurrent_count_downs() {
    explore("a_latch_opens_after_concurrent_count_downs", 2, 5, || {
        let latch = Arc::new(Latch::new(2));
        let counters: Vec<_> = (0..2)
            .map(|_| {
                let latch = Arc::clone(&latch);
                thread::spawn(move || latch.count_down())
            })
            .collect();
        block_on(latch.wait());
        for counter in counters {
            counter.join().expect("counter");
        }
        assert_eq!(latch.count(), 0);
    });
}

#[test]
fn a_barrier_releases_both_with_one_leader() {
    explore("a_barrier_releases_both_with_one_leader", 3, 5, || {
        let barrier = Arc::new(Barrier::new(2));
        let other = {
            let barrier = Arc::clone(&barrier);
            thread::spawn(move || block_on(barrier.wait()).is_leader())
        };
        let mine = block_on(barrier.wait()).is_leader();
        let theirs = other.join().expect("other");
        assert!(mine ^ theirs, "exactly one leader");
    });
}

#[test]
fn once_cell_initializers_agree_on_one_value() {
    explore("once_cell_initializers_agree_on_one_value", 3, 5, || {
        let cell = Arc::new(OnceCell::new());
        let racer = {
            let cell = Arc::clone(&cell);
            thread::spawn(move || *cell.get_or_init_racy(|| 1))
        };
        let mine = *block_on(cell.get_or_init(async { 2 }));
        assert_eq!(racer.join().expect("racer"), mine);
    });
}

#[test]
fn a_cancelled_rwlock_writer_racing_the_last_reader_loses_nothing() {
    explore(
        "a_cancelled_rwlock_writer_racing_the_last_reader_loses_nothing",
        2,
        10,
        || {
            let lock = Arc::new(RwLock::new(UnsafeCell::new(0usize)));
            let held = lock.try_read().expect("free");
            let canceller = {
                let lock = Arc::clone(&lock);
                thread::spawn(move || poll_once_then_drop(lock.write()))
            };
            let writer = {
                let lock = Arc::clone(&lock);
                thread::spawn(move || bump(&block_on(lock.write())))
            };
            drop(held);
            canceller.join().expect("canceller");
            writer.join().expect("writer");
            assert_eq!(read(&lock.try_write().expect("the lock was not leaked")), 1);
        },
    );
}

#[test]
fn a_reentrant_reader_upgrades_once_the_other_reader_leaves() {
    explore(
        "a_reentrant_reader_upgrades_once_the_other_reader_leaves",
        3,
        5,
        || {
            let lock = Arc::new(ReentrantRwLock::new(AtomicUsize::new(0)));
            let owner = Owner::new();
            let mine = lock.try_read(&owner).expect("free");
            let other = {
                let lock = Arc::clone(&lock);
                thread::spawn(move || {
                    let owner = Owner::new();
                    if let Some(read) = lock.try_read(&owner) {
                        read.load(Ordering::Relaxed);
                    }
                })
            };
            block_on(lock.write(&owner)).fetch_add(1, Ordering::Relaxed);
            drop(mine);
            other.join().expect("other reader");
            assert_eq!(
                lock.try_write(&Owner::new())
                    .expect("free")
                    .load(Ordering::Relaxed),
                1
            );
        },
    );
}

#[test]
fn a_cancelled_once_cell_initializer_hands_the_turn_on() {
    explore(
        "a_cancelled_once_cell_initializer_hands_the_turn_on",
        3,
        5,
        || {
            let cell = Arc::new(OnceCell::new());
            let quitter = {
                let cell = Arc::clone(&cell);
                thread::spawn(move || poll_once_then_drop(cell.get_or_init(std::future::pending())))
            };
            assert_eq!(*block_on(cell.get_or_init(async { 2 })), 2);
            quitter.join().expect("quitter");
        },
    );
}

#[test]
fn a_set_wakes_a_waiter_queued_behind_a_running_initializer() {
    explore(
        "a_set_wakes_a_waiter_queued_behind_a_running_initializer",
        3,
        5,
        || {
            let cell = Arc::new(OnceCell::new());
            let mut stuck = Box::pin(cell.get_or_init(std::future::pending()));
            assert!(
                stuck
                    .as_mut()
                    .poll(&mut Context::from_waker(std::task::Waker::noop()))
                    .is_pending()
            );
            let waiter = {
                let cell = Arc::clone(&cell);
                thread::spawn(move || *block_on(cell.get_or_init(async { 2 })))
            };
            assert_eq!(cell.set(1), Ok(()));
            assert_eq!(waiter.join().expect("waiter"), 1);
            drop(stuck);
        },
    );
}

#[test]
fn a_dropped_barrier_wait_stays_counted_while_its_generation_completes() {
    explore(
        "a_dropped_barrier_wait_stays_counted_while_its_generation_completes",
        3,
        5,
        || {
            let barrier = Arc::new(Barrier::new(2));
            let mut first = Box::pin(barrier.wait());
            assert!(
                first
                    .as_mut()
                    .poll(&mut Context::from_waker(std::task::Waker::noop()))
                    .is_pending()
            );
            let second = {
                let barrier = Arc::clone(&barrier);
                thread::spawn(move || block_on(barrier.wait()).is_leader())
            };
            drop(first);
            assert!(
                second.join().expect("second"),
                "the dropped arrival still counts, so the second completes the pair"
            );
            // The next generation starts clean.
            let third = {
                let barrier = Arc::clone(&barrier);
                thread::spawn(move || block_on(barrier.wait()).is_leader())
            };
            let fourth = block_on(barrier.wait()).is_leader();
            assert!(third.join().expect("third") ^ fourth, "exactly one leader");
        },
    );
}

#[test]
fn a_cancelled_event_wait_racing_the_set_strands_nobody() {
    explore(
        "a_cancelled_event_wait_racing_the_set_strands_nobody",
        2,
        5,
        || {
            let event = Arc::new(Event::new());
            let canceller = {
                let event = Arc::clone(&event);
                thread::spawn(move || poll_once_then_drop(event.wait()))
            };
            let waiter = {
                let event = Arc::clone(&event);
                thread::spawn(move || block_on(event.wait()))
            };
            event.set();
            canceller.join().expect("canceller");
            waiter.join().expect("waiter");
        },
    );
}

#[test]
#[should_panic(expected = "Causality violation")]
fn calibration_an_unguarded_write_is_caught() {
    explore("calibration_an_unguarded_write_is_caught", 3, 1, || {
        let cell = Arc::new(UnsafeCell::new(0usize));
        let other = {
            let cell = Arc::clone(&cell);
            thread::spawn(move || bump(&cell))
        };
        bump(&cell);
        other.join().expect("other");
    });
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn calibration_the_reverse_order_is_never_granted() {
    explore(
        "calibration_the_reverse_order_is_never_granted",
        3,
        1,
        || {
            let mutex = Arc::new(Mutex::new(Vec::new()));
            let held = mutex.try_lock().expect("free");
            let first_queued = Arc::new(AtomicBool::new(false));
            let first = {
                let (mutex, flag) = (Arc::clone(&mutex), Arc::clone(&first_queued));
                thread::spawn(move || block_on(flag_when_queued(mutex.lock(), &flag)).push(1))
            };
            wait_for(&first_queued);
            let second = {
                let mutex = Arc::clone(&mutex);
                thread::spawn(move || block_on(mutex.lock()).push(2))
            };
            drop(held);
            first.join().expect("first");
            second.join().expect("second");
            assert_eq!(*mutex.try_lock().expect("free"), vec![2, 1]);
        },
    );
}
