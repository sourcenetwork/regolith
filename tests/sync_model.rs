//! Property tests for `regolith::sync` against sequential models.
//!
//! Each case drives one primitive with a random schedule of acquires,
//! polls, cancellations (dropping a pending future), releases and `try_`
//! calls on a single-threaded executor, and after every step compares it
//! with a plain sequential model of the contract:
//!
//! - every `try_` call and every poll returns what the model says;
//! - a waiter's waker has fired exactly once if the model has granted it
//!   and never otherwise, so no wakeup is lost and nobody is woken for
//!   nothing;
//! - a cancelled waiter that had been granted passes its grant on.
//!
//! Single-threaded schedules cover the ordering contract; the loom models
//! in `tests/loom_sync.rs` cover the interleavings.

use std::collections::VecDeque;
use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::task::{Context, Poll, Wake, Waker};

use proptest::prelude::*;
use regolith::sync::{Mutex, Notify, RwLock, Semaphore};

struct Counter(AtomicUsize);

impl Wake for Counter {
    fn wake(self: Arc<Self>) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}

/// A future polled by hand under a waker that counts its wakes.
struct Polled<F: Future> {
    future: Pin<Box<F>>,
    counter: Arc<Counter>,
    waker: Waker,
}

impl<F: Future> Polled<F> {
    fn new(future: F) -> Self {
        let counter = Arc::new(Counter(AtomicUsize::new(0)));
        Self {
            future: Box::pin(future),
            waker: Waker::from(Arc::clone(&counter)),
            counter,
        }
    }

    fn poll(&mut self) -> Poll<F::Output> {
        self.future
            .as_mut()
            .poll(&mut Context::from_waker(&self.waker))
    }

    fn wakes(&self) -> usize {
        self.counter.0.load(Ordering::SeqCst)
    }
}

/// One step of a schedule. Indices pick among the live futures or held
/// guards, modulo how many there are.
#[derive(Clone, Debug)]
enum Step {
    Start(usize),
    Poll(usize),
    Cancel(usize),
    Release(usize),
    Try(usize),
    Add(usize),
}

fn steps() -> impl Strategy<Value = Vec<Step>> {
    let step = prop_oneof![
        3 => (1usize..4).prop_map(Step::Start),
        3 => any::<usize>().prop_map(Step::Poll),
        2 => any::<usize>().prop_map(Step::Cancel),
        3 => any::<usize>().prop_map(Step::Release),
        1 => (1usize..4).prop_map(Step::Try),
        1 => (1usize..3).prop_map(Step::Add),
    ];
    prop::collection::vec(step, 1..80)
}

fn pick(len: usize, i: usize) -> Option<usize> {
    (len != 0).then(|| i % len)
}

/// The weighted FIFO contract a semaphore keeps.
#[derive(Default)]
struct SemaphoreModel {
    free: usize,
    /// Waiting requests, oldest first: (id, permits).
    queue: VecDeque<(usize, usize)>,
    /// Granted requests whose future has not seen the grant yet.
    granted: Vec<(usize, usize)>,
}

impl SemaphoreModel {
    fn grant(&mut self) {
        while let Some(&(id, n)) = self.queue.front() {
            if self.free < n {
                break;
            }
            self.free -= n;
            self.queue.pop_front();
            self.granted.push((id, n));
        }
    }

    fn try_acquire(&mut self, n: usize) -> bool {
        let ok = self.queue.is_empty() && self.free >= n;
        if ok {
            self.free -= n;
        }
        ok
    }

    fn release(&mut self, n: usize) {
        self.free += n;
        self.grant();
    }

    fn is_granted(&self, id: usize) -> bool {
        self.granted.iter().any(|(g, _)| *g == id)
    }

    fn cancel(&mut self, id: usize) {
        if let Some(at) = self.granted.iter().position(|(g, _)| *g == id) {
            let (_, n) = self.granted.remove(at);
            self.release(n);
        } else {
            self.queue.retain(|(q, _)| *q != id);
            self.grant();
        }
    }
}

fn run_semaphore(initial: usize, schedule: &[Step], weighted: bool) -> Result<(), TestCaseError> {
    let sem = Semaphore::new(initial);
    let mut model = SemaphoreModel {
        free: initial,
        ..SemaphoreModel::default()
    };
    let mut waiting = Vec::new();
    let mut held = Vec::new();
    for (next_id, step) in schedule.iter().enumerate() {
        match *step {
            Step::Start(n) => {
                let n = if weighted { n } else { 1 };
                let ready_now = model.try_acquire(n);
                let mut future = Polled::new(sem.acquire(n));
                match future.poll() {
                    Poll::Ready(permit) => {
                        prop_assert!(ready_now, "acquired with others queued or too few free");
                        held.push(permit);
                    }
                    Poll::Pending => {
                        prop_assert!(!ready_now, "waited although the permits were free");
                        model.queue.push_back((next_id, n));
                        waiting.push((next_id, future));
                    }
                }
            }
            Step::Poll(i) => {
                if let Some(at) = pick(waiting.len(), i) {
                    let id = waiting[at].0;
                    match waiting[at].1.poll() {
                        Poll::Ready(permit) => {
                            prop_assert!(model.is_granted(id), "ready without a grant");
                            model.granted.retain(|(g, _)| *g != id);
                            held.push(permit);
                            waiting.remove(at);
                        }
                        Poll::Pending => prop_assert!(!model.is_granted(id), "granted but pending"),
                    }
                }
            }
            Step::Cancel(i) => {
                if let Some(at) = pick(waiting.len(), i) {
                    let (id, future) = waiting.remove(at);
                    drop(future);
                    model.cancel(id);
                }
            }
            Step::Release(i) => {
                if let Some(at) = pick(held.len(), i) {
                    let permit = held.remove(at);
                    model.release(permit.count());
                }
            }
            Step::Try(n) => {
                let n = if weighted { n } else { 1 };
                let expected = model.try_acquire(n);
                match sem.try_acquire(n) {
                    Some(permit) => {
                        prop_assert!(expected, "try_acquire jumped the queue");
                        held.push(permit);
                    }
                    None => prop_assert!(!expected, "try_acquire refused free permits"),
                }
            }
            Step::Add(n) => {
                sem.add_permits(n);
                model.release(n);
            }
        }
        prop_assert_eq!(sem.available_permits(), model.free);
        for (id, future) in &waiting {
            let expected = usize::from(model.is_granted(*id));
            prop_assert_eq!(future.wakes(), expected, "waiter {} woken wrongly", id);
        }
    }
    Ok(())
}

/// The phase-fair contract a reader-writer lock keeps.
#[derive(Default)]
struct RwModel {
    readers: usize,
    writer: bool,
    last_read: bool,
    waiting_readers: VecDeque<usize>,
    waiting_writers: VecDeque<usize>,
    granted: Vec<usize>,
}

impl RwModel {
    fn grant(&mut self) {
        loop {
            if self.writer {
                return;
            }
            let readers_turn = !self.last_read || self.waiting_writers.is_empty();
            if readers_turn && !self.waiting_readers.is_empty() {
                while let Some(id) = self.waiting_readers.pop_front() {
                    self.readers += 1;
                    self.granted.push(id);
                }
                self.last_read = true;
                continue;
            }
            if self.readers == 0
                && let Some(id) = self.waiting_writers.pop_front()
            {
                self.writer = true;
                self.last_read = false;
                self.granted.push(id);
            }
            return;
        }
    }

    fn try_read(&mut self) -> bool {
        let ok = !self.writer && self.waiting_writers.is_empty();
        if ok {
            self.readers += 1;
            self.last_read = true;
        }
        ok
    }

    fn try_write(&mut self) -> bool {
        let ok = !self.writer
            && self.readers == 0
            && self.waiting_writers.is_empty()
            && self.waiting_readers.is_empty();
        if ok {
            self.writer = true;
            self.last_read = false;
        }
        ok
    }
}

enum RwGuard<'a> {
    Read(regolith::sync::RwLockReadGuard<'a, ()>),
    Write(regolith::sync::RwLockWriteGuard<'a, ()>),
}

enum RwFuture<'a> {
    Read(Polled<regolith::sync::Read<'a, ()>>),
    Write(Polled<regolith::sync::Write<'a, ()>>),
}

impl<'a> RwFuture<'a> {
    fn poll(&mut self) -> Poll<RwGuard<'a>> {
        match self {
            Self::Read(f) => f.poll().map(RwGuard::Read),
            Self::Write(f) => f.poll().map(RwGuard::Write),
        }
    }

    fn wakes(&self) -> usize {
        match self {
            Self::Read(f) => f.wakes(),
            Self::Write(f) => f.wakes(),
        }
    }
}

fn run_rwlock(schedule: &[Step]) -> Result<(), TestCaseError> {
    let lock = RwLock::new(());
    let mut model = RwModel {
        last_read: true,
        ..RwModel::default()
    };
    let mut waiting: Vec<(usize, bool, RwFuture<'_>)> = Vec::new();
    let mut held: Vec<RwGuard<'_>> = Vec::new();
    for (id, step) in schedule.iter().enumerate() {
        match *step {
            Step::Start(n) => {
                let write = n == 1;
                let ready_now = if write {
                    model.try_write()
                } else {
                    model.try_read()
                };
                let mut future = if write {
                    RwFuture::Write(Polled::new(lock.write()))
                } else {
                    RwFuture::Read(Polled::new(lock.read()))
                };
                match future.poll() {
                    Poll::Ready(guard) => {
                        prop_assert!(ready_now, "entered past a waiter or a holder");
                        held.push(guard);
                    }
                    Poll::Pending => {
                        prop_assert!(!ready_now, "waited although the lock was free to it");
                        if write {
                            model.waiting_writers.push_back(id);
                        } else {
                            model.waiting_readers.push_back(id);
                        }
                        waiting.push((id, write, future));
                    }
                }
            }
            Step::Poll(i) => {
                if let Some(at) = pick(waiting.len(), i) {
                    let id = waiting[at].0;
                    match waiting[at].2.poll() {
                        Poll::Ready(guard) => {
                            prop_assert!(model.granted.contains(&id), "ready without a grant");
                            model.granted.retain(|g| *g != id);
                            held.push(guard);
                            waiting.remove(at);
                        }
                        Poll::Pending => prop_assert!(!model.granted.contains(&id)),
                    }
                }
            }
            Step::Cancel(i) => {
                if let Some(at) = pick(waiting.len(), i) {
                    let (id, write, future) = waiting.remove(at);
                    drop(future);
                    if let Some(g) = model.granted.iter().position(|g| *g == id) {
                        model.granted.remove(g);
                        if write {
                            model.writer = false;
                        } else {
                            model.readers -= 1;
                        }
                    } else {
                        model.waiting_readers.retain(|q| *q != id);
                        model.waiting_writers.retain(|q| *q != id);
                    }
                    model.grant();
                }
            }
            Step::Release(i) => {
                if let Some(at) = pick(held.len(), i) {
                    match held.remove(at) {
                        RwGuard::Read(guard) => {
                            drop(guard);
                            model.readers -= 1;
                        }
                        RwGuard::Write(guard) => {
                            drop(guard);
                            model.writer = false;
                        }
                    }
                    model.grant();
                }
            }
            Step::Try(n) => {
                if n == 1 {
                    let expected = model.try_write();
                    match lock.try_write() {
                        Some(guard) => {
                            prop_assert!(expected, "try_write overtook");
                            held.push(RwGuard::Write(guard));
                        }
                        None => prop_assert!(!expected, "try_write refused a free lock"),
                    }
                } else {
                    let expected = model.try_read();
                    match lock.try_read() {
                        Some(guard) => {
                            prop_assert!(expected, "try_read overtook a writer");
                            held.push(RwGuard::Read(guard));
                        }
                        None => prop_assert!(!expected, "try_read refused a free lock"),
                    }
                }
            }
            Step::Add(_) => {}
        }
        for (id, _, future) in &waiting {
            let expected = usize::from(model.granted.contains(id));
            prop_assert_eq!(future.wakes(), expected, "waiter {} woken wrongly", id);
        }
    }
    Ok(())
}

fn run_mutex(schedule: &[Step]) -> Result<(), TestCaseError> {
    let mutex = Mutex::new(());
    let mut model = SemaphoreModel {
        free: 1,
        ..SemaphoreModel::default()
    };
    let mut waiting = Vec::new();
    let mut held = Vec::new();
    for (id, step) in schedule.iter().enumerate() {
        match *step {
            Step::Start(_) => {
                let ready_now = model.try_acquire(1);
                let mut future = Polled::new(mutex.lock());
                match future.poll() {
                    Poll::Ready(guard) => {
                        prop_assert!(ready_now, "locked past a waiter or the holder");
                        held.push(guard);
                    }
                    Poll::Pending => {
                        prop_assert!(!ready_now, "waited on a free mutex");
                        model.queue.push_back((id, 1));
                        waiting.push((id, future));
                    }
                }
            }
            Step::Poll(i) => {
                if let Some(at) = pick(waiting.len(), i) {
                    let id = waiting[at].0;
                    match waiting[at].1.poll() {
                        Poll::Ready(guard) => {
                            prop_assert!(model.is_granted(id));
                            model.granted.clear();
                            held.push(guard);
                            waiting.remove(at);
                        }
                        Poll::Pending => prop_assert!(!model.is_granted(id)),
                    }
                }
            }
            Step::Cancel(i) => {
                if let Some(at) = pick(waiting.len(), i) {
                    let (id, future) = waiting.remove(at);
                    drop(future);
                    model.cancel(id);
                }
            }
            Step::Release(i) => {
                if pick(held.len(), i).is_some() {
                    held.clear();
                    model.release(1);
                }
            }
            Step::Try(_) => {
                let expected = model.try_acquire(1);
                match mutex.try_lock() {
                    Some(guard) => {
                        prop_assert!(expected, "try_lock barged");
                        held.push(guard);
                    }
                    None => prop_assert!(!expected, "try_lock refused a free mutex"),
                }
            }
            Step::Add(_) => {}
        }
        prop_assert!(held.len() <= 1, "two guards at once");
        for (id, future) in &waiting {
            let expected = usize::from(model.is_granted(*id));
            prop_assert_eq!(future.wakes(), expected, "waiter {} woken wrongly", id);
        }
    }
    Ok(())
}

/// Notify's contract: `notify_one` wakes the oldest waiter or stores one
/// permit; `notify_waiters` wakes everyone waiting; a dropped waiter that
/// had been handed a `notify_one` passes it on.
fn run_notify(schedule: &[Step]) -> Result<(), TestCaseError> {
    let notify = Notify::new();
    let mut permit = false;
    let mut queue: VecDeque<usize> = VecDeque::new();
    // Granted waiters, and whether a `notify_one` (rather than a
    // `notify_waiters`) granted them.
    let mut granted: Vec<(usize, bool)> = Vec::new();
    let mut waiting = Vec::new();
    for (id, step) in schedule.iter().enumerate() {
        match *step {
            Step::Start(_) => {
                let mut future = Polled::new(notify.notified());
                let ready_now = queue.is_empty() && std::mem::take(&mut permit);
                prop_assert_eq!(future.poll().is_ready(), ready_now);
                if !ready_now {
                    queue.push_back(id);
                    waiting.push((id, future));
                }
            }
            Step::Poll(i) => {
                if let Some(at) = pick(waiting.len(), i) {
                    let id = waiting[at].0;
                    let is_granted = granted.iter().any(|(g, _)| *g == id);
                    prop_assert_eq!(waiting[at].1.poll().is_ready(), is_granted);
                    if is_granted {
                        granted.retain(|(g, _)| *g != id);
                        waiting.remove(at);
                    }
                }
            }
            Step::Cancel(i) => {
                if let Some(at) = pick(waiting.len(), i) {
                    let (id, future) = waiting.remove(at);
                    drop(future);
                    queue.retain(|q| *q != id);
                    if let Some(g) = granted.iter().position(|(g, _)| *g == id) {
                        let (_, by_one) = granted.remove(g);
                        if by_one {
                            match queue.pop_front() {
                                Some(next) => granted.push((next, true)),
                                None => permit = true,
                            }
                        }
                    }
                }
            }
            Step::Release(_) | Step::Add(_) => {
                notify.notify_one();
                match queue.pop_front() {
                    Some(next) => granted.push((next, true)),
                    None => permit = true,
                }
            }
            Step::Try(_) => {
                notify.notify_waiters();
                granted.extend(queue.drain(..).map(|id| (id, false)));
            }
        }
        for (id, future) in &waiting {
            let expected = usize::from(granted.iter().any(|(g, _)| g == id));
            prop_assert_eq!(future.wakes(), expected, "waiter {} woken wrongly", id);
        }
    }
    Ok(())
}

proptest! {
    #[test]
    fn a_semaphore_follows_the_weighted_fifo_model(initial in 0usize..4, schedule in steps()) {
        run_semaphore(initial, &schedule, true)?;
    }

    #[test]
    fn a_unit_semaphore_follows_the_fifo_model(initial in 0usize..3, schedule in steps()) {
        run_semaphore(initial, &schedule, false)?;
    }

    #[test]
    fn a_mutex_follows_the_handoff_model(schedule in steps()) {
        run_mutex(&schedule)?;
    }

    #[test]
    fn a_rwlock_follows_the_phase_fair_model(schedule in steps()) {
        run_rwlock(&schedule)?;
    }

    #[test]
    fn notify_follows_its_model(schedule in steps()) {
        run_notify(&schedule)?;
    }
}
