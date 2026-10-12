//! Models of parking (`engine::commit::park`): a job a queue's poll steps
//! parks instead of waiting for another thread, and nobody who waits is
//! left behind.
//!
//! Four handshakes carry it. In each, two sides write one word and then
//! read the other's, and a side that misses the other sleeps for ever:
//!
//! - a job its holder parks, against a thread blocked on it (`io::job`,
//!   K4 in `commit::park`);
//! - a job parked for a thing another thread holds, against the thread that
//!   gives the thing up (`io::parked`, PK1), driven here through the
//!   version store's step, which the flush exclusion shares the list with;
//! - a rollback parked for the writes in flight on a failed log, against
//!   the last write to leave (`wal_gate`, WG1 and WG3);
//! - the wake of a parked job telling the queues registered on it, against
//!   the thread that lands it (`io::job`, `Job::ready`).
//!
//! Each positive model drives the production type, whose atomics, fences
//! and parking are loom's under `--cfg loom`. Each calibration rebuilds the
//! handshake out of plain loom atomics with one thing wrong, and must fail
//! its assertion. A side that would sleep says so instead of sleeping, and
//! the model then asks whether anybody woke it: a thread loom finds asleep
//! for good unwinds through the model's threads and stops the test process,
//! which a calibration cannot expect. Only the first model parks for real,
//! through the job's own code.
//!
//! # What was shrunk
//!
//! Two threads a model, one parked job, one thing held, one write in
//! flight, two queues. Every model is bounded by an explicit preemption
//! bound, never by time.

use std::sync::Arc as StdArc;
use std::task::{Wake, Waker};

use loom::sync::Arc;
use loom::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use loom::thread;

use super::super::io::job::{Job, JobBody, Step as JobStep, unpark_waker};
use super::super::io::shared::{Message, QueueShared};
use super::super::io::stack::{SHUT, Stack};
use super::super::step::Step;
use super::super::wal_gate::Gate;
use super::explore_bounded;
use crate::io_queue::QueueId;

/// A body that parks whenever a poll steps it, and counts its runs.
struct Parks {
    runs: Arc<AtomicUsize>,
}

impl JobBody for Parks {
    fn run(self: Box<Self>) {
        self.runs.fetch_add(1, Ordering::SeqCst);
    }

    fn step(self: Box<Self>, _waker: &Waker) -> JobStep {
        JobStep::Parked(self)
    }

    fn release(self: Box<Self>) {}
}

fn parking_job(runs: &Arc<AtomicUsize>) -> StdArc<Job> {
    Job::new(Box::new(Parks {
        runs: Arc::clone(runs),
    }))
}

/// Counts the wakes of a parked job, as the queue it is pushed back to
/// would see them.
struct Wakes(Arc<AtomicUsize>);

impl Wake for Wakes {
    fn wake(self: StdArc<Self>) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}

fn counting() -> (Arc<AtomicUsize>, Waker) {
    let wakes = Arc::new(AtomicUsize::new(0));
    (
        Arc::clone(&wakes),
        Waker::from(StdArc::new(Wakes(Arc::clone(&wakes)))),
    )
}

fn queue(n: u64) -> StdArc<QueueShared> {
    StdArc::new(QueueShared::new(
        QueueId::new(std::num::NonZeroU64::new(n).expect("model ids start at 1")),
        1 << 20,
    ))
}

/// K4: a poll has a job when a blocking caller arrives for it, and parks
/// it. Whichever comes first, the park or the caller going to sleep, the
/// caller ends up claiming the job and running it: it is never left asleep
/// on a job nobody runs, which loom would report as a deadlock.
///
/// Bound: 3 preemptions. One job, one park, one blocked thread.
pub fn a_job_its_holder_parks_is_run_by_the_thread_that_waited() {
    explore_bounded(
        "a_job_its_holder_parks_is_run_by_the_thread_that_waited",
        Some(3),
        50,
        30,
        |witness| {
            let runs = Arc::new(AtomicUsize::new(0));
            let job = parking_job(&runs);
            assert!(job.claim(), "the poll has the job");
            let blocked = {
                let (job, witness) = (StdArc::clone(&job), witness.clone());
                thread::spawn(move || {
                    // A blocking caller's loop (`RegolithEngine::run_or_wait`).
                    loop {
                        if job.claim() {
                            job.run();
                            return;
                        }
                        if job.wait_turn() {
                            return;
                        }
                        // Told of the park, or found the job parked.
                        witness.record();
                    }
                })
            };
            assert!(!job.step(Waker::noop()), "the body parks");
            blocked.join().expect("the blocked thread");
            assert!(job.is_done());
            assert_eq!(runs.load(Ordering::SeqCst), 1, "the job ran once");
        },
    );
}

/// Calibration for [`a_job_its_holder_parks_is_run_by_the_thread_that_waited`]:
/// a waiter that registers itself and goes to sleep without looking at the
/// job again. A park that came between its failed claim and its
/// registration took an empty list, so nobody wakes it.
pub fn a_waiter_that_does_not_look_again_sleeps_on_a_parked_job() {
    const CLAIMED: usize = 1;
    const FREE: usize = 0;
    explore_bounded(
        "a_waiter_that_does_not_look_again_sleeps_on_a_parked_job",
        Some(3),
        1,
        0,
        |_| {
            let state = Arc::new(AtomicUsize::new(CLAIMED));
            let sleepers: StdArc<Stack<u8>> = StdArc::new(Stack::new());
            let waiter = {
                let (state, sleepers) = (Arc::clone(&state), StdArc::clone(&sleepers));
                thread::spawn(move || {
                    if state
                        .compare_exchange(FREE, CLAIMED, Ordering::SeqCst, Ordering::SeqCst)
                        .is_ok()
                    {
                        return false;
                    }
                    let _ = sleepers.push(1, SHUT);
                    // The bug: no second look at the state. It sleeps here.
                    true
                })
            };
            // The holder parks the job and wakes whoever registered.
            state.store(FREE, Ordering::SeqCst);
            let woken = sleepers.take_open().count();
            let slept = waiter.join().expect("the waiter");
            assert!(
                !slept || woken == 1,
                "a thread slept on a parked job with nobody left to wake it"
            );
        },
    );
}

/// PK1 through the version store's step: a job finds the step held and
/// parks, or takes it. A job that parked is woken by the thread that gave
/// the step up; one that was not woken took the step. It never parks on a
/// step nobody holds.
///
/// Bound: 3 preemptions. One hold, one job.
pub fn a_job_parked_for_the_step_is_woken_when_it_is_given_up() {
    explore_bounded(
        "a_job_parked_for_the_step_is_woken_when_it_is_given_up",
        Some(3),
        15,
        4,
        |witness| {
            let step = Arc::new(Step::new());
            let hold = step
                .hold_or_park(Waker::noop())
                .expect("nobody holds the step yet");
            let (wakes, waker) = counting();
            let job = {
                let step = Arc::clone(&step);
                thread::spawn(move || match step.hold_or_park(&waker) {
                    Some(hold) => {
                        drop(hold);
                        false
                    }
                    // Parked: nothing runs the job again until its waker.
                    None => true,
                })
            };
            drop(hold);
            let parked = job.join().expect("the job's thread");
            if parked {
                witness.record();
                assert_eq!(
                    wakes.load(Ordering::SeqCst),
                    1,
                    "a job parked for the step and was not woken when it was given up"
                );
            }
            assert!(
                step.hold_or_park(Waker::noop()).is_some(),
                "the step was left held"
            );
        },
    );
}

/// Calibration for [`a_job_parked_for_the_step_is_woken_when_it_is_given_up`]:
/// a job that registers its waker and parks without trying the step a
/// second time. A step given up between its try and its registration woke
/// nobody, and the job sleeps on a free step.
pub fn a_job_that_parks_without_a_second_try_sleeps_on_a_free_step() {
    explore_bounded(
        "a_job_that_parks_without_a_second_try_sleeps_on_a_free_step",
        Some(3),
        1,
        0,
        |_| {
            let held = Arc::new(AtomicBool::new(true));
            let parked: StdArc<Stack<u8>> = StdArc::new(Stack::new());
            let job = {
                let (held, parked) = (Arc::clone(&held), StdArc::clone(&parked));
                thread::spawn(move || {
                    if !held.swap(true, Ordering::SeqCst) {
                        return false;
                    }
                    let _ = parked.push(1, 0);
                    // The bug: no second try before the park.
                    true
                })
            };
            held.store(false, Ordering::SeqCst);
            let woken = parked.take(0).count();
            let slept = job.join().expect("the job's thread");
            assert!(
                !slept || woken == 1,
                "a job parked for the step and was not woken when it was given up"
            );
        },
    );
}

/// WG1 and WG3: a rollback moves the gate on while a write decided before
/// is, or is not yet, in flight. The write either was let in before the
/// gate moved, and then the rollback cuts only once it left (it parks,
/// and the write wakes it on its way out), or it is turned away. It never
/// lands after the cut, and the rollback never parks on a gate that is
/// clear.
///
/// Bound: 3 preemptions. One write, one rollback.
pub fn a_rollback_parked_for_a_write_in_flight_cuts_after_it_left() {
    explore_bounded(
        "a_rollback_parked_for_a_write_in_flight_cuts_after_it_left",
        Some(3),
        8,
        1,
        |witness| {
            let gate = Arc::new(Gate::new());
            let cut = Arc::new(AtomicBool::new(false));
            let writer = {
                let (gate, cut) = (Arc::clone(&gate), Arc::clone(&cut));
                thread::spawn(move || {
                    if !gate.enter(0) {
                        return false;
                    }
                    // The write's bytes go to the host here.
                    let after_the_cut = cut.load(Ordering::SeqCst);
                    gate.leave(0);
                    after_the_cut
                })
            };
            let (wakes, waker) = counting();
            gate.turn(1);
            let parked = !gate.clear_or_park(&waker);
            if !parked {
                // Nothing is in flight and nothing of the old epoch gets in.
                cut.store(true, Ordering::SeqCst);
            }
            let after_the_cut = writer.join().expect("the writer");
            assert!(
                !after_the_cut,
                "a write of a discarded commit landed after the cut"
            );
            if parked {
                witness.record();
                assert_eq!(
                    wakes.load(Ordering::SeqCst),
                    1,
                    "a rollback parked for a write in flight and was not woken when it left"
                );
                assert!(gate.clear_or_park(&waker), "the write left");
            }
        },
    );
}

/// Calibration for [`a_rollback_parked_for_a_write_in_flight_cuts_after_it_left`]:
/// a write that looks at the epoch and then counts itself in, as two
/// steps. A rollback that moved the epoch and saw nobody counted between
/// the two cuts the file under the write.
pub fn a_write_counted_in_after_its_epoch_check_lands_after_the_cut() {
    explore_bounded(
        "a_write_counted_in_after_its_epoch_check_lands_after_the_cut",
        Some(3),
        1,
        0,
        |_| {
            let epoch = Arc::new(AtomicUsize::new(0));
            let writers = Arc::new(AtomicUsize::new(0));
            let cut = Arc::new(AtomicBool::new(false));
            let writer = {
                let (epoch, writers, cut) =
                    (Arc::clone(&epoch), Arc::clone(&writers), Arc::clone(&cut));
                thread::spawn(move || {
                    // The bug: the epoch is read before the count in.
                    if epoch.load(Ordering::SeqCst) != 0 {
                        return false;
                    }
                    writers.fetch_add(1, Ordering::SeqCst);
                    let after_the_cut = cut.load(Ordering::SeqCst);
                    writers.fetch_sub(1, Ordering::SeqCst);
                    after_the_cut
                })
            };
            epoch.store(1, Ordering::SeqCst);
            if writers.load(Ordering::SeqCst) == 0 {
                cut.store(true, Ordering::SeqCst);
            }
            let after_the_cut = writer.join().expect("the writer");
            assert!(
                !after_the_cut,
                "a write of a discarded commit landed after the cut"
            );
        },
    );
}

/// `Job::ready` against a landing: the wake of a parked job takes the
/// queues registered on it off the list to tell them, while a blocking
/// caller claims the job and lands it. Each queue is told the landing
/// exactly once, by the lander or by the wake that had it off the list.
///
/// Bound: 2 preemptions. Two queues, one wake, one landing.
pub fn a_queue_off_the_list_when_the_job_lands_is_told_once() {
    explore_bounded(
        "a_queue_off_the_list_when_the_job_lands_is_told_once",
        Some(2),
        90,
        100,
        |witness| {
            let runs = Arc::new(AtomicUsize::new(0));
            let job = parking_job(&runs);
            let (stepper, other) = (queue(1), queue(2));
            assert!(job.register(StdArc::clone(&stepper)));
            assert!(job.register(StdArc::clone(&other)));
            assert!(job.claim());
            let waker = unpark_waker(&job, &stepper);
            assert!(!job.step(&waker), "the body parks");
            let waking = thread::spawn(move || waker.wake());
            let landing = {
                let job = StdArc::clone(&job);
                thread::spawn(move || {
                    assert!(job.claim(), "a parked job is free");
                    job.run();
                })
            };
            waking.join().expect("the wake");
            landing.join().expect("the landing");
            assert!(job.is_done());
            for told in [&stepper, &other] {
                let (mut ready, mut done) = (0, 0);
                for message in told.take_inbox() {
                    match message {
                        Message::Ready(_) => ready += 1,
                        Message::JobDone(_) => done += 1,
                        _ => panic!("a message no step of the model sends"),
                    }
                }
                assert_eq!(done, 1, "a queue was told the landing {done} times");
                assert!(ready <= 1, "a queue was told to go on {ready} times");
                if ready == 1 {
                    witness.record();
                }
            }
        },
    );
}

/// Calibration for [`a_queue_off_the_list_when_the_job_lands_is_told_once`]:
/// a wake that puts a queue back on the list without looking at whether
/// the list was closed meanwhile. A landing between its take and its push
/// saw no queue, and the queue is never told.
pub fn a_wake_that_registers_again_blindly_loses_a_landing() {
    explore_bounded(
        "a_wake_that_registers_again_blindly_loses_a_landing",
        Some(2),
        1,
        0,
        |_| {
            let waiters: StdArc<Stack<u8>> = StdArc::new(Stack::new());
            waiters.push(1, SHUT).expect("the list is open");
            let told = Arc::new(AtomicUsize::new(0));
            let waking = {
                let waiters = StdArc::clone(&waiters);
                thread::spawn(move || {
                    for queue in waiters.take_open() {
                        // The bug: a refused push is dropped on the floor.
                        let _ = waiters.push(queue, SHUT);
                    }
                })
            };
            for _queue in waiters.take(SHUT) {
                told.fetch_add(1, Ordering::SeqCst);
            }
            waking.join().expect("the wake");
            assert_eq!(
                told.load(Ordering::SeqCst),
                1,
                "a queue was never told the landing"
            );
        },
    );
}
