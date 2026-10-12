//! Foreground jobs: `compact_range`, an ingest and a checkpoint, run as
//! background jobs instead of on the caller's call (plan 4.10).
//!
//! Each of them holds the compaction gate alone for part of its work
//! (`compaction_gate.rs`). A caller never waits on the gate: the call
//! returns a [`JobTicket`] at once, and the job runs
//!
//! - **on the compaction worker**, when the database has one: the worker
//!   runs one job between its own passes and waits for the gate on its own
//!   thread;
//! - **as a job on the caller's queue**, with no worker: the caller's thread
//!   runs it when it polls its [`IoQueue`](crate::IoQueue), as the I/O it
//!   asked for. The poll never waits for the gate either: while another
//!   thread holds it, the job parks on the queue, keeping its place among
//!   the gate's waiters, and the queue's owner is woken once the job may go
//!   on;
//! - **inline**, with neither: the call runs it before it returns, as the
//!   blocking calls do their own I/O, and waits for the gate on its own
//!   thread, as [`JobTicket::wait`] does for a job it runs itself.
//!
//! A job has two parts. What needs no gate comes first, with the gate free
//! for compaction: an ingest copies and validates its files, a checkpoint
//! readies its target and drains the memtables. Then the job takes the gate
//! and does the rest: the range's passes, the install, the capture and its
//! links.
//!
//! The ticket is completed on the queue of the thread that made the call (at
//! that queue's poll), or, for a caller with no queue, by whichever thread
//! finished the job. Close settles a job not yet run with
//! [`Error::Closed`]: the workers' queue when they stop, a queue's job in the
//! job table's sweep, parked or not.

use std::io;
use std::path::PathBuf;
use std::sync::{Arc, Weak};
use std::task::{Poll, Waker};

use super::RegolithEngine;
use super::compaction_gate::{Admission, Exclusive};
use super::ingest::Staged;
use super::io::job::{Delivery, Job, JobBody, Step};
use super::io::shared::{Message, QueueShared};
use crate::io_queue::completion::Completion;
use crate::{Error, IngestOptions, JobTicket};

/// Checks one column-family-prefixed key of an ingested file.
pub(crate) type KeyCheck = Box<dyn FnMut(&[u8]) -> io::Result<()> + Send>;

/// What a foreground job does.
pub(crate) enum Work {
    /// Compact every table overlapping `[lower, upper)`, both bounds column
    /// family prefixed.
    CompactRange { lower: Vec<u8>, upper: Vec<u8> },
    /// Ingest `files`, checking each key with `check`.
    Ingest {
        files: Vec<PathBuf>,
        options: IngestOptions,
        check: KeyCheck,
    },
    /// Create a checkpoint in `target`.
    Checkpoint { target: PathBuf },
}

/// A job whose part before the gate is done: what it does holding the gate.
enum Gated {
    CompactRange {
        lower: Vec<u8>,
        upper: Vec<u8>,
    },
    Ingest {
        staged: Staged,
        options: IngestOptions,
    },
    Checkpoint {
        target: PathBuf,
    },
}

/// Where a job stands.
enum Stage {
    /// Nothing done yet.
    Fresh(Work),
    /// The part before the gate is done, and the job waits to hold the gate
    /// alone, keeping its place among the gate's waiters.
    Admitting(Gated, Admission),
}

/// Where a finished job's outcome is told.
enum Tell {
    /// The job is a unit on the caller's queue: the queue tells it as the
    /// job's waiter when the job lands.
    AsWaiter,
    /// The job ran on a worker for a caller with this queue: pushed there,
    /// told at its poll.
    Queue(Arc<QueueShared>),
    /// The job ran on a worker for a caller with no queue: told on the
    /// worker.
    Here,
}

/// The job's body: the work, and how its outcome reaches the ticket.
struct Foreground {
    engine: Weak<RegolithEngine>,
    stage: Stage,
    finish: Finish,
}

/// The ticket's shared half, and where its outcome is told.
struct Finish {
    completion: Arc<Completion<Result<(), Error>>>,
    tell: Tell,
}

impl Finish {
    fn finish(self, result: Result<(), Error>) {
        self.completion.decide(result);
        match self.tell {
            Tell::AsWaiter => {}
            Tell::Queue(queue) => {
                let waiter = Arc::clone(&self.completion) as Arc<dyn Delivery>;
                // A queue dropped since the call refuses the push: its drop
                // has told everything it held, so this is told here.
                if queue.deliver(Message::Deliver(waiter)).is_err() {
                    self.completion.deliver_decided();
                }
            }
            Tell::Here => self.completion.deliver_decided(),
        }
    }
}

impl JobBody for Foreground {
    /// On a worker, or for a blocking caller: waits for the gate here.
    fn run(self: Box<Self>) {
        let Foreground {
            engine,
            stage,
            finish,
        } = *self;
        let result = match engine.upgrade() {
            Some(engine) => engine.run_foreground(stage),
            None => Err(Error::Closed),
        };
        finish.finish(result);
    }

    /// On a queue's poll: parks instead of waiting for the gate.
    fn step(self: Box<Self>, waker: &Waker) -> Step {
        let Foreground {
            engine: weak,
            stage,
            finish,
        } = *self;
        let Some(engine) = weak.upgrade() else {
            finish.finish(Err(Error::Closed));
            return Step::Done;
        };
        let (gated, mut admission) = match stage {
            Stage::Fresh(work) => match engine.before_gate(work) {
                Ok(Some(gated)) => (gated, engine.compaction_gate.admit()),
                Ok(None) => {
                    finish.finish(Ok(()));
                    return Step::Done;
                }
                Err(err) => {
                    finish.finish(Err(err));
                    return Step::Done;
                }
            },
            Stage::Admitting(gated, admission) => (gated, admission),
        };
        match admission.poll(waker) {
            Poll::Ready(gate) => {
                finish.finish(engine.under_gate(gated, gate));
                Step::Done
            }
            Poll::Pending => Step::Parked(Box::new(Foreground {
                engine: weak,
                stage: Stage::Admitting(gated, admission),
                finish,
            })),
        }
    }

    /// Settled without running: the database closed, or the queue that
    /// would have run it was dropped. Dropping the stage gives back what it
    /// holds: an ingest's staged files, and the job's place at the gate, with
    /// the gate itself if it was handed over meanwhile.
    fn release(self: Box<Self>) {
        let closed = self
            .engine
            .upgrade()
            .is_none_or(|engine| engine.is_closed());
        let result = if closed {
            Err(Error::Closed)
        } else {
            Err(Error::invalid_argument(
                "the I/O queue that would have run this job was dropped before it ran; call again",
            ))
        };
        let held_a_place = matches!(self.stage, Stage::Admitting(..));
        drop(self.stage);
        // The gate, handed to the job while it was parked, kept stopped
        // writers' steps contended: with it given back they look again
        // (`StallSignal`, relief handed back).
        if held_a_place && let Some(engine) = self.engine.upgrade() {
            engine.refresh_stall_level();
        }
        self.finish.finish(result);
    }
}

impl RegolithEngine {
    /// Start `work` without waiting for it (see the module docs), and return
    /// its ticket.
    pub(crate) fn start_foreground(&self, work: Work) -> JobTicket {
        let completion = JobTicket::completion(self.me.clone());
        let ticket = JobTicket::new(Arc::clone(&completion));
        if let Err(err) = self.ensure_writable() {
            completion.decide(Err(err.into()));
            completion.deliver_decided();
            return ticket;
        }
        let queue = self.io().current_queue();
        if self.has_worker {
            let body = Box::new(Foreground {
                engine: self.me.clone(),
                stage: Stage::Fresh(work),
                finish: Finish {
                    completion: Arc::clone(&completion),
                    tell: queue.map_or(Tell::Here, Tell::Queue),
                },
            });
            if let Err(body) = self.compaction.submit(body) {
                // The workers stopped: the database is closing.
                body.release();
            }
            return ticket;
        }
        let Some(queue) = queue else {
            // No worker and no queue: the caller runs it, as a blocking call
            // does its own I/O.
            completion.decide(self.run_foreground(Stage::Fresh(work)));
            completion.deliver_decided();
            return ticket;
        };
        let job = Job::new(Box::new(Foreground {
            engine: self.me.clone(),
            stage: Stage::Fresh(work),
            finish: Finish {
                completion: Arc::clone(&completion),
                tell: Tell::AsWaiter,
            },
        }));
        let waiter = Arc::clone(&completion) as Arc<dyn Delivery>;
        match self
            .io()
            .submit(&queue, Arc::clone(&job), Some(Arc::clone(&waiter)))
        {
            Ok(()) => JobTicket::of_job(completion, job),
            Err(job) => {
                // Not left on the queue (closing, or the queue went away):
                // settle it here and tell the ticket.
                job.release();
                waiter.deliver();
                ticket
            }
        }
    }

    /// Do a job from `stage` to its end on this thread, waiting here for the
    /// gate: the worker, a blocking caller, or the call itself.
    fn run_foreground(&self, stage: Stage) -> Result<(), Error> {
        let (gated, admission) = match stage {
            Stage::Fresh(work) => match self.before_gate(work)? {
                Some(gated) => (gated, self.compaction_gate.admit()),
                None => return Ok(()),
            },
            Stage::Admitting(gated, admission) => (gated, admission),
        };
        let gate = admission.wait()?;
        self.under_gate(gated, gate)
    }

    /// A job's part before the gate. `None` when nothing is left to do under
    /// it. A panic in code run for the caller (an ingest's key check) fails
    /// the job alone.
    fn before_gate(&self, work: Work) -> Result<Option<Gated>, Error> {
        contained(|| match work {
            Work::CompactRange { lower, upper } => {
                self.ensure_writable()?;
                Ok(Some(Gated::CompactRange { lower, upper }))
            }
            Work::Ingest {
                files,
                options,
                check,
            } => {
                let staged = self.ingest_stage(&files, &options, check)?;
                Ok((!staged.is_empty()).then_some(Gated::Ingest { staged, options }))
            }
            Work::Checkpoint { target } => {
                crate::checkpoint::prepare(self, &target)?;
                Ok(Some(Gated::Checkpoint { target }))
            }
        })
    }

    /// A job's part holding the gate, which it releases before this returns.
    /// A panic in code the job runs for the caller (a compaction filter, a
    /// merge operator, a listener) fails the job alone. Once the gate is
    /// free again, the stop it kept writers from relieving is relieved
    /// here ([`Self::relieve_after_gate`]).
    fn under_gate(&self, gated: Gated, gate: Exclusive) -> Result<(), Error> {
        // The closure owns the gate, so it is released when this returns.
        let result = contained(move || match gated {
            Gated::CompactRange { lower, upper } => self
                .compact_range(&gate, Some(&lower), Some(&upper))
                .map_err(Error::from),
            Gated::Ingest { staged, options } => self
                .ingest_install(&gate, staged, &options)
                .map_err(Error::from),
            Gated::Checkpoint { target } => crate::checkpoint::capture_into(self, gate, &target),
        });
        self.relieve_after_gate();
        result
    }

    /// Relieve a stop that a sole hold of the compaction gate, or a wait
    /// owed it, kept writers from relieving. Called once that hold or wait
    /// is over.
    ///
    /// On a database with no worker and inline compaction on, a stopped
    /// writer relieves the stop with compaction steps on its own thread. A
    /// step that finds the gate held alone, or owed to a waiter, is
    /// contended, and the writer waits for the thread in its way to relieve
    /// the stop. A foreground job holds the gate for its gated part, a job
    /// parked on a queue is owed it from the handoff to its owner's next
    /// poll, and an ingest or a checkpoint only adds L0 tables, so here that
    /// thread is this one: once the gate is released it runs the same
    /// bounded steps a stopped writer would. A stop that stays (nothing left
    /// to compact, the bound reached, a step failing) lands the waiters'
    /// unit anyway, as every piece of progress does here (`StallSignal`,
    /// relief handed back), so each writer looks again and relieves it or
    /// reports why it cannot, instead of waiting for a relief nobody is
    /// running. A step contended by another thread's work leaves the stop
    /// to that thread, which hands it back the same way.
    /// `proofs/tla/StallRelief.tla` checks that no stopped writer is left
    /// waiting once nobody is relieving.
    pub(super) fn relieve_after_gate(&self) {
        if self.has_worker || !self.inline_compaction {
            return;
        }
        let mut passes = 0usize;
        let mut idle = 0usize;
        while matches!(self.stall_state(), Some((_, true))) {
            match self.run_one_background_step() {
                Ok(super::compaction::CompactionOutcome::DidWork) => {
                    idle = 0;
                    passes += 1;
                    if passes > Self::MAX_INLINE_PASSES {
                        break;
                    }
                }
                Ok(super::compaction::CompactionOutcome::Idle) => {
                    idle += 1;
                    if idle > Self::MAX_IDLE_PASSES {
                        break;
                    }
                }
                Ok(super::compaction::CompactionOutcome::Contended) => return,
                Err(err) => {
                    tracing::debug!(error = %err, "a step relieving a stop after a job failed");
                    break;
                }
            }
        }
        // Lands the unit, the stop cleared or not.
        self.refresh_stall_level();
    }
}

#[cfg(test)]
#[path = "foreground_tests.rs"]
mod tests;

/// Run one part of a job, turning a panic in it into the job's failure.
fn contained<T>(part: impl FnOnce() -> Result<T, Error>) -> Result<T, Error> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(part)).unwrap_or_else(|_| {
        tracing::error!("a background job panicked");
        Err(Error::Io(io::Error::other(
            "the job panicked in code it ran on the caller's behalf, such as a compaction filter or a listener",
        )))
    })
}
