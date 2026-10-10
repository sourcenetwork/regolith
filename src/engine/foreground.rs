//! Foreground jobs: `compact_range`, an ingest and a checkpoint, run as
//! background jobs instead of on the caller's call (plan 4.10).
//!
//! Each of them takes the compaction gate exclusively, which waits for every
//! background pass in flight. A caller never waits on the gate: the call
//! returns a [`JobTicket`] at once, and the job runs
//!
//! - **on the compaction worker**, when the database has one: the worker
//!   takes the gate between its own passes;
//! - **as a job on the caller's queue**, with no worker: the caller's thread
//!   runs it when it polls its [`IoQueue`](crate::IoQueue), as the I/O it
//!   asked for;
//! - **inline**, with neither: the call runs it before it returns, as the
//!   blocking calls do their own I/O.
//!
//! The ticket is completed on the queue of the thread that made the call (at
//! that queue's poll), or, for a caller with no queue, by whichever thread
//! finished the job. Close settles a job not yet run with
//! [`Error::Closed`]: the workers' queue when they stop, a queue's job in the
//! job table's sweep.

use std::io;
use std::path::PathBuf;
use std::sync::{Arc, Weak};

use super::RegolithEngine;
use super::io::job::{Delivery, Job, JobBody};
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
    work: Work,
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
    fn run(self: Box<Self>) {
        let Foreground {
            engine,
            work,
            finish,
        } = *self;
        let result = match engine.upgrade() {
            Some(engine) => engine.run_foreground(work),
            None => Err(Error::Closed),
        };
        finish.finish(result);
    }

    /// Settled without running: the database closed, or the queue that
    /// would have run it was dropped.
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
                work,
                finish: Finish {
                    completion: Arc::clone(&completion),
                    tell: queue.map_or(Tell::Here, Tell::Queue),
                },
            });
            if let Err(body) = self.compaction.lock().submit(body) {
                // The workers stopped: the database is closing.
                body.release();
            }
            return ticket;
        }
        let Some(queue) = queue else {
            // No worker and no queue: the caller runs it, as a blocking call
            // does its own I/O.
            completion.decide(self.run_foreground(work));
            completion.deliver_decided();
            return ticket;
        };
        let job = Job::new(Box::new(Foreground {
            engine: self.me.clone(),
            work,
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

    /// Do `work` on this thread: the worker, the caller's poll, or the
    /// caller itself. A panic in code the job runs for the caller (a
    /// compaction filter, a merge operator, a listener) fails the job alone.
    fn run_foreground(&self, work: Work) -> Result<(), Error> {
        let ran = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| match work {
            Work::CompactRange { lower, upper } => self
                .compact_range(Some(&lower), Some(&upper))
                .map_err(Error::from),
            Work::Ingest {
                files,
                options,
                check,
            } => self
                .ingest_external_files(&files, &options, check)
                .map_err(Error::from),
            Work::Checkpoint { target } => crate::checkpoint::create(self, &target),
        }));
        ran.unwrap_or_else(|_| {
            tracing::error!("a background job panicked");
            Err(Error::Io(io::Error::other(
                "the job panicked in code it ran on the caller's behalf, such as a compaction filter or a listener",
            )))
        })
    }
}
