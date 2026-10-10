//! Tickets: what a call that does not wait for its I/O hands back.

use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Weak};
use std::task::{Context, Poll};

use super::completion::Completion;
use crate::engine::RegolithEngine;
use crate::engine::io::job::Job;
use crate::{CommitReceipt, Error, TxResult};

/// The outcome of a [`Transaction::commit_nowait`](crate::Transaction::commit_nowait).
///
/// Ready once the commit is visible, and durable when its durability is
/// [`Immediate`](crate::DurabilityMode::Immediate), or with the reason it
/// did not commit: a conflict, a failed log write, `Closed`. Every outcome
/// comes through the ticket, a conflict included.
///
/// - **Where it completes.** A commit on a transaction with an
///   [`IoQueue`](crate::IoQueue) (named by
///   [`TxnOptions::io_queue`](crate::TxnOptions::io_queue), or by its
///   [`ReadMode::CacheOnly`](crate::ReadMode::CacheOnly)) whose outcome is
///   still owed an fsync when `commit_nowait` returns is completed on that
///   queue: at the [`IoQueue::poll`](crate::IoQueue::poll) that takes the
///   completion in, on the thread that owns the queue, and nowhere else. A
///   task awaiting the ticket is woken by that poll only. A commit whose
///   outcome is known when `commit_nowait` returns (a conflict, an
///   `Eventual` commit, a transaction with no queue, which syncs inline)
///   returns a ticket that is ready already.
/// - **Callbacks.** The transaction's own `on_commit` or `on_abort`
///   callbacks, then the database's hooks, then each [`on_complete`](Self::on_complete)
///   callback run once, on the thread that delivers the outcome (the queue's
///   owner at that poll, or the committing thread for a ticket ready at
///   return), in that order.
/// - **Dropping** a ticket never cancels the commit: it is decided and
///   written before the ticket exists, and its callbacks still run when the
///   queue delivers it. Dropping the queue instead delivers every ticket it
///   holds on the dropping thread (see [`IoQueue`](crate::IoQueue)).
///
/// It is a [`Future`] whose output is the commit's outcome; awaiting it again
/// after it was ready returns a copy of the same outcome.
pub struct CommitTicket {
    completion: Arc<Completion<TxResult<CommitReceipt>>>,
}

impl CommitTicket {
    pub(crate) fn new(completion: Arc<Completion<TxResult<CommitReceipt>>>) -> Self {
        Self { completion }
    }

    /// A completion for a commit on `engine`, with nothing decided.
    pub(crate) fn completion(
        engine: Weak<RegolithEngine>,
    ) -> Arc<Completion<TxResult<CommitReceipt>>> {
        Completion::new(engine, "CommitTicket::on_complete")
    }

    /// Whether the outcome has been delivered. Never waits.
    pub fn is_ready(&self) -> bool {
        self.completion.is_ready()
    }

    /// Run `f` once with the commit's outcome: at the poll that delivers it,
    /// on the thread that owns the ticket's queue, or at once, on this
    /// thread, if the ticket is ready already. `f` runs after the
    /// transaction's own callbacks and the database hooks. It must not block
    /// or re-enter the database; a panic in it is caught and reported to
    /// [`EventListener::on_callback_panic`](crate::EventListener::on_callback_panic),
    /// and the outcome stands.
    pub fn on_complete(&self, f: impl FnOnce(&TxResult<CommitReceipt>) + Send + 'static) {
        self.completion.on_complete(Box::new(f));
    }
}

impl Future for CommitTicket {
    type Output = TxResult<CommitReceipt>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        self.completion.poll_ready(cx).map(|outcome| match outcome {
            Ok(receipt) => Ok(*receipt),
            Err(err) => Err(err.duplicate()),
        })
    }
}

impl std::fmt::Debug for CommitTicket {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CommitTicket")
            .field("ready", &self.is_ready())
            .finish()
    }
}

/// The outcome of a foreground job: [`Db::compact_range`](crate::Db::compact_range),
/// [`Db::ingest_external_files`](crate::Db::ingest_external_files) or
/// [`Db::checkpoint`](crate::Db::checkpoint).
///
/// The call returns it at once and never waits on the compaction gate. The
/// job runs on the compaction worker when the database has one, and
/// otherwise as a job on the calling thread's [`IoQueue`](crate::IoQueue),
/// run at that queue's poll; a caller with neither runs it inline, before
/// the call returns. When it is done, the ticket is completed on the queue
/// of the thread that made the call (at that queue's poll), or, for a caller
/// with no queue, directly by whichever thread finished the job.
///
/// It is a [`Future`] whose output is the job's result; [`JobTicket::wait`]
/// blocks for it instead. Dropping a ticket cancels nothing: the job still
/// runs and its `on_complete` callbacks still run.
pub struct JobTicket {
    completion: Arc<Completion<Result<(), Error>>>,
    /// The job, when it waits on the caller's queue: [`JobTicket::wait`]
    /// runs it itself if nobody has claimed it.
    job: Option<Arc<Job>>,
}

impl JobTicket {
    pub(crate) fn new(completion: Arc<Completion<Result<(), Error>>>) -> Self {
        Self {
            completion,
            job: None,
        }
    }

    /// The ticket of `job`, a unit left on the caller's queue.
    pub(crate) fn of_job(completion: Arc<Completion<Result<(), Error>>>, job: Arc<Job>) -> Self {
        Self {
            completion,
            job: Some(job),
        }
    }

    /// A completion for a job on `engine`, with nothing decided.
    pub(crate) fn completion(engine: Weak<RegolithEngine>) -> Arc<Completion<Result<(), Error>>> {
        Completion::new(engine, "JobTicket::on_complete")
    }

    /// A ticket that is ready already with `result`.
    pub(crate) fn ready(engine: Weak<RegolithEngine>, result: Result<(), Error>) -> Self {
        let completion = Self::completion(engine);
        completion.decide(result);
        completion.deliver_decided();
        Self::new(completion)
    }

    /// Whether the job is done and its result delivered. Never waits.
    pub fn is_ready(&self) -> bool {
        self.completion.is_ready()
    }

    /// Run `f` once with the job's result: when it is delivered, or at once
    /// if the ticket is ready already. The same rules as
    /// [`CommitTicket::on_complete`] apply.
    pub fn on_complete(&self, f: impl FnOnce(&Result<(), Error>) + Send + 'static) {
        self.completion.on_complete(Box::new(f));
    }

    /// Block this thread until the job is done, and return its result: a
    /// blocking caller's way to use the ticket.
    ///
    /// A job left on this thread's [`IoQueue`](crate::IoQueue) that no poll
    /// has run yet is run here, on this thread, as a blocking call does its
    /// own I/O; one a worker or a poll runs is waited for. The ticket's
    /// delivery is unchanged: on a ticket completed on a queue, the
    /// `on_complete` callbacks still run at that queue's poll.
    pub fn wait(self) -> Result<(), Error> {
        if let Some(job) = &self.job
            && job.claim()
        {
            match self.completion.report().upgrade() {
                Some(engine) => engine.io().run_job(job),
                None => job.run(),
            }
        }
        match self.completion.wait_decided() {
            Ok(()) => Ok(()),
            Err(err) => Err(err.duplicate()),
        }
    }
}

impl Future for JobTicket {
    type Output = Result<(), Error>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        self.completion.poll_ready(cx).map(|outcome| match outcome {
            Ok(()) => Ok(()),
            Err(err) => Err(err.duplicate()),
        })
    }
}

impl std::fmt::Debug for JobTicket {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("JobTicket")
            .field("ready", &self.is_ready())
            .finish()
    }
}
