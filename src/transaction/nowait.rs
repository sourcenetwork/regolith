//! `commit_nowait`: a commit that is decided and written, then hands back a
//! ticket instead of waiting for its fsync (plan 3.0, 3.16, 4.10; D43, D53).
//!
//! The commit runs exactly as [`Transaction::commit`] runs it up to the log
//! write: its `before_commit` callbacks, its validation when its slot of the
//! commit ring is decided, its record's write. What differs is the end:
//!
//! - With no queue (neither [`TxnOptions::io_queue`](super::TxnOptions::io_queue)
//!   nor a [`ReadMode::CacheOnly`](crate::ReadMode::CacheOnly) names one) the
//!   commit syncs inline, as `commit` does, and the ticket is ready.
//! - With a queue, a commit that waits for no fsync, or one decided without
//!   the log (a conflict, a failed callback), is published before the call
//!   returns, and the ticket is ready.
//! - With a queue, a commit that waits for an fsync is left waiting for it:
//!   the sync is one unit every commit it covers waits on, on each
//!   committer's own queue (`engine::commit::round`). The ticket completes
//!   on this transaction's queue once the commit is published: the outcome
//!   is resolved, and the transaction's callbacks run, at the poll that
//!   delivers it, on the queue's thread.
//!
//! A pessimistic commit's key locks are released when the commit lands, by
//! the thread that lands it: the commit is applied and visible by then (and
//! durable at `Immediate`), so the next holder reads it, and no transaction
//! waits for this one's owner to poll its queue (`LockTable.tla`,
//! `IsolationAtLanding`).
//!
//! The transaction's snapshot stays pinned until the commit lands too, and
//! is let go by the same thread. A commit left behind a write stall has not
//! taken its slot, so the check of what landed above its early horizon is
//! still to come, and it reads every version above the snapshot. Unpinned,
//! a compaction meanwhile may retire a deletion newer than the snapshot
//! (there is no live snapshot below it), and the check would let through a
//! commit that conflicts with it.
//!
//! Exactly one outcome per transaction, whichever way it ends: the commit
//! claim is won here as `commit` wins it, and the callbacks of the outcome
//! run once, at return for a ticket ready then, else at delivery, through the
//! same function `commit` uses (`callbacks::Ending`).

use std::sync::{Arc, Weak};

use super::{Transaction, TransactionError, TxResult, receipt_of};
use crate::engine::io::job::Delivery;
use crate::engine::io::shared::QueueShared;
use crate::engine::{NowaitCommit, PendingCommit, RegolithEngine, SnapshotPin, conclude_settled};
use crate::{CommitReceipt, CommitTicket, Error};

/// The snapshot pin of a commit that lands later, let go by whoever lands
/// it (see the module docs).
struct LandingSnapshot {
    engine: Weak<RegolithEngine>,
    /// Taken once: a `try_lock` that finds it held means the other caller is
    /// letting it go.
    pin: crate::sync::Mutex<SnapshotPin>,
}

impl LandingSnapshot {
    fn release(&self) {
        let Some(mut pin) = self.pin.try_lock() else {
            return;
        };
        let pin = pin.take();
        // A database that is gone took its snapshot registry with it.
        if let Some(engine) = self.engine.upgrade() {
            engine.release_snapshot(pin);
        }
    }
}

impl Delivery for LandingSnapshot {
    fn deliver(&self) {
        self.release();
    }
}

/// How far `commit_nowait` got before it returned.
enum Committed {
    /// The outcome is known now.
    Done(TxResult<CommitReceipt>),
    /// Not published yet: it waits for a write stall to clear before it
    /// takes its slot, or, decided and written, for its fsync. The outcome
    /// is in `pending` once it is delivered on `queue`.
    Pending {
        pending: PendingCommit,
        queue: Arc<QueueShared>,
        scan_runs_dropped: u64,
    },
}

impl Transaction {
    /// Commit without waiting for durability: decide and write the commit,
    /// then return a [`CommitTicket`] that completes once the commit is
    /// durable (at [`crate::DurabilityMode::Immediate`]) and visible. Every
    /// outcome comes through the ticket, a conflict included.
    ///
    /// The commit runs as [`Transaction::commit`] runs it until its record
    /// is written: [`Transaction::prepare`] first, then validation in the
    /// commit pipeline, in order with every concurrent commit and write. It
    /// never waits for the log's fsync: the sync is one unit shared by the
    /// queue of every commit it covers, which the first of their threads to
    /// poll runs, and the ticket completes on this transaction's queue when
    /// it lands. A commit made with a blocking call runs it itself. Nor does
    /// it wait for anything else under way, a memtable rotation or a full
    /// commit ring: the commit is left on its queue behind that and goes on
    /// at the poll that finds it done.
    ///
    /// A write stall does not end the commit either. A commit that meets a
    /// stop trigger has not taken its place in the pipeline yet: it is left
    /// on its queue behind the stall, nothing of it is stored, and at the
    /// poll that finds the stop relieved it goes on and commits, so its
    /// ticket completes then. On a database with no worker and
    /// [`crate::Options::inline_compaction`] on, the queue's polls run the
    /// steps that relieve the stop too. A commit waiting there is told what
    /// a write arriving then is told when the stop will not clear (the
    /// database closed, the engine latched, the relief keeps failing), as
    /// its outcome.
    ///
    /// - **The queue.** The one [`TxnOptions::io_queue`](super::TxnOptions::io_queue)
    ///   names, else the one this transaction's
    ///   [`ReadMode::CacheOnly`](crate::ReadMode::CacheOnly) names. With
    ///   neither, the commit syncs inline, as `commit` does, and the ticket is
    ///   ready when this returns. A queue that is not open on this database
    ///   ends the commit with [`Error::InvalidArgument`].
    /// - **Ready at return.** A commit that waits for no fsync (it, and every
    ///   commit decided before it and not yet visible, at `Eventual`
    ///   durability), and one decided before the pipeline (a conflict the
    ///   early check found, a failed `before_commit` callback), returns a
    ///   ready ticket: its callbacks ran on this thread
    ///   before this returned.
    /// - **Completed on the queue.** Otherwise the outcome is delivered at
    ///   the [`IoQueue::poll`](crate::IoQueue::poll) of this transaction's
    ///   queue that takes it in, on that queue's thread: the transaction's
    ///   own `on_commit` or `on_abort` callbacks run then, then the database
    ///   hooks, then the ticket's `on_complete` callbacks. A conflict is
    ///   reported to the [`crate::EventListener`]s then too.
    /// - **Reads.** On a `CacheOnly` transaction the `before_commit`
    ///   callbacks' reads stay non-blocking: one that misses ends the commit
    ///   with [`TransactionError::WouldBlock`] in the ticket, and the
    ///   `on_abort` callbacks run. [`OptimisticTransactionDb::transact_async`](super::OptimisticTransactionDb::transact_async)
    ///   prepares first and waits out such a miss instead. The commit's own
    ///   validation reads only the cache too, whichever thread runs it: a
    ///   block it needs and the cache does not hold ends the commit with
    ///   [`TransactionError::WouldBlock`] in the ticket, having taken no
    ///   sequence and written nothing, and the read is on the queue.
    /// - **Locks and the snapshot.** The snapshot is released when this
    ///   returns. A pessimistic transaction's key locks are held until the
    ///   commit lands (applied and visible, and durable at `Immediate`), so
    ///   no transaction that takes one reads past a commit written but not
    ///   yet visible. They are released by the thread that lands the commit,
    ///   whether or not this transaction's queue was polled since: another
    ///   transaction never waits for this one's outcome to be delivered.
    ///
    /// Dropping the ticket never cancels the commit. Dropping the queue
    /// delivers its tickets on the dropping thread (see
    /// [`IoQueue`](crate::IoQueue)).
    ///
    /// # Example
    ///
    /// ```
    /// use regolith::{OptimisticTransactionDb, Options, TransactionError, TxnOptions};
    ///
    /// let db = OptimisticTransactionDb::open("rows", Options::memory())?;
    /// // This thread's queue: the outcomes of its commits are delivered here.
    /// let mut queue = db.db().io_queue();
    /// let on_queue = TxnOptions::new().io_queue(queue.id());
    ///
    /// let txn = db.begin(&on_queue);
    /// txn.put(b"row", b"1")?;
    /// let ticket = txn.commit_nowait();
    /// // The commit is decided and written, and the call did not wait for a
    /// // sync. `block_on` polls the queue until the ticket completes. (An
    /// // in-memory database has no sync to wait for, so here it already has.)
    /// let receipt = queue.block_on(ticket)?;
    /// assert!(receipt.seq() > 0);
    /// assert_eq!(db.db().get(b"row")?.as_deref(), Some(&b"1"[..]));
    ///
    /// // A lost race comes through the ticket too, never out of the call.
    /// let (one, two) = (db.begin(&on_queue), db.begin(&on_queue));
    /// one.put(b"row", b"one")?;
    /// two.put(b"row", b"two")?;
    /// let (one, two) = (one.commit_nowait(), two.commit_nowait());
    /// assert!(queue.block_on(one).is_ok());
    /// assert!(matches!(queue.block_on(two), Err(TransactionError::Conflict(_))));
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn commit_nowait(mut self) -> CommitTicket {
        let engine = Arc::clone(&self.engine);
        let completion = CommitTicket::completion(Arc::downgrade(&engine));
        // `close` may have aborted the transaction since it began: the commit
        // is then refused, and `close` ran the abort callbacks.
        let claimed = self.claim.as_ref().is_none_or(|claim| claim.begin_commit());
        self.committing = claimed;
        self.nowait = true;
        let committed = if claimed {
            self.commit_nowait_inner(&engine)
        } else {
            Committed::Done(Err(Error::Closed.into()))
        };
        self.resolved = true;
        match committed {
            Committed::Done(result) => {
                // As `commit` ends: locks and snapshot first, so a callback
                // holds nothing of this transaction.
                self.release_resources();
                if let Err(TransactionError::Conflict(conflict)) = &result {
                    engine.notify_conflict(conflict);
                }
                self.finish(claimed, &result);
                completion.decide(result);
                completion.deliver_decided();
            }
            Committed::Pending {
                pending,
                queue,
                scan_runs_dropped,
            } => {
                let locks = self.take_landing_locks();
                let snapshot = Arc::new(LandingSnapshot {
                    engine: Arc::downgrade(&engine),
                    pin: crate::sync::Mutex::new(self.snapshot_pin.take()),
                });
                self.release_resources();
                let ending = self.ending();
                let stats = engine.statistics_arc();
                let snapshot_seq = self.snapshot_seq;
                let pending = Arc::new(pending);
                let waited = Arc::clone(&pending);
                completion.resolve_with(Box::new(move || {
                    let settled = waited
                        .settled(stats.as_deref())
                        .and_then(|settled| conclude_settled(stats.as_deref(), settled));
                    receipt_of(stats.as_deref(), settled, snapshot_seq, scan_runs_dropped)
                }));
                let report = Arc::downgrade(&engine);
                completion.first(Box::new(move |result| {
                    if let Err(TransactionError::Conflict(conflict)) = result
                        && let Some(engine) = report.upgrade()
                    {
                        engine.notify_conflict(conflict);
                    }
                    ending.finish(true, result);
                }));
                // Told by whichever thread lands the commit, on that thread;
                // a commit that landed already refuses, and they go now.
                if let Some(locks) = locks
                    && !pending.listen(Arc::clone(&locks) as Arc<dyn Delivery>)
                {
                    locks.release();
                }
                if !pending.listen(Arc::clone(&snapshot) as Arc<dyn Delivery>) {
                    snapshot.release();
                }
                let waiter: Arc<dyn Delivery> = Arc::clone(&completion) as Arc<dyn Delivery>;
                // Told on the queue once the commit is published. A queue
                // dropped since this commit looked it up would have
                // delivered the ticket on its thread, so this one does,
                // once the commit was brought through.
                engine.await_commit(&pending, &queue, waiter);
            }
        }
        CommitTicket::new(completion)
    }

    /// The commit up to the point it returns: the claim was won.
    fn commit_nowait_inner(&mut self, engine: &Arc<RegolithEngine>) -> Committed {
        let queue = match self.io_queue() {
            None => None,
            Some(id) => match engine.io().queue(id) {
                Some(queue) => Some(queue),
                None => {
                    return Committed::Done(Err(Error::invalid_argument(
                        "the I/O queue this transaction names is not open on this database",
                    )
                    .into()));
                }
            },
        };
        if let Err(err) = self.prepare() {
            return Committed::Done(Err(err));
        }
        let super::Drained {
            mut commit,
            write_free,
            scan_runs_dropped,
            _contain,
        } = match self.drain_for_commit() {
            Ok(drained) => drained,
            Err(err) => return Committed::Done(Err(err)),
        };
        let stats = engine.statistics();
        let receipt = |outcome| receipt_of(stats, outcome, self.snapshot_seq, scan_runs_dropped);
        if write_free {
            return Committed::Done(receipt(engine.commit_write_free(&commit.checks)));
        }
        // A `CacheOnly` handle never reads the device, in its commit's own
        // validation either.
        commit.read_queue = self.read_mode().queue();
        let Some(queue) = queue else {
            // No queue to complete on: the commit syncs inline.
            return Committed::Done(receipt(engine.commit_with_conflict_check(
                commit.checks,
                commit.point_ops,
                commit.range_deletes,
                commit.merges,
                commit.appends,
                commit.durability,
            )));
        };
        match engine.commit_optimistic_nowait(commit) {
            Ok(NowaitCommit::Done(outcome)) => Committed::Done(receipt(Ok(outcome))),
            Ok(NowaitCommit::Pending(pending)) => Committed::Pending {
                pending,
                queue,
                scan_runs_dropped,
            },
            Err(err) => Committed::Done(receipt(Err(err))),
        }
    }
}
