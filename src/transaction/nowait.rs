//! `commit_nowait`: a commit that is decided and written, then hands back a
//! ticket instead of waiting for its fsync (plan 3.0, 3.16, 4.10; D43, D53).
//!
//! The commit runs exactly as [`Transaction::commit`] runs it up to the log
//! write: its `before_commit` callbacks, its validation in a commit group,
//! the group's append. What differs is the end:
//!
//! - With no queue (neither [`TxnOptions::io_queue`](super::TxnOptions::io_queue)
//!   nor a [`ReadMode::CacheOnly`](crate::ReadMode::CacheOnly) names one) the
//!   commit syncs inline, as `commit` does, and the ticket is ready.
//! - With a queue, a group that needs no fsync, or a commit decided without
//!   one (a conflict, a failed callback), is landed before the call returns,
//!   and the ticket is ready.
//! - With a queue, a group that needs an fsync is left owing it, as one unit
//!   its members' queues wait on (`engine::commit::deferred`). The ticket
//!   completes on this transaction's queue when the group lands: the
//!   outcome is resolved, and the transaction's callbacks run, at the poll
//!   that delivers it, on the queue's thread.
//!
//! Exactly one outcome per transaction, whichever way it ends: the commit
//! claim is won here as `commit` wins it, and the callbacks of the outcome
//! run once, at return for a ticket ready then, else at delivery, through the
//! same function `commit` uses (`callbacks::Ending`).

use std::sync::Arc;

use super::{LockManager, Transaction, TransactionError, TxMode, TxResult, receipt_of};
use crate::engine::io::job::Delivery;
use crate::engine::io::shared::QueueShared;
use crate::engine::{GroupSync, NowaitCommit, RegolithEngine, Settled, conclude_settled};
use crate::{CommitReceipt, CommitTicket, Error};

/// How far `commit_nowait` got before it returned.
enum Committed {
    /// The outcome is known now.
    Done(TxResult<CommitReceipt>),
    /// Decided and written; its group owes its fsync. The outcome is member
    /// `member` of `group`, delivered on `queue`.
    Pending {
        group: Arc<GroupSync>,
        member: usize,
        queue: Arc<QueueShared>,
        scan_runs_dropped: u64,
    },
}

/// The key locks a pessimistic commit holds until its outcome is delivered:
/// released then, so no transaction that takes one of them can read past a
/// commit that is written but not yet visible.
struct HeldLocks {
    manager: Arc<LockManager>,
    tx_id: u64,
    keys: Vec<Vec<u8>>,
}

impl HeldLocks {
    fn release(self) {
        for key in self.keys {
            self.manager.release(&key, self.tx_id);
        }
    }
}

impl Transaction {
    /// Commit without waiting for durability: decide and write the commit,
    /// then return a [`CommitTicket`] that completes once the commit is
    /// durable (at [`crate::DurabilityMode::Immediate`]) and visible. Every
    /// outcome comes through the ticket, a conflict included.
    ///
    /// The commit runs as [`Transaction::commit`] runs it until its group's
    /// log write: [`Transaction::prepare`] first, then validation in a commit
    /// group shared with every concurrent commit and write. It never waits for
    /// the group's fsync: a group that owes one is left owing it as one unit
    /// shared by every member's queue, which the first member thread to poll
    /// runs, and the ticket completes on this transaction's queue when it
    /// lands. A member that committed with a blocking call runs it itself.
    ///
    /// - **The queue.** The one [`TxnOptions::io_queue`](super::TxnOptions::io_queue)
    ///   names, else the one this transaction's
    ///   [`ReadMode::CacheOnly`](crate::ReadMode::CacheOnly) names. With
    ///   neither, the commit syncs inline, as `commit` does, and the ticket is
    ///   ready when this returns. A queue that is not open on this database
    ///   ends the commit with [`Error::InvalidArgument`].
    /// - **Ready at return.** A commit whose group needs no fsync (every
    ///   member at `Eventual` durability), and one decided without the group
    ///   (a conflict the early check found, a failed `before_commit`
    ///   callback), returns a ready ticket: its callbacks ran on this thread
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
    ///   validation reads the device, as the commit group's leader always
    ///   does.
    /// - **Locks and the snapshot.** The snapshot is released when this
    ///   returns. A pessimistic transaction's key locks are held until the
    ///   outcome is delivered, so no transaction that takes one reads past a
    ///   commit written but not yet visible.
    ///
    /// Dropping the ticket never cancels the commit. Dropping the queue
    /// delivers its tickets on the dropping thread (see
    /// [`IoQueue`](crate::IoQueue)).
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
                group,
                member,
                queue,
                scan_runs_dropped,
            } => {
                let locks = self.take_locks();
                self.release_resources();
                let ending = self.ending();
                let stats = engine.statistics_arc();
                let snapshot_seq = self.snapshot_seq;
                let waited = Arc::clone(&group);
                completion.resolve_with(Box::new(move || {
                    let settled = conclude_settled(
                        stats.as_deref(),
                        Settled::Pending {
                            group: waited,
                            member,
                        },
                    );
                    receipt_of(stats.as_deref(), settled, snapshot_seq, scan_runs_dropped)
                }));
                let report = Arc::downgrade(&engine);
                completion.first(Box::new(move |result| {
                    if let Some(locks) = locks {
                        locks.release();
                    }
                    if let Err(TransactionError::Conflict(conflict)) = result
                        && let Some(engine) = report.upgrade()
                    {
                        engine.notify_conflict(conflict);
                    }
                    ending.finish(true, result);
                }));
                let waiter: Arc<dyn Delivery> = Arc::clone(&completion) as Arc<dyn Delivery>;
                if !engine
                    .io()
                    .wait_on(&queue, Arc::clone(group.job()), Some(waiter))
                {
                    // The queue was dropped since this commit looked it up:
                    // its drop would have delivered the ticket on its thread,
                    // so this one does, once the group landed.
                    group.land_here(&engine);
                    completion.deliver();
                }
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
            commit,
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
            Ok(NowaitCommit::Pending { group, member }) => Committed::Pending {
                group,
                member,
                queue,
                scan_runs_dropped,
            },
            Err(err) => Committed::Done(receipt(Err(err))),
        }
    }

    /// The key locks a pessimistic transaction holds, taken out of it.
    fn take_locks(&mut self) -> Option<HeldLocks> {
        let TxMode::Pessimistic { tx_id } = self.mode else {
            return None;
        };
        let manager = Arc::clone(self.lock_manager.as_ref()?);
        let keys: Vec<Vec<u8>> = self
            .held_locks
            .drain()
            .into_iter()
            .map(|(k, ())| k)
            .collect();
        Some(HeldLocks {
            manager,
            tx_id,
            keys,
        })
    }
}
