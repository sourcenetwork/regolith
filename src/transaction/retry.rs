//! Bounded retries owned by regolith: [`OptimisticTransactionDb::transact`]
//! and [`TransactionDb::transact`] run a closure in a transaction, commit it,
//! and run it again when the commit loses a race.
//!
//! A re-run starts at once. A one-winner race resolves on the re-run, which
//! sees the winner, so nothing sleeps. The closure receives the [`Conflict`]
//! the previous attempt lost to, so it can resolve the race instead of
//! redoing the same work blindly.
//!
//! [`OptimisticTransactionDb::transact_async`] is the same contract for a
//! caller that must never block: each attempt reads through a
//! `CacheOnly` handle on the caller's queue, a block-cache miss suspends the
//! attempt on its wait instead of ending it, and the commit goes through
//! `commit_nowait`, whose ticket the attempt awaits. It needs no runtime: the
//! caller's executor polls the future, and the caller's thread polls its
//! queue when it has nothing else to run ([`crate::IoQueue::block_on`] does
//! both).

use super::{OptimisticTransactionDb, TransactionDb, TxnOptions};
use crate::{
    CommitReceipt, Conflict, QueueId, ReadMode, Transaction, TransactionError, TxResult, WouldBlock,
};

/// Attempts [`RetryPolicy::default`] allows, the first included.
// vertexia: provisional until the contention benchmarks measure how many
// re-runs a one-winner race needs; set it from that depth.
const DEFAULT_MAX_ATTEMPTS: u32 = 8;

/// How many times `transact` runs its closure before giving up on a conflict.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct RetryPolicy {
    max_attempts: u32,
}

impl RetryPolicy {
    /// Allow `max_attempts` runs of the closure, the first included. Zero is
    /// taken as one: the closure always runs once.
    pub fn new(max_attempts: u32) -> Self {
        Self {
            max_attempts: max_attempts.max(1),
        }
    }

    /// The most times the closure runs, the first included.
    pub fn max_attempts(&self) -> u32 {
        self.max_attempts
    }
}

impl Default for RetryPolicy {
    fn default() -> Self {
        Self::new(DEFAULT_MAX_ATTEMPTS)
    }
}

/// Why [`OptimisticTransactionDb::transact`] or [`TransactionDb::transact`]
/// returned no value. `E` is the closure's own error type.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum TransactError<E> {
    /// The closure returned an error. The attempt ended with it and was not
    /// retried.
    #[error("{0}")]
    Closure(E),
    /// Every attempt lost its commit to a conflict; this is the last one.
    #[error("{0}")]
    Exhausted(Conflict),
    /// The commit failed for a reason a re-run cannot fix.
    #[error(transparent)]
    Engine(TransactionError),
}

/// Run `f` in a transaction from `begin`, committing it, and again after each
/// conflict until `policy` runs out. The one loop both databases share.
fn run<T, E>(
    policy: &RetryPolicy,
    begin: impl Fn() -> Transaction,
    mut f: impl FnMut(&mut Transaction, Option<&Conflict>) -> Result<T, E>,
) -> Result<(T, CommitReceipt), TransactError<E>> {
    let mut previous: Option<Conflict> = None;
    let mut attempts_left = policy.max_attempts();
    loop {
        let mut txn = begin();
        let value = match f(&mut txn, previous.as_ref()) {
            Ok(value) => value,
            Err(error) => {
                txn.rollback();
                return Err(TransactError::Closure(error));
            }
        };
        match txn.commit() {
            Ok(receipt) => return Ok((value, receipt)),
            Err(TransactionError::Conflict(conflict)) => {
                attempts_left -= 1;
                if attempts_left == 0 {
                    return Err(TransactError::Exhausted(conflict));
                }
                previous = Some(conflict);
            }
            // A blocking call waits out a stall on its own thread, then runs
            // the attempt again, uncounted, with the same previous conflict.
            #[cfg(not(target_arch = "wasm32"))]
            Err(TransactionError::WouldBlock(WouldBlock::Stall(stall))) => stall.wait(),
            Err(other) => return Err(TransactError::Engine(other)),
        }
    }
}

/// Run `call` until it stops asking to wait: on
/// [`TransactionError::WouldBlock`], await what the error carries (a read's
/// [`IoWait`](crate::IoWait), a stall's [`StallWait`](crate::StallWait), a
/// key lock's [`LockWait`](crate::LockWait)) and call it again; any other
/// outcome is returned.
///
/// Inside [`OptimisticTransactionDb::transact_async`] a read that may miss
/// the cache is written `ready(|| txn.get_slice(key)).await`: the attempt
/// suspends on the miss and resumes with the same read, so the work it did
/// before the miss is kept. The wait completes at the poll of the queue the
/// read was recorded on, on that queue's thread; a task awaiting it on
/// another thread waits until that thread polls.
pub async fn ready<T>(mut call: impl FnMut() -> TxResult<T>) -> TxResult<T> {
    loop {
        match call() {
            Err(TransactionError::WouldBlock(would_block)) => wait_out(would_block).await,
            other => return other,
        }
    }
}

/// Await what a [`WouldBlock`] asks to wait on.
async fn wait_out(would_block: WouldBlock) {
    match would_block {
        WouldBlock::Io(wait) => wait.await,
        WouldBlock::Stall(wait) => wait.await,
        WouldBlock::Locked(wait) => wait.await,
    }
}

/// [`run`] for an attempt that never blocks: it reads through a `CacheOnly`
/// handle on `queue`, runs its `before_commit` callbacks with
/// [`Transaction::prepare`], waiting out any miss, and commits through
/// [`Transaction::commit_nowait`]. A commit refused because writes are
/// stalled waits for the stall and runs the attempt again, uncounted, with
/// the same `previous` conflict.
async fn run_async<T, E>(
    policy: &RetryPolicy,
    begin: impl Fn(&TxnOptions) -> Transaction,
    queue: QueueId,
    mut f: impl AsyncFnMut(&mut Transaction, Option<&Conflict>) -> Result<T, E>,
) -> Result<(T, CommitReceipt), TransactError<E>> {
    let options = TxnOptions::new().read_mode(ReadMode::CacheOnly(queue));
    let mut previous: Option<Conflict> = None;
    let mut attempts_left = policy.max_attempts();
    loop {
        let mut txn = begin(&options);
        let value = match f(&mut txn, previous.as_ref()).await {
            Ok(value) => value,
            Err(error) => {
                txn.rollback();
                return Err(TransactError::Closure(error));
            }
        };
        // A callback that misses stays queued with its effects rolled back,
        // so preparing again after the wait resumes where it stopped. Any
        // other failure is left for the commit to report.
        while let Err(TransactionError::WouldBlock(would_block)) = txn.prepare() {
            wait_out(would_block).await;
        }
        match txn.commit_nowait().await {
            Ok(receipt) => return Ok((value, receipt)),
            Err(TransactionError::Conflict(conflict)) => {
                attempts_left -= 1;
                if attempts_left == 0 {
                    return Err(TransactError::Exhausted(conflict));
                }
                previous = Some(conflict);
            }
            Err(TransactionError::WouldBlock(would_block)) => wait_out(would_block).await,
            Err(other) => return Err(TransactError::Engine(other)),
        }
    }
}

impl OptimisticTransactionDb {
    /// [`OptimisticTransactionDb::transact`] for a caller that must never
    /// block. Runs `f` in a transaction and commits it, re-running it
    /// on a conflict up to [`RetryPolicy::max_attempts`] runs, with the
    /// conflict the previous attempt lost to.
    ///
    /// Each attempt reads through a [`ReadMode::CacheOnly`] handle whose
    /// misses go to `queue`. Inside `f`, write a read that may miss as
    /// [`ready`]`(|| txn.get_slice(key)).await`: a miss suspends the attempt
    /// on its wait instead of ending it, and the work done before it is kept.
    /// The transaction's `before_commit` callbacks run through
    /// [`Transaction::prepare`], waiting out their misses the same way, and
    /// the commit goes through [`Transaction::commit_nowait`], whose ticket
    /// the attempt awaits: nothing here waits for the device or for another
    /// thread.
    ///
    /// The returned future needs no runtime. Every wait it awaits is
    /// completed by `queue`'s poll, on the thread that owns `queue`, so poll
    /// the future on that thread and poll `queue` when the future cannot
    /// progress; [`IoQueue::block_on`](crate::IoQueue::block_on) does both.
    ///
    /// A commit refused because writes are stalled waits for the stall to
    /// clear and runs the attempt again; that run is not counted against the
    /// policy, and it gets the same previous conflict. An error from `f` ends
    /// the attempt with [`TransactError::Closure`] and is not retried; any
    /// failure but a conflict ends it with [`TransactError::Engine`].
    ///
    /// # Example
    ///
    /// ```
    /// use regolith::{OptimisticTransactionDb, Options, RetryPolicy, TransactionError, ready};
    ///
    /// let db = OptimisticTransactionDb::open("counter", Options::memory())?;
    /// db.db().put(b"n", &41u64.to_be_bytes())?;
    /// // Flushed to a table the block cache has not read: the read below
    /// // misses the cache once.
    /// db.db().flush()?;
    ///
    /// let mut queue = db.db().io_queue();
    /// let policy = RetryPolicy::default();
    /// let mut misses = 0;
    /// let attempt = db.transact_async(queue.id(), &policy, async |txn, _lost| {
    ///     // `ready` waits out a miss and runs the read again, so the attempt
    ///     // is suspended, not ended.
    ///     let read = ready(|| {
    ///         let read = txn.get_for_update(b"n");
    ///         misses += usize::from(matches!(read, Err(TransactionError::WouldBlock(_))));
    ///         read
    ///     });
    ///     let n = read.await?.map_or(0, |n| u64::from_be_bytes(n.try_into().expect("eight bytes")));
    ///     txn.put(b"n", &(n + 1).to_be_bytes())?;
    ///     Ok::<_, TransactionError>(n + 1)
    /// });
    ///
    /// // No runtime: this thread polls the future, and its own queue whenever
    /// // the future waits.
    /// let (n, _receipt) = queue.block_on(attempt)?;
    /// assert_eq!((n, misses), (42, 1));
    /// assert_eq!(db.db().get(b"n")?, Some(42u64.to_be_bytes().to_vec()));
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn transact_async<T, E>(
        &self,
        queue: QueueId,
        policy: &RetryPolicy,
        f: impl AsyncFnMut(&mut Transaction, Option<&Conflict>) -> Result<T, E>,
    ) -> impl Future<Output = Result<(T, CommitReceipt), TransactError<E>>> {
        run_async(policy, |options| self.begin(options), queue, f)
    }

    /// Run `f` in a transaction and commit it. When the commit loses a race
    /// ([`TransactionError::Conflict`]), run `f` again in a fresh transaction,
    /// up to [`RetryPolicy::max_attempts`] runs in all.
    ///
    /// A re-run starts at once and sleeps for nothing: a race with one winner
    /// is settled on the re-run, which sees the winner. `f` gets the
    /// [`Conflict`] the previous attempt lost to, `None` on the first run, so
    /// it can settle the race by its own logic (the document it meant to
    /// delete is already deleted) instead of redoing the work blindly.
    ///
    /// An error from `f` ends the attempt with [`TransactError::Closure`] and
    /// is not retried; its transaction is rolled back. A commit a write stall
    /// stopped waits, on this thread, for the stall to clear, and runs the
    /// attempt again, uncounted. A commit that fails for any other reason but
    /// a conflict returns [`TransactError::Engine`]. When every attempt
    /// conflicts, the last conflict comes back as [`TransactError::Exhausted`].
    ///
    /// The transactions begin as [`OptimisticTransactionDb::begin`] begins
    /// them with default [`TxnOptions`]: at the database's isolation level.
    ///
    /// `f` may run more than once. Work with effects outside the transaction
    /// belongs before the call, or must be idempotent.
    ///
    /// # Example
    ///
    /// A counter another writer gets to first:
    ///
    /// ```
    /// use regolith::{
    ///     OptimisticTransactionDb, Options, RetryPolicy, TransactError, TransactionError,
    /// };
    ///
    /// let db = OptimisticTransactionDb::open("counter", Options::memory())?;
    /// let number = |held: Option<Vec<u8>>| {
    ///     held.map_or(0, |n| u64::from_be_bytes(n.try_into().expect("eight bytes")))
    /// };
    ///
    /// let mut runs = 0;
    /// let (seen, _receipt) = db.transact(&RetryPolicy::new(3), |txn, lost| {
    ///     runs += 1;
    ///     let n = number(txn.get_for_update(b"n")?);
    ///     if lost.is_none() {
    ///         // On the first run only, another writer commits in between.
    ///         db.db().put(b"n", &10u64.to_be_bytes())?;
    ///     }
    ///     txn.put(b"n", &(n + 1).to_be_bytes())?;
    ///     Ok::<_, TransactionError>(n)
    /// })?;
    ///
    /// // The first run lost its commit. The second began after the winner,
    /// // read its value and committed on top of it.
    /// assert_eq!((runs, seen), (2, 10));
    /// assert_eq!(number(db.db().get(b"n")?), 11);
    ///
    /// // An error from the closure ends the call and is not retried.
    /// let refused = db.transact(&RetryPolicy::default(), |_txn, _lost| Err::<(), _>("not today"));
    /// assert!(matches!(refused, Err(TransactError::Closure("not today"))));
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn transact<T, E>(
        &self,
        policy: &RetryPolicy,
        f: impl FnMut(&mut Transaction, Option<&Conflict>) -> Result<T, E>,
    ) -> Result<(T, CommitReceipt), TransactError<E>> {
        run(policy, || self.begin(&TxnOptions::new()), f)
    }
}

impl TransactionDb {
    /// [`OptimisticTransactionDb::transact_async`] for a pessimistic
    /// transaction. Its key locks are taken as `get_for_update` and the writes
    /// take them, which can still wait for another holder; the reads and the
    /// commit never wait for the device.
    pub fn transact_async<T, E>(
        &self,
        queue: QueueId,
        policy: &RetryPolicy,
        f: impl AsyncFnMut(&mut Transaction, Option<&Conflict>) -> Result<T, E>,
    ) -> impl Future<Output = Result<(T, CommitReceipt), TransactError<E>>> {
        run_async(policy, |options| self.begin(options), queue, f)
    }

    /// [`OptimisticTransactionDb::transact`] for a pessimistic transaction.
    ///
    /// A pessimistic commit conflicts only when a key it validates was written
    /// around the lock manager, so a re-run is rare. A lock that cannot be
    /// taken in time ([`TransactionError::Busy`]) arises inside `f`, where it
    /// is `f`'s own error and ends the attempt like any other.
    pub fn transact<T, E>(
        &self,
        policy: &RetryPolicy,
        f: impl FnMut(&mut Transaction, Option<&Conflict>) -> Result<T, E>,
    ) -> Result<(T, CommitReceipt), TransactError<E>> {
        run(policy, || self.begin(&TxnOptions::new()), f)
    }
}
