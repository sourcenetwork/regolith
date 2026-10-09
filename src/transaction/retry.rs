//! Bounded retries owned by regolith: [`OptimisticTransactionDb::transact`]
//! and [`TransactionDb::transact`] run a closure in a transaction, commit it,
//! and run it again when the commit loses a race.
//!
//! A re-run starts at once. A one-winner race resolves on the re-run, which
//! sees the winner, so nothing sleeps. The closure receives the [`Conflict`]
//! the previous attempt lost to, so it can resolve the race instead of
//! redoing the same work blindly.

use super::{OptimisticTransactionDb, TransactionDb, TxnOptions};
use crate::{CommitReceipt, Conflict, Transaction, TransactionError};

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
        let value = f(&mut txn, previous.as_ref()).map_err(TransactError::Closure)?;
        match txn.commit() {
            Ok(receipt) => return Ok((value, receipt)),
            Err(TransactionError::Conflict(conflict)) => {
                attempts_left -= 1;
                if attempts_left == 0 {
                    return Err(TransactError::Exhausted(conflict));
                }
                previous = Some(conflict);
            }
            Err(other) => return Err(TransactError::Engine(other)),
        }
    }
}

impl OptimisticTransactionDb {
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
    /// is not retried; its transaction is rolled back. A commit that fails for
    /// any reason but a conflict returns [`TransactError::Engine`]. When every
    /// attempt conflicts, the last conflict comes back as
    /// [`TransactError::Exhausted`].
    ///
    /// The transactions begin as [`OptimisticTransactionDb::begin`] begins
    /// them with default [`TxnOptions`]: at the database's isolation level.
    ///
    /// `f` may run more than once. Work with effects outside the transaction
    /// belongs before the call, or must be idempotent.
    pub fn transact<T, E>(
        &self,
        policy: &RetryPolicy,
        f: impl FnMut(&mut Transaction, Option<&Conflict>) -> Result<T, E>,
    ) -> Result<(T, CommitReceipt), TransactError<E>> {
        run(policy, || self.begin(&TxnOptions::new()), f)
    }
}

impl TransactionDb {
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
