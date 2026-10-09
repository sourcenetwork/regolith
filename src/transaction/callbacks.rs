//! Callbacks a caller attaches to a transaction, and the database-wide hooks.
//!
//! A transaction has three points a caller can run code at: before the commit
//! decides ([`Transaction::before_commit`]), after it commits
//! ([`Transaction::on_commit`]) and after it ends without committing
//! ([`Transaction::on_abort`]). [`TransactionHooks`] is the same three points
//! for every transaction of a database. Both work at every isolation level,
//! for optimistic and pessimistic transactions alike. The protocol is the one
//! `proofs/tla/TxnCallbacks.tla` checks and `proofs/lean/Regolith/Callbacks.lean`
//! proves.
//!
//! Invariants this module holds:
//!
//! - Exactly one outcome. Every transaction ends in a commit or in an abort,
//!   never both and never neither, and the callbacks of the other outcome are
//!   dropped unrun. A callback registered for the outcome runs once: the
//!   `on_commit` ones are reached only by the owner that won the commit claim
//!   and the `on_abort` ones through the claim in `super::claim`, which
//!   settles between the owner and `close`.
//! - Order. At commit the transaction's own `before_commit` callbacks run in
//!   registration order, then the database hook, then validation. After the
//!   outcome the transaction's callbacks run in registration order, then the
//!   hook's.
//! - Before the outcome a panic or an error undoes the callback's effects
//!   (writes, savepoints and registrations) and fails the commit. After the
//!   outcome a panic is caught and reported to
//!   [`crate::EventListener::on_callback_panic`], and the outcome stands.
//! - A transaction that registered nothing, under a database with no hooks,
//!   pays one empty-option check at each point and allocates nothing.

use std::sync::Arc;

use super::claim::Claim;
use super::queue::Queue;
use super::{
    CommitReceipt, Conflict, Error, IsolationLevel, Transaction, TransactionError, TxResult,
};
use crate::engine::RegolithEngine;
use crate::engine::callback::{InCommit, contain};
use crate::sync::internal::Mutex;

/// Why a transaction ended without committing, as its
/// [`Transaction::on_abort`] callbacks and [`TransactionHooks::on_abort`] see
/// it.
///
/// Borrows the error that ended the commit, so building one costs nothing.
/// Match it through the reference the callback receives.
#[derive(Clone, Copy, Debug)]
#[non_exhaustive]
pub enum AbortReason<'a> {
    /// The caller rolled the transaction back with [`Transaction::rollback`].
    Rollback,
    /// The caller dropped the transaction without committing it or rolling it
    /// back.
    Dropped,
    /// The commit lost a race: another transaction wrote a key this one
    /// depended on. [`OptimisticTransactionDb::transact`](crate::OptimisticTransactionDb::transact)
    /// runs the closure again in a new transaction, which registers its own
    /// callbacks.
    Conflict(&'a Conflict),
    /// The commit failed for another reason: a `before_commit` callback or
    /// hook returned this error, or the engine refused the commit.
    Error(&'a TransactionError),
    /// The database was closed before the transaction could commit.
    Closed,
    /// A `before_commit` callback or hook panicked.
    CallbackPanicked,
}

impl<'a> AbortReason<'a> {
    /// What a failed commit that returned `error` reports.
    fn of(error: &'a TransactionError) -> Self {
        match error {
            TransactionError::Conflict(conflict) => Self::Conflict(conflict),
            TransactionError::Engine(Error::Closed) => Self::Closed,
            TransactionError::Engine(Error::CallbackPanicked { .. }) => Self::CallbackPanicked,
            other => Self::Error(other),
        }
    }
}

/// What a committed transaction hands [`TransactionHooks::on_commit`].
#[derive(Clone, Copy, Debug)]
#[non_exhaustive]
pub struct CommitInfo {
    receipt: CommitReceipt,
    isolation: IsolationLevel,
}

impl CommitInfo {
    /// The receipt of the commit: the sequence its writes became visible at,
    /// or the snapshot's sequence for a transaction that wrote nothing.
    pub fn receipt(&self) -> CommitReceipt {
        self.receipt
    }

    /// The isolation level the transaction ran at.
    pub fn isolation(&self) -> IsolationLevel {
        self.isolation
    }
}

/// Callbacks run for every transaction of a database, installed with
/// [`Options::transaction_hooks`](crate::Options::transaction_hooks).
///
/// The three methods are the points [`Transaction::before_commit`],
/// [`Transaction::on_commit`] and [`Transaction::on_abort`] give one
/// transaction. At commit the transaction's own `before_commit` callbacks run
/// first and the hook's [`before_commit`](Self::before_commit) after them,
/// both before validation. After the outcome the transaction's own callbacks
/// run first and the hook's after them. Every method has a default that does
/// nothing.
///
/// `on_commit` and `on_abort` run on the thread that completes the outcome and
/// must not block, panic or re-enter the database; a panic is caught and
/// reported to [`crate::EventListener::on_callback_panic`], and the outcome
/// stands. A panic in `before_commit` fails the commit with
/// [`Error::CallbackPanicked`].
///
/// A database with hooks tracks every transaction it begins, so that
/// [`crate::Db::close`] can run `on_abort` for the ones still open: that costs
/// one small allocation per transaction, and nothing for a database without
/// hooks.
pub trait TransactionHooks: Send + Sync + 'static {
    /// Runs once per commit, after the transaction's own `before_commit`
    /// callbacks and before validation, on the committing thread. It may read
    /// and write through `txn`; its writes are part of the commit and are
    /// validated like any other. An error fails the commit with that error,
    /// rolls the hook's writes back, and runs the abort callbacks.
    fn before_commit(&self, txn: &mut Transaction) -> TxResult<()> {
        let _ = txn;
        Ok(())
    }

    /// Runs once for a committed transaction, after its own `on_commit`
    /// callbacks, when the commit is visible (and durable under
    /// [`crate::DurabilityMode::Immediate`]).
    fn on_commit(&self, info: &CommitInfo) {
        let _ = info;
    }

    /// Runs once for a transaction that ended without committing, after its
    /// own `on_abort` callbacks.
    fn on_abort(&self, reason: &AbortReason<'_>) {
        let _ = reason;
    }
}

type BeforeCommit = Box<dyn FnOnce(&mut Transaction) -> TxResult<()> + Send>;
type OnCommit = Box<dyn FnOnce(&CommitReceipt) + Send>;
pub(super) type OnAbort = Box<dyn FnOnce(&AbortReason<'_>) + Send>;

/// Run `f`, catching a panic in it and naming `callback` in the error.
///
/// The commit's containment (`engine::callback`), switched on for this call:
/// the same catch and the same error as a caller's trait that panics inside
/// the ordered step.
fn caught<T>(callback: &'static str, f: impl FnOnce() -> T) -> Result<T, Error> {
    let _mode = InCommit::enter();
    contain(callback, f)
}

/// Run a callback after the outcome is decided: a panic cannot change the
/// outcome, so it is caught and reported to the listeners.
pub(super) fn survive(engine: &RegolithEngine, callback: &'static str, f: impl FnOnce()) {
    if caught(callback, f).is_err() {
        engine.notify_callback_panic(callback);
    }
}

#[derive(Default)]
struct Queues {
    before_commit: Queue<BeforeCommit>,
    on_commit: Queue<OnCommit>,
}

/// The `before_commit` and `on_commit` callbacks one transaction registered:
/// nothing until the first registration, then one allocation. (The
/// `on_abort` ones are in the transaction's claim.)
///
/// A [`Mutex`] only so a `Transaction` stays `Sync` although the closures are
/// `Send` and not `Sync`: the queues are reached through `&mut Transaction` or
/// by value, with `get_mut`, and never locked.
#[derive(Default)]
pub(super) struct Callbacks(Option<Box<Mutex<Queues>>>);

impl Callbacks {
    fn queues(&mut self) -> &mut Queues {
        self.0
            .get_or_insert_with(|| Box::new(Mutex::new(Queues::default())))
            .get_mut()
    }

    fn existing(&mut self) -> Option<&mut Queues> {
        self.0.as_mut().map(|queues| queues.get_mut())
    }

    fn take(&mut self) -> Option<Queues> {
        self.0.take().map(|queues| (*queues).into_inner())
    }
}

/// How far `prepare` got, so a second call repeats nothing.
#[derive(Clone, Copy)]
pub(super) enum Prepare {
    /// The database hook has not run.
    Pending,
    /// The database hook ran and succeeded.
    HooksRan,
    /// A `before_commit` callback panicked: the commit can only fail.
    Panicked(&'static str),
}

/// What `prepare` restores when a callback fails: the write and append
/// buffers and the savepoint stack as they were, and the callbacks as
/// registered.
struct Mark {
    writes: usize,
    appends: usize,
    savepoints: usize,
    before_commit: usize,
    on_commit: usize,
    on_abort: usize,
}

impl Transaction {
    /// The transaction's claim, made on the first `on_abort` registration.
    fn claim(&mut self) -> &Arc<Claim> {
        self.claim.get_or_insert_with(|| Claim::track(&self.engine))
    }

    /// Run `f` at commit, before validation, on the committing thread.
    ///
    /// Callbacks run in registration order, then the database's
    /// [`TransactionHooks::before_commit`], then validation. `f` may read and
    /// write through the transaction, and what it writes is part of the
    /// commit and validated like any other write. It may register further
    /// callbacks of any kind; the `before_commit` ones run in the same pass.
    ///
    /// An error from `f` fails the commit with that error and runs the
    /// `on_abort` callbacks. A panic in `f` does the same with
    /// [`Error::CallbackPanicked`], and leaves the database writable. Either
    /// way the writes `f` made, the savepoints it set and the callbacks it
    /// registered are taken back, and `f` is consumed: it is `FnOnce` and
    /// cannot run again.
    ///
    /// [`Transaction::prepare`] runs the pending callbacks early, and
    /// [`Transaction::commit`] runs whatever is left. A callback does not run
    /// for a transaction that is rolled back or dropped.
    pub fn before_commit(
        &mut self,
        f: impl FnOnce(&mut Transaction) -> TxResult<()> + Send + 'static,
    ) {
        self.callbacks.queues().before_commit.push(Box::new(f));
    }

    /// Run `f` once if the transaction commits, when the commit is visible
    /// (and durable under [`crate::DurabilityMode::Immediate`]), with the
    /// commit's receipt. A transaction that wrote nothing is handed the
    /// receipt of its snapshot.
    ///
    /// `f` runs on the thread that completes the commit, after the
    /// transaction released its locks and snapshot, and after the transaction's
    /// earlier `on_commit` callbacks. It must not block or re-enter the
    /// database. A panic in `f` is caught and reported to
    /// [`crate::EventListener::on_callback_panic`]; the commit stands and the
    /// other callbacks still run. If the transaction does not commit, `f` is
    /// dropped without running.
    pub fn on_commit(&mut self, f: impl FnOnce(&CommitReceipt) + Send + 'static) {
        self.callbacks.queues().on_commit.push(Box::new(f));
    }

    /// Run `f` once if the transaction ends without committing: rolled back,
    /// dropped, lost to a conflict, failed, or aborted by [`crate::Db::close`].
    /// The [`AbortReason`] says which.
    ///
    /// The same thread, ordering and panic rules as [`Transaction::on_commit`]
    /// apply. If the transaction commits, `f` is dropped without running.
    ///
    /// A transaction still open when the database is closed ends there: `close`
    /// runs `f` with [`AbortReason::Closed`] on its own thread, and the
    /// transaction's later commit fails with [`Error::Closed`]. That holds even
    /// if the close then fails, as the transaction stays aborted. A
    /// transaction that had begun to commit is not touched.
    pub fn on_abort(&mut self, f: impl FnOnce(&AbortReason<'_>) + Send + 'static) {
        self.claim().push(Box::new(f));
    }

    /// Run the pending `before_commit` callbacks now, then the database's
    /// [`TransactionHooks::before_commit`], so a caller can find out whether
    /// the commit would get past them before it commits.
    ///
    /// [`Transaction::commit`] calls this first, so calling it is never
    /// required. It is idempotent: a call with nothing pending does nothing,
    /// and the hook runs once however often this is called. A callback
    /// registered after a successful call runs at the next one, after the
    /// hook.
    ///
    /// An error from a callback is returned, the writes, savepoints and
    /// registrations that callback made are taken back, and the callback is
    /// consumed because it is `FnOnce`. The callbacks after it stay queued, so
    /// a second call runs them. An error from the hook leaves the hook to run
    /// again. A callback that panics returns [`Error::CallbackPanicked`], and
    /// so does every later call: the transaction can only be rolled back.
    ///
    /// A callback that calls `prepare` on the transaction it was handed runs
    /// the callbacks queued behind it inside itself.
    pub fn prepare(&mut self) -> TxResult<()> {
        if let Prepare::Panicked(callback) = self.prepare_state {
            return Err(Error::CallbackPanicked { callback }.into());
        }
        self.run_before_commit()?;
        if matches!(self.prepare_state, Prepare::Pending)
            && let Some(hooks) = self.engine.transaction_hooks().cloned()
        {
            self.guarded("TransactionHooks", |txn| hooks.before_commit(txn))?;
            self.prepare_state = Prepare::HooksRan;
            self.run_before_commit()?;
        }
        Ok(())
    }

    /// Run every queued `before_commit` callback, including those they
    /// register.
    fn run_before_commit(&mut self) -> TxResult<()> {
        while let Some(f) = self
            .callbacks
            .existing()
            .and_then(|queues| queues.before_commit.pop())
        {
            self.guarded("before_commit", f)?;
        }
        Ok(())
    }

    /// Run `run`, and when it errors or panics, take back everything it did.
    fn guarded(
        &mut self,
        callback: &'static str,
        run: impl FnOnce(&mut Transaction) -> TxResult<()>,
    ) -> TxResult<()> {
        let mark = self.mark();
        let error = match caught(callback, || run(self)) {
            Ok(Ok(())) => return Ok(()),
            Ok(Err(error)) => error,
            Err(panicked) => {
                self.prepare_state = Prepare::Panicked(callback);
                panicked.into()
            }
        };
        self.rewind(mark);
        Err(error)
    }

    fn mark(&mut self) -> Mark {
        let (before_commit, on_commit) = self
            .callbacks
            .existing()
            .map_or((0, 0), |q| (q.before_commit.mark(), q.on_commit.mark()));
        Mark {
            writes: self.writes.len(),
            appends: self.appends_len(),
            savepoints: self.savepoints.len(),
            before_commit,
            on_commit,
            on_abort: self.claim.as_ref().map_or(0, |claim| claim.mark()),
        }
    }

    fn rewind(&mut self, mark: Mark) {
        self.writes.truncate(mark.writes);
        self.truncate_appends(mark.appends);
        self.savepoints.truncate(mark.savepoints);
        if let Some(queues) = self.callbacks.existing() {
            queues.before_commit.truncate(mark.before_commit);
            queues.on_commit.truncate(mark.on_commit);
        }
        if let Some(claim) = &self.claim {
            claim.truncate(mark.on_abort);
        }
    }

    /// End the transaction whose commit the owner claimed, by the commit's
    /// result: run the callbacks of the outcome it reached and drop the other
    /// outcome's. `claimed` is whether the owner won the commit claim; if
    /// `close` aborted the transaction first, `close` ran its callbacks and
    /// only those registered since are left.
    pub(super) fn finish(&mut self, claimed: bool, result: &TxResult<CommitReceipt>) {
        match (claimed, result) {
            (true, Ok(receipt)) => self.finish_commit(*receipt),
            (true, Err(error)) => self.finish_abort(&AbortReason::of(error)),
            (false, _) => self.finish_closed(),
        }
    }

    fn finish_commit(&mut self, receipt: CommitReceipt) {
        if let Some(mut own) = self.callbacks.take() {
            while let Some(f) = own.on_commit.pop() {
                survive(&self.engine, "on_commit", || f(&receipt));
            }
        }
        if let Some(hooks) = self.engine.transaction_hooks() {
            let info = CommitInfo {
                receipt,
                isolation: self.isolation,
            };
            survive(&self.engine, "TransactionHooks::on_commit", || {
                hooks.on_commit(&info)
            });
        }
    }

    fn finish_abort(&mut self, reason: &AbortReason<'_>) {
        drop(self.callbacks.take());
        if let Some(claim) = &self.claim {
            claim.run_abort(&self.engine, reason);
        }
    }

    /// `close` already ended this transaction and ran its callbacks; run the
    /// ones registered after it did.
    fn finish_closed(&mut self) {
        drop(self.callbacks.take());
        if let Some(claim) = &self.claim {
            claim.run_callbacks(&self.engine, &AbortReason::Closed);
        }
    }

    /// End a transaction the owner rolled back or dropped before any commit
    /// claimed it. The owner wins the abort unless `close` did.
    fn end_open(&mut self, reason: &AbortReason<'_>) {
        if self.claim.as_ref().is_some_and(|claim| claim.owner_abort()) {
            self.finish_abort(reason);
        } else {
            self.finish_closed();
        }
    }

    /// The owner rolled the transaction back.
    pub(super) fn finish_rolled_back(&mut self) {
        self.end_open(&AbortReason::Rollback);
    }

    /// The owner dropped the transaction without resolving it.
    pub(super) fn finish_dropped(&mut self) {
        if self.claim.is_none() {
            return;
        }
        let reason = if self.engine.is_closed() {
            AbortReason::Closed
        } else {
            AbortReason::Dropped
        };
        self.end_open(&reason);
    }
}
