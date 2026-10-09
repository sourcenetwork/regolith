//! The single-winner claim on a transaction's abort, shared with the engine.
//!
//! A transaction with an `on_abort` callback, or under a database with
//! [`TransactionHooks`](super::TransactionHooks), has to be abortable by a
//! thread that does not own it: `close` aborts every transaction still open.
//! The owner and the closer settle who ends the transaction with one
//! compare-and-swap on the claim's state word, as the model in
//! `proofs/tla/TxnCallbacks.tla` does:
//!
//! - `OPEN -> COMMITTING` is the owner starting its commit. After it nothing
//!   else aborts the transaction, and the owner alone runs its outcome.
//! - `OPEN -> ABORTED` is whoever ends the transaction without a commit: the
//!   owner by rollback or drop, or `close`. The winner runs the abort
//!   callbacks and the database hook; a loser runs neither.
//!
//! The `on_abort` callbacks live here, behind a mutex that is held only to
//! push or pop one, so each runs once however many threads reach for it.

use std::sync::Arc;

use super::callbacks::{AbortReason, OnAbort, survive};
use super::queue::Queue;
use crate::engine::RegolithEngine;
use crate::portability::{AtomicU8, Ordering};
use crate::sync::internal::Mutex;

const OPEN: u8 = 0;
const COMMITTING: u8 = 1;
const ABORTED: u8 = 2;

/// The shared half of a transaction that has something to run when it aborts.
pub(crate) struct Claim {
    pub(crate) id: u64,
    state: AtomicU8,
    on_abort: Mutex<Queue<OnAbort>>,
}

impl Claim {
    /// A claim on a new transaction, listed with the engine so `close` finds
    /// it. Nothing is listed once the database has begun to close: the closer
    /// has already swept, and the owner ends the transaction itself.
    pub(super) fn track(engine: &RegolithEngine) -> Arc<Self> {
        let claim = Arc::new(Self {
            id: engine.open_transactions().next_id(),
            state: AtomicU8::new(OPEN),
            on_abort: Mutex::new(Queue::default()),
        });
        if !engine.is_closed() {
            engine.open_transactions().insert(Arc::clone(&claim));
        }
        claim
    }

    fn win(&self, to: u8) -> bool {
        self.state
            .compare_exchange(OPEN, to, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
    }

    /// Claim the transaction for its commit. `false` means `close` aborted it
    /// first, and the owner's commit fails with [`crate::Error::Closed`].
    pub(super) fn begin_commit(&self) -> bool {
        self.win(COMMITTING)
    }

    /// Claim the transaction's abort. `false` means someone else already ended
    /// it.
    pub(super) fn abort(&self) -> bool {
        self.win(ABORTED)
    }

    /// [`Claim::abort`] for the owner, who also ends a transaction whose commit
    /// it claimed and then abandoned by unwinding.
    pub(super) fn owner_abort(&self) -> bool {
        match self
            .state
            .compare_exchange(OPEN, ABORTED, Ordering::AcqRel, Ordering::Acquire)
        {
            Ok(_) => true,
            Err(state) => state == COMMITTING,
        }
    }

    pub(super) fn push(&self, f: OnAbort) {
        self.on_abort.lock().push(f);
    }

    pub(super) fn mark(&self) -> usize {
        self.on_abort.lock().mark()
    }

    pub(super) fn truncate(&self, mark: usize) {
        self.on_abort.lock().truncate(mark);
    }

    fn pop(&self) -> Option<OnAbort> {
        self.on_abort.lock().pop()
    }

    /// Run the `on_abort` callbacks still queued, oldest first, each at most
    /// once. The lock is not held while one runs.
    pub(super) fn run_callbacks(&self, engine: &RegolithEngine, reason: &AbortReason<'_>) {
        while let Some(f) = self.pop() {
            survive(engine, "on_abort", || f(reason));
        }
    }

    /// What an abort owes: the transaction's `on_abort` callbacks, then the
    /// database hook's. The one function the owner and `close` both call.
    pub(super) fn run_abort(&self, engine: &RegolithEngine, reason: &AbortReason<'_>) {
        self.run_callbacks(engine, reason);
        if let Some(hooks) = engine.transaction_hooks() {
            survive(engine, "TransactionHooks::on_abort", || {
                hooks.on_abort(reason)
            });
        }
    }

    /// `close` ends the transaction if it is still open, on the closing
    /// thread.
    pub(crate) fn abort_for_close(&self, engine: &RegolithEngine) {
        if self.abort() {
            self.run_abort(engine, &AbortReason::Closed);
        }
    }
}
