//! The transactions still open that have something to run when the database
//! closes: the ones with an `on_abort` callback, and every one under a
//! database with transaction hooks.
//!
//! `close` aborts each of them (see `transaction::claim`), so a callback
//! never waits on a caller that will not return. Nothing is listed for a
//! transaction without callbacks or hooks, and the map is built by the first
//! one that is, so a database that uses neither pays nothing.
//!
//! A pessimistic database also lists its lock table here: `close` releases
//! the key locks of the transactions it aborted and wakes every transaction
//! waiting for a lock, which then fails with `Closed`.

use std::sync::{Arc, OnceLock};

use kovan_map::HopscotchMap;

use super::RegolithEngine;
use crate::portability::{AtomicU64, Ordering};
use crate::transaction::{Claim, LockTable};

pub(crate) struct OpenTransactions {
    next_id: AtomicU64,
    open: OnceLock<HopscotchMap<u64, Arc<Claim>>>,
    /// The pessimistic lock table of the database, if it has one.
    locks: OnceLock<Arc<LockTable>>,
}

impl OpenTransactions {
    pub(crate) fn new() -> Self {
        Self {
            next_id: AtomicU64::new(0),
            open: OnceLock::new(),
            locks: OnceLock::new(),
        }
    }

    pub(crate) fn next_id(&self) -> u64 {
        self.next_id.fetch_add(1, Ordering::Relaxed)
    }

    pub(crate) fn insert(&self, claim: Arc<Claim>) {
        self.open
            .get_or_init(HopscotchMap::new)
            .insert(claim.id, claim);
    }

    pub(crate) fn remove(&self, id: u64) {
        if let Some(open) = self.open.get() {
            open.remove(&id);
        }
    }

    /// List the database's pessimistic lock table, for `close` to settle.
    pub(crate) fn track_locks(&self, locks: Arc<LockTable>) {
        let _ = self.locks.set(locks);
    }

    /// Abort every transaction still open, on the calling thread. One that
    /// began to commit first is not touched, and one listed while this runs
    /// may be missed: its owner ends it, with the same outcome. Then the
    /// lock table: the aborted transactions' key locks are released, and
    /// every transaction waiting for a lock is woken to find the database
    /// closed.
    pub(crate) fn abort_all(&self, engine: &RegolithEngine) {
        let mut aborted = Vec::new();
        if let Some(open) = self.open.get() {
            for (_, claim) in open.iter() {
                if claim.abort_for_close(engine)
                    && let Some(owner) = claim.lock_owner()
                {
                    aborted.push(Arc::clone(owner));
                }
            }
        }
        if let Some(locks) = self.locks.get() {
            locks.close(&aborted);
        }
    }

    /// A close that failed and left the database open: lock waits queue
    /// again.
    pub(crate) fn reopen_locks(&self) {
        if let Some(locks) = self.locks.get() {
            locks.reopen();
        }
    }
}
