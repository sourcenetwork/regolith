//! The transactions still open that have something to run when the database
//! closes: the ones with an `on_abort` callback, and every one under a
//! database with transaction hooks.
//!
//! `close` aborts each of them (see `transaction::claim`), so a callback
//! never waits on a caller that will not return. Nothing is listed for a
//! transaction without callbacks or hooks, and the map is built by the first
//! one that is, so a database that uses neither pays nothing.

use std::sync::{Arc, OnceLock};

use kovan_map::HopscotchMap;

use super::RegolithEngine;
use crate::portability::{AtomicU64, Ordering};
use crate::transaction::Claim;

pub(crate) struct OpenTransactions {
    next_id: AtomicU64,
    open: OnceLock<HopscotchMap<u64, Arc<Claim>>>,
}

impl OpenTransactions {
    pub(crate) fn new() -> Self {
        Self {
            next_id: AtomicU64::new(0),
            open: OnceLock::new(),
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

    /// Abort every transaction still open, on the calling thread. One that
    /// began to commit first is not touched, and one listed while this runs
    /// may be missed: its owner ends it, with the same outcome.
    pub(crate) fn abort_all(&self, engine: &RegolithEngine) {
        let Some(open) = self.open.get() else {
            return;
        };
        for (_, claim) in open.iter() {
            claim.abort_for_close(engine);
        }
    }
}
