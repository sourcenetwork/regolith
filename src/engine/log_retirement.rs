//! Retiring the write-ahead logs whose writes are in tables (E30).
//!
//! A flush makes its memtable's log redundant with the one synced manifest
//! batch that adds the table: the same batch records, as `min_wal_id`,
//! that every log up to the flushed one holds only writes a table holds.
//! Recovery replays only logs at or above `min_wal_id`
//! (`should_replay_wal`), so a redundant log is never replayed, whether or
//! not its removal succeeded. Replaying one would put its versions in the
//! memtable, which a read consults before any table, so a key rewritten
//! since, by a later flush or an ingest, would read back as its older value.
//!
//! Removal is then a matter of disk space. A failed one is reported, a warn
//! line and [`Ticker::WalRemoveFailed`], and retried: by the next flush,
//! which sweeps every log below the one it retires, and by the next open,
//! which removes every log below the one it starts. Logs are retired oldest
//! first, so a log below a retired one is redundant too.

use std::path::{Path, PathBuf};

use crate::env::Env;
use crate::portability::{AtomicBool, Ordering};
use crate::statistics::{Statistics, Ticker};

use super::memtable::MemTable;
use super::wal::Wal;

/// The logs a flush leaves behind, and whether a removal is owed.
pub(crate) struct RetiredLogs {
    wal_dir: PathBuf,
    /// Set when a removal failed; the next retirement sweeps the directory.
    owed: AtomicBool,
}

impl RetiredLogs {
    /// Retirement for the logs in `wal_dir`, owing a sweep when `owed`.
    pub(crate) fn new(wal_dir: PathBuf, owed: bool) -> Self {
        Self {
            wal_dir,
            owed: AtomicBool::new(owed),
        }
    }

    /// Remove the log `flushed` was sealed with, once a durable manifest
    /// batch holds its writes in a table, and every log below it a failed
    /// removal left behind.
    ///
    /// Caller holds the flush exclusion, so retirements run in seal order.
    pub(crate) fn retire(&self, env: &dyn Env, flushed: &MemTable, stats: Option<&Statistics>) {
        let Some(path) = flushed.sealed_wal() else {
            return;
        };
        if !remove_log(env, path, stats) {
            self.owed.store(true, Ordering::Release);
            return;
        }
        if self.owed.swap(false, Ordering::AcqRel)
            && let Some(id) = super::wal_file_id(path)
            && !remove_below(env, &self.wal_dir, id, stats)
        {
            self.owed.store(true, Ordering::Release);
        }
    }
}

/// The `min_wal_id` a flush of `flushed` records with its table: every log
/// up to the one `flushed` was sealed with is then in tables.
pub(crate) fn min_wal_id_after(flushed: &MemTable) -> Option<u64> {
    super::wal_file_id(flushed.sealed_wal()?).map(|id| id + 1)
}

/// Remove every log in `wal_dir` whose id is below `min_wal_id`, reporting
/// each one that stays. Returns whether none stayed.
pub(crate) fn remove_below(
    env: &dyn Env,
    wal_dir: &Path,
    min_wal_id: u64,
    stats: Option<&Statistics>,
) -> bool {
    let logs = match super::list_wal_files(env, wal_dir) {
        Ok(logs) => logs,
        Err(error) => {
            tracing::warn!(
                dir = %wal_dir.display(),
                %error,
                "could not list the write-ahead logs to remove the ones in tables; trying again at the next flush or open"
            );
            return false;
        }
    };
    // Every log is tried, whether or not one before it stayed.
    let stayed = logs
        .iter()
        .filter(|path| super::wal_file_id(path).is_some_and(|id| id < min_wal_id))
        .filter(|path| !remove_log(env, path, stats))
        .count();
    stayed == 0
}

/// Remove one log whose writes are in tables. A log already gone counts as
/// removed; any other failure is logged and counted, and returns `false`.
fn remove_log(env: &dyn Env, path: &Path, stats: Option<&Statistics>) -> bool {
    match Wal::remove_in(env, path) {
        Ok(()) => true,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => true,
        Err(error) => {
            tracing::warn!(
                path = %path.display(),
                %error,
                "could not remove a write-ahead log whose writes are in tables; it is never replayed, and the next flush or open removes it"
            );
            if let Some(stats) = stats {
                stats.add(Ticker::WalRemoveFailed, 1);
            }
            false
        }
    }
}
