//! Walking `wal/` for the write-ahead logs it holds.
//!
//! Every walk takes one directory entry at a time ([`Env::read_dir`]). The
//! sweeps that remove logs act on each one as it comes, and recovery keeps
//! only the logs it is going to replay before it sorts them, so no walk
//! holds the directory, however many other files it has.

use std::io;
use std::path::{Path, PathBuf};

use crate::env::Env;

/// Whether `path` names a write-ahead log, by its extension.
fn is_log(path: &Path) -> bool {
    path.extension()
        .is_some_and(|ext| ext == "log" || ext == "wal")
}

/// Walk the write-ahead logs in `dir`, one entry at a time. A directory
/// that does not exist holds none.
pub(super) fn walk<'a>(
    env: &'a dyn Env,
    dir: &Path,
) -> io::Result<impl Iterator<Item = io::Result<PathBuf>> + use<'a>> {
    let entries = if env.exists(dir) {
        Some(env.read_dir(dir)?)
    } else {
        None
    };
    Ok(entries
        .into_iter()
        .flatten()
        .filter_map(|entry| match entry {
            Ok(entry) => is_log(&entry.path).then_some(Ok(entry.path)),
            Err(e) => Some(Err(e)),
        }))
}

/// The logs recovery replays, oldest first: the ones at or above
/// `min_wal_id` (`should_replay_wal`).
///
/// The walk keeps only those, then sorts them, so it holds the live logs
/// and never the directory. A live log is one whose writes no table holds
/// yet, and replay reads each one whole, so their paths cost nothing beside
/// the replay itself.
pub(super) fn live(env: &dyn Env, dir: &Path, min_wal_id: u64) -> io::Result<Vec<PathBuf>> {
    let mut live = Vec::new();
    for log in walk(env, dir)? {
        let log = log?;
        if super::should_replay_wal(&log, min_wal_id) {
            live.push(log);
        }
    }
    live.sort();
    Ok(live)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::MemEnv;

    fn touch(env: &MemEnv, path: &str) {
        env.write(Path::new(path), b"").unwrap();
    }

    #[test]
    fn live_keeps_only_the_logs_at_or_above_the_minimum_in_order() {
        let env = MemEnv::new();
        env.create_dir_all(Path::new("/db/wal")).unwrap();
        // Logs below the minimum, a staging file and a stray name, among
        // the live ones, in no particular order.
        for id in (0..200).rev() {
            touch(&env, &format!("/db/wal/wal_{id:06}.log"));
        }
        touch(&env, "/db/wal/wal_000300.tmp");
        touch(&env, "/db/wal/LOCK");
        let live = live(&env, Path::new("/db/wal"), 197).unwrap();
        let want: Vec<PathBuf> = (197..200)
            .map(|id| PathBuf::from(format!("/db/wal/wal_{id:06}.log")))
            .collect();
        assert_eq!(live, want);
    }

    #[test]
    fn before_any_reset_every_log_is_live_even_one_without_an_id() {
        let env = MemEnv::new();
        env.create_dir_all(Path::new("/db/wal")).unwrap();
        touch(&env, "/db/wal/wal_000002.log");
        touch(&env, "/db/wal/legacy.wal");
        let live = live(&env, Path::new("/db/wal"), 0).unwrap();
        assert_eq!(
            live,
            vec![
                PathBuf::from("/db/wal/legacy.wal"),
                PathBuf::from("/db/wal/wal_000002.log"),
            ]
        );
        // Once a reset committed, a log with no id is never replayed.
        let live = super::live(&env, Path::new("/db/wal"), 1).unwrap();
        assert_eq!(live, vec![PathBuf::from("/db/wal/wal_000002.log")]);
    }

    #[test]
    fn a_missing_directory_holds_no_log() {
        let env = MemEnv::new();
        assert_eq!(walk(&env, Path::new("/nowhere")).unwrap().count(), 0);
        assert!(live(&env, Path::new("/nowhere"), 0).unwrap().is_empty());
    }
}
