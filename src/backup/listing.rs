//! Listing the backups in `meta/`, in id order, a bounded page at a time.
//!
//! Id order needs a sort, and a sort of the whole directory would hold
//! every backup id at once. Instead each page is one walk of `meta/` that
//! keeps the [`PAGE`] smallest ids above the last one listed, in a heap of
//! that size. Listing a repository of `n` backups takes `n / PAGE + 1`
//! walks and holds one page of ids and one backup's listing at any time,
//! whatever the repository holds.

use std::collections::BinaryHeap;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::{BackupId, BackupInfo, backup_filename, format, parse_backup_id};
use crate::env::Env;
use crate::{Error, Result};

/// Backup ids one page holds: 8 KiB of ids.
pub(super) const PAGE: usize = 1024;

/// The backup id `name` is the metadata file of, when it is exactly the
/// name the engine writes for it. A stray name that parses to an id
/// (`7.backup` beside `000007.backup`) is not a second backup 7.
fn listed_id(name: &str) -> Option<u64> {
    parse_backup_id(name).filter(|&id| backup_filename(id) == name)
}

/// The `limit` smallest backup ids above `after` in `meta_dir`, ascending,
/// from one walk of the directory that holds at most `limit` ids.
pub(super) fn page_after(
    env: &dyn Env,
    meta_dir: &Path,
    after: Option<u64>,
    limit: usize,
) -> io::Result<Vec<u64>> {
    // A max-heap of the smallest ids seen so far: a smaller id displaces
    // the largest one held once the heap is full.
    let mut smallest = BinaryHeap::with_capacity(limit);
    for entry in env.read_dir(meta_dir)? {
        let Some(id) = listed_id(&entry?.file_name()) else {
            continue;
        };
        if after.is_some_and(|after| id <= after) {
            continue;
        }
        if smallest.len() < limit {
            smallest.push(id);
        } else if let Some(mut largest) = smallest.peek_mut()
            && id < *largest
        {
            *largest = id;
        }
    }
    Ok(smallest.into_sorted_vec())
}

/// The backups in a repository, in id order (creation order), from
/// [`super::BackupEngine::list_backups`].
///
/// Streamed a page at a time: the next page is walked only when the last
/// one is used up, so a listing holds one page of ids and one backup's
/// listing whatever the repository holds. It owns what it needs, so the
/// engine can delete the backups it lists while it lists them.
///
/// A backup whose metadata cannot be read is left out. An error walking
/// `meta/` is yielded as an `Err` item and ends the listing: the backups
/// after it are not known, and the error says so rather than end the
/// listing as if there were none.
pub struct Backups {
    env: Arc<dyn Env>,
    meta_dir: PathBuf,
    /// The page being listed, the ids not yet yielded.
    page: std::vec::IntoIter<u64>,
    /// The last id taken from a page; the next page starts above it.
    after: Option<u64>,
    /// No page is left to walk.
    done: bool,
}

impl Backups {
    pub(super) fn new(env: Arc<dyn Env>, meta_dir: PathBuf) -> Self {
        Self {
            env,
            meta_dir,
            page: Vec::new().into_iter(),
            after: None,
            done: false,
        }
    }

    /// Backup `id`'s summary, or `None` when its metadata cannot be read.
    fn info(&self, id: u64) -> Option<BackupInfo> {
        let bytes = self
            .env
            .read(&self.meta_dir.join(backup_filename(id)))
            .ok()?;
        let listing = format::decode_listing(&bytes).ok()?;
        // A listing whose sizes overflow is not one the engine wrote: it
        // is left out like any other that cannot be read.
        let bytes = listing
            .objects
            .iter()
            .try_fold(0u64, |total, &(_, size)| total.checked_add(size))?;
        Some(BackupInfo {
            id: BackupId(id),
            created_at_unix: listing.created_at_unix,
            file_count: listing.objects.len(),
            bytes,
        })
    }
}

impl Iterator for Backups {
    type Item = Result<BackupInfo>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(id) = self.page.next() {
                self.after = Some(id);
                match self.info(id) {
                    Some(info) => return Some(Ok(info)),
                    None => continue,
                }
            }
            if self.done {
                return None;
            }
            match page_after(&*self.env, &self.meta_dir, self.after, PAGE) {
                Ok(page) => {
                    // A short page is the last one.
                    self.done = page.len() < PAGE;
                    self.page = page.into_iter();
                }
                Err(e) => {
                    self.done = true;
                    return Some(Err(Error::from(e)));
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::MemEnv;

    fn meta_dir(env: &MemEnv, ids: impl IntoIterator<Item = u64>) -> PathBuf {
        let dir = PathBuf::from("/backups/meta");
        env.create_dir_all(&dir).unwrap();
        for id in ids {
            env.write(&dir.join(backup_filename(id)), b"").unwrap();
        }
        dir
    }

    #[test]
    fn pages_cover_every_id_once_in_order() {
        let env = MemEnv::new();
        // Gaps, as deletes leave them, created in no particular order.
        let ids: Vec<u64> = (1..=50).rev().filter(|id| id % 7 != 0).collect();
        let dir = meta_dir(&env, ids.iter().copied());
        let mut listed = Vec::new();
        let mut after = None;
        loop {
            let page = page_after(&env, &dir, after, 4).unwrap();
            assert!(page.len() <= 4, "a page held {} ids", page.len());
            assert!(page.windows(2).all(|w| w[0] < w[1]), "{page:?}");
            let Some(&last) = page.last() else {
                break;
            };
            listed.extend_from_slice(&page);
            after = Some(last);
        }
        let mut want = ids;
        want.sort_unstable();
        assert_eq!(listed, want);
    }

    #[test]
    fn a_page_skips_stray_names_and_other_files() {
        let env = MemEnv::new();
        let dir = meta_dir(&env, [3, 1]);
        env.write(&dir.join("1.backup"), b"").unwrap();
        env.write(&dir.join("000002.tmp"), b"").unwrap();
        env.write(&dir.join("notes"), b"").unwrap();
        assert_eq!(page_after(&env, &dir, None, PAGE).unwrap(), vec![1, 3]);
        assert_eq!(page_after(&env, &dir, Some(1), PAGE).unwrap(), vec![3]);
        assert!(page_after(&env, &dir, Some(3), PAGE).unwrap().is_empty());
    }

    #[test]
    fn listed_ids_round_trip_only_the_engine_name() {
        assert_eq!(listed_id("000007.backup"), Some(7));
        assert_eq!(listed_id("1234567.backup"), Some(1_234_567));
        assert_eq!(listed_id("7.backup"), None);
        assert_eq!(listed_id("000007.tmp"), None);
        assert_eq!(listed_id("x.backup"), None);
    }

    #[test]
    fn a_walk_error_is_yielded_and_ends_the_listing() {
        let env: Arc<dyn Env> = Arc::new(MemEnv::new());
        let mut backups = Backups::new(env, PathBuf::from("/missing/meta"));
        let first = backups.next().expect("an item");
        assert!(
            matches!(&first, Err(Error::Io(e)) if e.kind() == io::ErrorKind::NotFound),
            "{first:?}"
        );
        assert!(backups.next().is_none());
    }
}
