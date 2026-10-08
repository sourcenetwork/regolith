//! The newest-first walk over a view's sources for one key. Every single-key
//! probe (the point read, the merge-chain read, the commit check's
//! latest-version and terminator probes) shares it, so they cannot disagree
//! about which source shadows which. `multi_get_in_view` keeps its own
//! source-major walk because it visits each source once for many keys.

use std::io;
use std::ops::ControlFlow;

use super::file_covers_key;
use super::memtable::MemTable;
use super::read_view::ReadView;
use super::sstable::SsTableReader;

/// One source a key's entries can come from.
pub(crate) enum Source<'a> {
    /// The active memtable or a frozen one.
    Memtable(&'a MemTable),
    /// One SSTable that may hold the key.
    Table(&'a SsTableReader),
}

impl ReadView {
    /// Visits the sources of this view that may hold `key`, newest first: the
    /// active memtable, the frozen ones, every L0 table, then each deeper
    /// level's tables whose key range covers `key`. `visit` sees each with the
    /// newest sequence of a range tombstone covering `key` at `snapshot_seq`
    /// seen so far: a memtable's or an L0 table's own count before it is
    /// visited, a deeper level's are gathered across all its covering tables
    /// before any of them is, since a tombstone can sit in a table other than
    /// the one holding the key. `visit` breaks to stop the walk; once every
    /// source was visited, the walk continues with the final tombstone
    /// sequence.
    #[inline]
    pub(crate) fn walk_newest_first<B>(
        &self,
        key: &[u8],
        snapshot_seq: u64,
        mut visit: impl FnMut(Source<'_>, u64) -> io::Result<ControlFlow<B>>,
    ) -> io::Result<ControlFlow<B, u64>> {
        let mut max_rt_seq: u64 = 0;

        for mt in std::iter::once(&self.active).chain(self.frozen.iter().rev()) {
            max_rt_seq = max_rt_seq.max(mt.covering_range_tombstone_seq(key, snapshot_seq));
            if let ControlFlow::Break(done) = visit(Source::Memtable(mt), max_rt_seq)? {
                return Ok(ControlFlow::Break(done));
            }
        }

        let levels = &self.version.levels;
        // Every L0 table, whatever its key range: they may overlap, and a
        // filter here would change which bloom checks a point read runs.
        for file in levels[0].iter().rev() {
            max_rt_seq =
                max_rt_seq.max(file.reader.covering_range_tombstone_seq(key, snapshot_seq));
            if let ControlFlow::Break(done) = visit(Source::Table(&file.reader), max_rt_seq)? {
                return Ok(ControlFlow::Break(done));
            }
        }

        for files in levels.iter().skip(1) {
            if files.is_empty() {
                continue;
            }
            for file in files.iter().filter(|file| file_covers_key(file, key)) {
                max_rt_seq =
                    max_rt_seq.max(file.reader.covering_range_tombstone_seq(key, snapshot_seq));
            }
            let holders = files
                .iter()
                .filter(|file| file.meta.num_entries > 0 && file_covers_key(file, key));
            for file in holders {
                if let ControlFlow::Break(done) = visit(Source::Table(&file.reader), max_rt_seq)? {
                    return Ok(ControlFlow::Break(done));
                }
            }
        }

        Ok(ControlFlow::Continue(max_rt_seq))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::column_family::{DEFAULT_CF_ID, prefix_key};
    use crate::engine::internal_key::{VALUE_TYPE_VALUE, encode_internal_key};
    use crate::engine::manifest::Version;
    use crate::engine::memtable::MemTableConfig;
    use crate::engine::sstable::{LiveSst, SsTableMeta, SsTableWriter};
    use crate::options::CompressionType;
    use crate::portability::Ordering;
    use crate::{Db, Options};
    use std::sync::Arc;
    use tempfile::TempDir;

    /// A database where only an explicit flush moves data between sources.
    fn open(dir: &TempDir) -> Db {
        let options = Options {
            max_background_compactions: 0,
            ..Options::default()
        };
        Db::open(dir.path(), options).unwrap()
    }

    /// `name` as the default column family stores it.
    fn key_of(name: &[u8]) -> Vec<u8> {
        prefix_key(DEFAULT_CF_ID, name)
    }

    /// Seal the active memtable and leave it frozen. Only an ingest in
    /// flight keeps a rotation from flushing the memtable it seals.
    fn freeze_active(db: &Db) {
        let engine = db.engine();
        let _pipeline = engine.pipeline.lock();
        engine.ingest_holds_flushes.store(true, Ordering::Release);
        engine.rotate_memtable().unwrap();
        engine.ingest_holds_flushes.store(false, Ordering::Release);
    }

    /// Where `view` keeps `source`: "active", "frozen N" or "L<level> N",
    /// N counting from the oldest.
    fn name_of(view: &ReadView, source: &Source<'_>) -> String {
        match source {
            Source::Memtable(mt) if std::ptr::eq(*mt, &*view.active) => "active".to_string(),
            Source::Memtable(mt) => {
                let n = view
                    .frozen
                    .iter()
                    .position(|frozen| std::ptr::eq(*mt, &**frozen))
                    .expect("a frozen memtable of the view");
                format!("frozen {n}")
            }
            Source::Table(reader) => view
                .version
                .levels
                .iter()
                .enumerate()
                .find_map(|(level, files)| {
                    files
                        .iter()
                        .position(|file| std::ptr::eq(*reader, &*file.reader))
                        .map(|n| format!("L{level} {n}"))
                })
                .expect("a table of the view"),
        }
    }

    /// Walk `view` for `key` without ever breaking: every source visited
    /// with the tombstone sequence it was handed, and the sequence the walk
    /// ended with.
    fn walk_all(view: &ReadView, key: &[u8], snapshot_seq: u64) -> (Vec<(String, u64)>, u64) {
        let mut visited = Vec::new();
        let ended = view
            .walk_newest_first(&key_of(key), snapshot_seq, |source, max_rt_seq| {
                visited.push((name_of(view, &source), max_rt_seq));
                Ok(ControlFlow::<()>::Continue(()))
            })
            .unwrap();
        match ended {
            ControlFlow::Continue(max_rt_seq) => (visited, max_rt_seq),
            ControlFlow::Break(()) => unreachable!("the visit never breaks"),
        }
    }

    #[test]
    fn the_walk_visits_memtables_before_tables_newest_first_and_stops_at_the_first_break() {
        let dir = TempDir::new().unwrap();
        let db = open(&dir);
        db.put(b"a", b"1").unwrap();
        db.flush().unwrap();
        db.put(b"b", b"2").unwrap();
        db.flush().unwrap();
        db.put(b"c", b"3").unwrap();
        freeze_active(&db);
        db.put(b"d", b"4").unwrap();
        let view = db.engine().view.load();

        // Every L0 table is visited, whatever its key range.
        let (visited, ended) = walk_all(&view, b"a", u64::MAX);
        let places: Vec<&str> = visited.iter().map(|(place, _)| place.as_str()).collect();
        assert_eq!(places, ["active", "frozen 0", "L0 1", "L0 0"]);
        assert_eq!(ended, 0);

        for (stop_at, expected) in [
            ("active", &["active"][..]),
            ("L0 1", &["active", "frozen 0", "L0 1"][..]),
        ] {
            let mut seen = Vec::new();
            let walked = view
                .walk_newest_first(&key_of(b"a"), u64::MAX, |source, _| {
                    let name = name_of(&view, &source);
                    let stop = name == stop_at;
                    seen.push(name);
                    Ok(if stop {
                        ControlFlow::Break(7)
                    } else {
                        ControlFlow::Continue(())
                    })
                })
                .unwrap();
            assert!(matches!(walked, ControlFlow::Break(7)));
            assert_eq!(seen, expected);
        }
    }

    #[test]
    fn an_exhausted_walk_continues_with_the_newest_covering_tombstone_sequence() {
        let dir = TempDir::new().unwrap();
        let db = open(&dir);
        db.put(b"k", b"v").unwrap();
        db.flush().unwrap();
        db.delete_range(b"a", b"m").unwrap();
        let first = db.latest_sequence();
        {
            let view = db.engine().view.load();
            assert_eq!(walk_all(&view, b"k", u64::MAX).1, first);
            assert_eq!(walk_all(&view, b"z", u64::MAX).1, 0, "not covered");
            assert_eq!(walk_all(&view, b"m", u64::MAX).1, 0, "the end is exclusive");
        }

        // The first tombstone moves into a table; a newer one covers `k` too.
        db.flush().unwrap();
        db.delete_range(b"b", b"z").unwrap();
        let second = db.latest_sequence();
        let view = db.engine().view.load();
        assert_eq!(walk_all(&view, b"k", u64::MAX).1, second);
        assert_eq!(
            walk_all(&view, b"k", first).1,
            first,
            "a tombstone above the snapshot is not seen"
        );
        assert_eq!(walk_all(&view, b"k", first - 1).1, 0);
    }

    #[test]
    fn a_tombstone_in_a_newer_source_reaches_the_visit_of_an_older_table() {
        let dir = TempDir::new().unwrap();
        let db = open(&dir);
        db.put(b"k", b"v").unwrap();
        db.flush().unwrap();
        db.delete_range(b"a", b"z").unwrap();
        let tombstone = db.latest_sequence();
        db.flush().unwrap();
        let view = db.engine().view.load();

        let (visited, ended) = walk_all(&view, b"k", u64::MAX);
        let expected = [("active", 0), ("L0 1", tombstone), ("L0 0", tombstone)];
        assert_eq!(visited, expected.map(|(place, rt)| (place.to_string(), rt)));
        assert_eq!(ended, tombstone);
    }

    #[test]
    fn a_tombstone_in_an_older_source_does_not_reach_the_visit_of_a_newer_one() {
        let dir = TempDir::new().unwrap();
        let db = open(&dir);
        db.delete_range(b"a", b"z").unwrap();
        let tombstone = db.latest_sequence();
        db.flush().unwrap();
        db.put(b"k", b"v").unwrap();
        db.flush().unwrap();
        let view = db.engine().view.load();

        let (visited, ended) = walk_all(&view, b"k", u64::MAX);
        let expected = [("active", 0), ("L0 1", 0), ("L0 0", tombstone)];
        assert_eq!(visited, expected.map(|(place, rt)| (place.to_string(), rt)));
        assert_eq!(ended, tombstone);
    }

    /// A table of the point entries `points` (key, sequence) and the range
    /// tombstones `tombstones` (start, end, sequence), as a level lists it.
    fn live_table(
        dir: &TempDir,
        file_id: u64,
        points: &[(&[u8], u64)],
        tombstones: &[(&[u8], &[u8], u64)],
    ) -> Arc<LiveSst> {
        let path = dir.path().join(format!("{file_id}.sst"));
        let mut writer =
            SsTableWriter::new(&path, 4096, 10, CompressionType::None, None, false, 4096).unwrap();
        for &(key, seq) in points {
            let internal = encode_internal_key(&key_of(key), seq, VALUE_TYPE_VALUE);
            writer.add(&internal, b"v").unwrap();
        }
        for &(start, end, seq) in tombstones {
            writer.add_range_tombstone(&key_of(start), &key_of(end), seq);
        }
        let summary = writer.finish().unwrap().unwrap();
        let meta = SsTableMeta {
            file_id,
            smallest_key: summary.smallest_user_key,
            largest_key: summary.largest_user_key,
            file_size: 0,
            num_entries: summary.num_entries,
        };
        LiveSst::new(meta, Arc::new(SsTableReader::open(&path, file_id).unwrap()))
    }

    #[test]
    fn a_deeper_levels_tombstones_are_gathered_before_any_of_its_tables_is_visited() {
        let dir = TempDir::new().unwrap();
        // L1 lists the table holding `k` first and, after it, one holding only
        // a newer tombstone over it.
        let holder = live_table(&dir, 1, &[(b"a", 5), (b"k", 5), (b"m", 5)], &[]);
        let tombstone_only = live_table(&dir, 2, &[], &[(b"c", b"p", 10)]);
        let mut version = Version::new();
        version.levels[1] = vec![holder, tombstone_only];
        let view = ReadView {
            active: Arc::new(MemTable::new(&MemTableConfig::default()).unwrap()),
            frozen: Vec::new(),
            version: Arc::new(version),
        };
        let at = |place: &str, rt| (place.to_string(), rt);

        // The table without entries is not visited, but its tombstone is
        // seen by the one that holds the key.
        let (visited, ended) = walk_all(&view, b"k", u64::MAX);
        assert_eq!(visited, [at("active", 0), at("L1 0", 10)]);
        assert_eq!(ended, 10);

        // Outside the tombstone's range, the holder sees none.
        let (visited, ended) = walk_all(&view, b"a", u64::MAX);
        assert_eq!(visited, [at("active", 0), at("L1 0", 0)]);
        assert_eq!(ended, 0);

        // Outside every table's key range, only the memtable is visited.
        let (visited, ended) = walk_all(&view, b"q", u64::MAX);
        assert_eq!(visited, [at("active", 0)]);
        assert_eq!(ended, 0);
    }
}
