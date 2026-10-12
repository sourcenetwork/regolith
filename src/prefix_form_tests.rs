//! A prefix seek over tables of both prefix-bloom forms
//! (`engine::prefix_call`): the caller-key form every table is written in,
//! and the engine-key form of a table written before it, which only this
//! crate's tests can still write.
//!
//! The rule under test: a prefix seek returns what a full scan of the family
//! returns for that prefix, whichever form each table it meets is in, in
//! level 0 and below it. A table is asked in its own form, so a table of the
//! old form is never ruled out for a key it holds.

use std::collections::BTreeMap;
use std::path::Path;
use std::sync::Arc;

use proptest::prelude::*;

use super::*;
use crate::engine::block_cache::BlockCache;
use crate::engine::prefix_call::{PrefixForm, writing_engine_key_form};

/// Through the first `:` of a key, the colon included; a key without one has
/// no prefix. It keeps the trait's `extract_query`, which lets a seek ask
/// only for a prefix that is a whole extracted one.
struct ThroughColon;

impl PrefixExtractor for ThroughColon {
    fn extract<'a>(&self, key: &'a [u8]) -> Option<&'a [u8]> {
        let colon = key.iter().position(|byte| *byte == b':')?;
        Some(&key[..=colon])
    }

    fn name(&self) -> &'static str {
        "ThroughColon"
    }
}

/// The form of each live table's prefix bloom, level by level.
fn forms(db: &Db) -> Vec<Vec<Option<PrefixForm>>> {
    let cache = BlockCache::new(0);
    db.engine
        .current_version()
        .levels
        .iter()
        .map(|level| {
            level
                .iter()
                .map(|table| table.reader.prefix_form(&cache).unwrap())
                .collect()
        })
        .collect()
}

/// Every form among the live tables that have a prefix bloom.
fn forms_in_use(db: &Db) -> Vec<PrefixForm> {
    let mut forms: Vec<_> = forms(db).into_iter().flatten().flatten().collect();
    forms.sort_by_key(|form| form.tag());
    forms.dedup();
    forms
}

/// What `iter` yields from where it stands to where it stops.
fn rest(mut iter: CfIter<'_>) -> Vec<(Vec<u8>, Vec<u8>)> {
    let mut rows = Vec::new();
    while iter.valid() {
        rows.push((iter.key().unwrap().to_vec(), iter.value().unwrap().to_vec()));
        iter.next();
    }
    iter.status().unwrap();
    rows
}

/// The rows of `family` (`None` for the default one) a prefix seek yields.
fn seek(db: &Db, family: Option<&ColumnFamilyHandle>, prefix: &[u8]) -> Vec<(Vec<u8>, Vec<u8>)> {
    let mut iter = family.map_or_else(|| db.iter(), |cf| db.iter_cf(cf));
    iter.seek_prefix(prefix);
    rest(iter)
}

/// The rows of `family` a full scan yields that start with `prefix`.
fn scan(db: &Db, family: Option<&ColumnFamilyHandle>, prefix: &[u8]) -> Vec<(Vec<u8>, Vec<u8>)> {
    let mut iter = family.map_or_else(|| db.iter(), |cf| db.iter_cf(cf));
    iter.seek_to_first();
    let mut rows = rest(iter);
    rows.retain(|(key, _)| key.starts_with(prefix));
    rows
}

/// How many tables a prefix seek in `family` ruled out by their prefix
/// bloom. The seek must also find what a full scan finds.
fn ruled_out(
    db: &Db,
    stats: &Statistics,
    family: Option<&ColumnFamilyHandle>,
    prefix: &[u8],
) -> u64 {
    let before = stats.get_ticker(Ticker::BloomFilterUseful);
    let found = seek(db, family, prefix);
    let ruled_out = stats.get_ticker(Ticker::BloomFilterUseful) - before;
    assert_eq!(found, scan(db, family, prefix));
    ruled_out
}

/// Options for an in-memory database with `extractor`, no compaction worker,
/// and a compaction due once level 0 holds `trigger` tables, and the
/// statistics it reports to.
fn options(extractor: Arc<dyn PrefixExtractor>, trigger: usize) -> (Options, Arc<Statistics>) {
    let stats = Arc::new(Statistics::new());
    let options = Options::memory()
        .l0_compaction_trigger(trigger)
        .prefix_extractor(Some(extractor))
        .statistics(Some(Arc::clone(&stats)));
    (options, stats)
}

/// A flush writes the caller-key form; only the test switch writes the old
/// one, and a compaction that rewrites an old table writes it in the
/// caller-key form.
#[test]
fn only_the_test_switch_writes_the_old_form_and_a_compaction_rewrites_it() {
    let (options, stats) = options(Arc::new(FixedLengthPrefix(4)), 1_000);
    let db = Db::open("prefix-forms", options).unwrap();
    db.put(b"aaaa:1", b"new").unwrap();
    db.put(b"cccc:1", b"new").unwrap();
    db.flush().unwrap();
    assert_eq!(forms(&db)[0], [Some(PrefixForm::CallerKey)]);

    db.put(b"aaaa:2", b"old").unwrap();
    writing_engine_key_form(|| db.flush()).unwrap();
    assert_eq!(
        forms(&db)[0],
        [Some(PrefixForm::CallerKey), Some(PrefixForm::EngineKey)]
    );

    // The old table's four-byte prefixes are family ids, so it rules out no
    // prefix of the family it holds; the new one rules out what it lacks.
    assert_eq!(ruled_out(&db, &stats, None, b"bbbb"), 1);
    assert_eq!(ruled_out(&db, &stats, None, b"aaaa"), 0);

    // The two tables overlap, so the compaction rewrites both into one,
    // which rules out by the caller's key what the old one could not.
    db.compact_range(None, None).wait().unwrap();
    assert!(forms(&db)[0].is_empty());
    assert_eq!(forms_in_use(&db), [PrefixForm::CallerKey]);
    let row = |key: &[u8], value: &[u8]| (key.to_vec(), value.to_vec());
    assert_eq!(
        seek(&db, None, b"aaaa"),
        [row(b"aaaa:1", b"new"), row(b"aaaa:2", b"old")]
    );
    assert_eq!(ruled_out(&db, &stats, None, b"bbbb"), 1);
    assert_eq!(ruled_out(&db, &stats, None, b"cccc"), 0);
}

/// The database regolith 0.1.9 wrote with an eight-byte extractor
/// (`tests/fixtures/v0_1_9_prefix`; `tests/upgrade_from_0_1_9.rs` says what
/// it holds), copied into memory.
fn written_by_0_1_9() -> Arc<MemEnv> {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/v0_1_9_prefix");
    let env = Arc::new(MemEnv::new());
    for file in [
        "MANIFEST",
        "sst/000003.sst",
        "sst/000005.sst",
        "sst/000007.sst",
        "wal/wal_000006.log",
    ] {
        let to = Path::new("/db").join(file);
        env.create_dir_all(to.parent().unwrap()).unwrap();
        env.write(&to, &std::fs::read(fixture.join(file)).unwrap())
            .unwrap();
    }
    env
}

/// The tables a release from before the forms wrote read as the engine-key
/// form, are asked that way, and are in the caller-key form once a
/// compaction has rewritten them.
#[test]
fn tables_written_by_0_1_9_read_as_the_old_form_until_a_compaction_rewrites_them() {
    let (options, stats) = options(Arc::new(FixedLengthPrefix(8)), 2);
    let db = Db::open("/db", options.env(written_by_0_1_9())).unwrap();
    let named = db.column_family("named").expect("the family 0.1.9 created");
    assert_eq!(forms(&db)[0], [Some(PrefixForm::EngineKey); 3]);

    // Eight bytes of the engine's key are the family id and four bytes of
    // the caller's: the default family's `tenA` is in two of the tables.
    assert_eq!(ruled_out(&db, &stats, None, b"tenA0009"), 1);
    assert_eq!(ruled_out(&db, &stats, None, b"tenZ0001"), 3);
    assert_eq!(ruled_out(&db, &stats, Some(&named), b"tenA0009"), 2);
    assert_eq!(seek(&db, None, b"tenA0001").len(), 2);
    assert_eq!(seek(&db, Some(&named), b"tenA0001").len(), 1);

    assert_eq!(db.compact_step().unwrap(), CompactionOutcome::DidWork);
    assert_eq!(forms_in_use(&db), [PrefixForm::CallerKey]);
    assert_eq!(seek(&db, None, b"tenA0001").len(), 2);
    assert_eq!(seek(&db, Some(&named), b"tenA0001").len(), 1);
    // Now the filter is on eight bytes of the caller's key.
    assert_eq!(ruled_out(&db, &stats, None, b"tenA0009"), 1);
    assert_eq!(ruled_out(&db, &stats, None, b"tenA0001"), 0);
}

/// The extractor a case runs with.
#[derive(Clone, Debug)]
enum Extractor {
    Fixed(usize),
    ThroughColon,
}

impl Extractor {
    fn build(&self) -> Arc<dyn PrefixExtractor> {
        match self {
            Self::Fixed(width) => Arc::new(FixedLengthPrefix(*width)),
            Self::ThroughColon => Arc::new(ThroughColon),
        }
    }
}

fn extractor() -> impl Strategy<Value = Extractor> {
    prop_oneof![
        (0usize..6).prop_map(Extractor::Fixed),
        Just(Extractor::ThroughColon),
    ]
}

/// A key, or a seek's prefix, over an alphabet small enough that keys share
/// prefixes and seeks find them.
fn bytes(len: std::ops::Range<usize>) -> impl Strategy<Value = Vec<u8>> {
    prop::collection::vec(prop_oneof![Just(b'a'), Just(b'b'), Just(b':')], len)
}

/// A write: the family (0 is the default one), the key, and the value, or
/// `None` for a delete.
type Write = (usize, Vec<u8>, Option<u8>);

fn write() -> impl Strategy<Value = Write> {
    (
        0usize..3,
        bytes(1..5),
        prop::option::weighted(0.8, any::<u8>()),
    )
}

/// What happens to the memtable after a batch of writes.
#[derive(Clone, Copy, Debug)]
enum After {
    /// Flushed to a table of the form tables are written in.
    Flush,
    /// Flushed to a table of the form tables were written in before.
    FlushOldForm,
    /// Flushed, then one compaction pass, which may move tables down.
    FlushAndCompact,
    /// Left in the memtable.
    Nothing,
}

fn after() -> impl Strategy<Value = After> {
    prop_oneof![
        3 => Just(After::Flush),
        3 => Just(After::FlushOldForm),
        2 => Just(After::FlushAndCompact),
        1 => Just(After::Nothing),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(96))]

    /// Over random keys, families, extractors and a random split of tables
    /// between the two forms, some of them compacted below level 0 (into
    /// one table, or into a table for each key), a prefix seek returns
    /// exactly the rows a full scan has under that prefix, and they are the
    /// rows a model of the writes holds.
    #[test]
    fn a_prefix_seek_over_both_forms_returns_what_a_full_scan_returns(
        extractor in extractor(),
        trigger in prop_oneof![Just(2usize), Just(4), Just(1_000)],
        table_size in prop_oneof![Just(1u64), Just(64 << 20)],
        batches in prop::collection::vec((prop::collection::vec(write(), 1..8), after()), 1..7),
        seeks in prop::collection::vec((0usize..3, bytes(0..5)), 1..12),
    ) {
        let (options, _stats) = options(extractor.build(), trigger);
        let db = Db::open("prefix-forms", options.target_file_size(table_size)).unwrap();
        let named = [
            db.create_column_family("one").unwrap(),
            db.create_column_family("two").unwrap(),
        ];
        let family = |index: usize| index.checked_sub(1).map(|named_index| &named[named_index]);
        let mut model: BTreeMap<(usize, Vec<u8>), Vec<u8>> = BTreeMap::new();

        for (writes, after) in &batches {
            for (index, key, value) in writes {
                match (family(*index), value) {
                    (None, Some(value)) => db.put(key, &[*value]),
                    (None, None) => db.delete(key),
                    (Some(cf), Some(value)) => db.put_cf(cf, key, &[*value]),
                    (Some(cf), None) => db.delete_cf(cf, key),
                }
                .unwrap();
                match value {
                    Some(value) => model.insert((*index, key.clone()), vec![*value]),
                    None => model.remove(&(*index, key.clone())),
                };
            }
            match after {
                After::Flush => db.flush().unwrap(),
                After::FlushOldForm => writing_engine_key_form(|| db.flush()).unwrap(),
                After::FlushAndCompact => {
                    db.flush().unwrap();
                    db.compact_step().unwrap();
                }
                After::Nothing => {}
            }
        }

        for (index, prefix) in &seeks {
            let expected: Vec<(Vec<u8>, Vec<u8>)> = model
                .range((*index, prefix.clone())..)
                .take_while(|((held, key), _)| held == index && key.starts_with(prefix))
                .map(|((_, key), value)| (key.clone(), value.clone()))
                .collect();
            prop_assert_eq!(
                &seek(&db, family(*index), prefix),
                &expected,
                "seek for {:?} in family {} with {:?}; tables {:?}",
                prefix, index, extractor, forms(&db)
            );
            prop_assert_eq!(&scan(&db, family(*index), prefix), &expected);
        }
    }
}
