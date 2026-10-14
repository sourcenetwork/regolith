//! A flush publishes its table and retires its memtable as one view: no
//! view holds both, so no read sees the memtable's entries twice.

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use crate::{Db, MergeOperator, Options};

/// Concatenates operands onto the base, so an operand applied twice shows.
struct Append;

impl MergeOperator for Append {
    fn full_merge(&self, _key: &[u8], base: Option<&[u8]>, operands: &[&[u8]]) -> Option<Vec<u8>> {
        let mut out = base.map(<[u8]>::to_vec).unwrap_or_default();
        for operand in operands {
            out.extend_from_slice(operand);
        }
        Some(out)
    }

    fn partial_merge(&self, _key: &[u8], left: &[u8], right: &[u8]) -> Option<Vec<u8>> {
        let mut out = left.to_vec();
        out.extend_from_slice(right);
        Some(out)
    }

    fn name(&self) -> &'static str {
        "append"
    }
}

/// Reads made right after the flush published the version holding its
/// table see each merge operand once, by point lookup and by scan. With the
/// memtable retired in a later publication, the view in between held the
/// memtable and its table at once, and both reads returned "abab".
#[test]
fn reads_right_after_a_flush_installs_its_table_count_each_operand_once() {
    let dir = tempfile::tempdir().unwrap();
    let db = Arc::new(
        Db::open(
            dir.path(),
            Options {
                max_background_compactions: 0,
                merge_operator: Some(Arc::new(Append)),
                ..Options::default()
            },
        )
        .unwrap(),
    );
    db.merge(b"k", b"a").unwrap();
    db.merge(b"k", b"b").unwrap();
    let ran = Arc::new(AtomicBool::new(false));
    {
        let (db, ran) = (Arc::clone(&db), Arc::clone(&ran));
        super::after_next_flush_install(move || {
            assert_eq!(
                db.get(b"k").unwrap(),
                Some(b"ab".to_vec()),
                "a point read in the flush's window applied an operand twice"
            );
            assert_eq!(
                db.scan(None, None).unwrap(),
                vec![(b"k".to_vec(), b"ab".to_vec())],
                "a scan in the flush's window applied an operand twice"
            );
            ran.store(true, Ordering::Release);
        });
    }
    db.flush().unwrap();
    assert!(ran.load(Ordering::Acquire), "setup: the flush ran its hook");
    assert_eq!(db.get(b"k").unwrap(), Some(b"ab".to_vec()));
}
