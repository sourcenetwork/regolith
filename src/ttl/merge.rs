//! The caller's merge operator on a TTL database.
//!
//! Every value and every merge operand written through [`super::DbWithTtl`]
//! carries the time it was written at behind it. The caller's operator
//! knows nothing of that, so it is shown what the caller wrote, and what it
//! returns is given the time of the newest write it folded.
//!
//! A merge is a write: it gives the value a new TTL, as a put would. So
//! what a merge folds is the value as it stood when the merge was written,
//! and a value that had already expired by then is not part of it: the
//! merge starts the value over, as a put after the expiry would. That is
//! decided by the times the writes carry, never by the clock when the fold
//! runs, so a read and every compaction fold the same writes into the same
//! value, whenever they run.
//!
//! Operands are written oldest first, with times that do not go back. Two
//! operands are not folded ahead of their base: whether the older one
//! started the value over depends on the base, which is not known then.

use std::sync::Arc;

use super::{decode_ttl_suffix, outlived, stamp};
use crate::options::MergeOperator;

/// The caller's operator, behind the timestamps.
pub(super) struct TtlMergeOperator {
    pub(super) callers: Arc<dyn MergeOperator>,
    pub(super) ttl_seconds: u64,
}

/// What the caller wrote, and the time it was written at: `None` for a
/// value written past the wrapper, which carries no time and never expires.
fn unstamp(stamped: &[u8]) -> (&[u8], Option<u64>) {
    match decode_ttl_suffix(stamped) {
        Some(decoded) => (&stamped[..decoded.value_len], Some(decoded.timestamp)),
        None => (stamped, None),
    }
}

impl MergeOperator for TtlMergeOperator {
    fn full_merge(&self, key: &[u8], base: Option<&[u8]>, operands: &[&[u8]]) -> Option<Vec<u8>> {
        let (mut base, mut newest) = match base.map(unstamp) {
            Some((value, at)) => (Some(value), at),
            None => (None, None),
        };
        let mut kept: Vec<&[u8]> = Vec::with_capacity(operands.len());
        for operand in operands {
            let (value, at) = unstamp(operand);
            if let (Some(before), Some(at)) = (newest, at)
                && outlived(self.ttl_seconds, before, at)
            {
                // Everything written before this operand had expired when
                // it was written: the value starts over here.
                base = None;
                kept.clear();
            }
            kept.push(value);
            newest = newest.max(at);
        }
        let merged = self.callers.full_merge(key, base, &kept)?;
        Some(match newest {
            Some(at) => stamp(&merged, at),
            // Nothing it folded carried a time: what the caller's operator
            // returned is a value written past the wrapper.
            None => merged,
        })
    }

    /// Not folded while values expire (module docs): compaction keeps the
    /// operands as they are, and the base's merge folds them.
    fn partial_merge(&self, key: &[u8], left: &[u8], right: &[u8]) -> Option<Vec<u8>> {
        if self.ttl_seconds > 0 {
            return None;
        }
        let ((left, early), (right, late)) = (unstamp(left), unstamp(right));
        let merged = self.callers.partial_merge(key, left, right)?;
        Some(match early.max(late) {
            Some(at) => stamp(&merged, at),
            None => merged,
        })
    }

    fn touches(&self, key: &[u8], operand: &[u8], parts: &[u32]) -> bool {
        self.callers.touches(key, unstamp(operand).0, parts)
    }

    fn name(&self) -> &'static str {
        self.callers.name()
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Mutex;

    use super::*;

    /// The base and the operands of one full merge.
    type Fold = (Option<Vec<u8>>, Vec<Vec<u8>>);

    /// Concatenates, and records the base and operands of each full merge.
    #[derive(Default)]
    struct Concat(Mutex<Vec<Fold>>);

    impl MergeOperator for Concat {
        fn full_merge(&self, _: &[u8], base: Option<&[u8]>, operands: &[&[u8]]) -> Option<Vec<u8>> {
            self.0.lock().unwrap().push((
                base.map(<[u8]>::to_vec),
                operands.iter().map(|o| o.to_vec()).collect(),
            ));
            let mut out = base.map(<[u8]>::to_vec).unwrap_or_default();
            out.extend(operands.iter().flat_map(|o| o.iter().copied()));
            Some(out)
        }

        fn partial_merge(&self, _: &[u8], left: &[u8], right: &[u8]) -> Option<Vec<u8>> {
            Some([left, right].concat())
        }

        fn name(&self) -> &'static str {
            "concat"
        }
    }

    /// An operator around `Concat` with a TTL of `ttl` seconds.
    fn operator(ttl: u64) -> (TtlMergeOperator, Arc<Concat>) {
        let concat = Arc::new(Concat::default());
        let op = TtlMergeOperator {
            callers: concat.clone(),
            ttl_seconds: ttl,
        };
        (op, concat)
    }

    fn last(concat: &Concat) -> Fold {
        concat.0.lock().unwrap().last().cloned().unwrap()
    }

    #[test]
    fn a_full_merge_folds_what_the_caller_wrote_and_keeps_the_newest_time() {
        let (op, concat) = operator(100);
        let merged = op
            .full_merge(
                b"k",
                Some(&stamp(b"a", 950)),
                &[&stamp(b"b", 960), &stamp(b"c", 990)],
            )
            .unwrap();
        assert_eq!(merged, stamp(b"abc", 990));
        assert_eq!(
            last(&concat),
            (Some(b"a".to_vec()), vec![b"b".to_vec(), b"c".to_vec()])
        );
    }

    /// Each write gives the value a new TTL: a chain of writes each within
    /// the TTL of the one before is one value, however old its start.
    #[test]
    fn a_write_within_the_ttl_of_the_one_before_keeps_the_value() {
        let (op, concat) = operator(100);
        let merged = op
            .full_merge(
                b"k",
                Some(&stamp(b"a", 0)),
                &[&stamp(b"b", 90), &stamp(b"c", 180)],
            )
            .unwrap();
        assert_eq!(merged, stamp(b"abc", 180));
        assert_eq!(last(&concat).0, Some(b"a".to_vec()));
    }

    /// A write after the value expired starts it over: what came before is
    /// not folded, whatever the clock reads when the fold runs.
    #[test]
    fn a_write_after_the_value_expired_starts_it_over() {
        let (op, concat) = operator(100);
        let merged = op
            .full_merge(
                b"k",
                Some(&stamp(b"old", 0)),
                &[&stamp(b"x", 50), &stamp(b"new", 300)],
            )
            .unwrap();
        assert_eq!(merged, stamp(b"new", 300));
        assert_eq!(last(&concat), (None, vec![b"new".to_vec()]));
    }

    #[test]
    fn a_value_written_past_the_wrapper_is_folded_as_it_is() {
        let (op, _) = operator(100);
        assert_eq!(op.full_merge(b"k", Some(b"raw"), &[b"+"]).unwrap(), b"raw+");
        assert_eq!(
            op.full_merge(b"k", Some(b"raw"), &[&stamp(b"+", 990)])
                .unwrap(),
            stamp(b"raw+", 990)
        );
    }

    #[test]
    fn operands_are_folded_ahead_of_their_base_only_when_nothing_expires() {
        let (op, _) = operator(100);
        assert_eq!(
            op.partial_merge(b"k", &stamp(b"x", 1), &stamp(b"y", 2)),
            None
        );
        let (op, _) = operator(0);
        assert_eq!(
            op.partial_merge(b"k", &stamp(b"x", 1), &stamp(b"y", 2)),
            Some(stamp(b"xy", 2))
        );
    }
}
