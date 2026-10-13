//! The caller's merge operator on a TTL database, and how a merged key is
//! stored.
//!
//! Each write expires by its own time: a put and each merge operand live
//! the TTL from when they were written, and a read folds the writes of a
//! key that have not expired. A fold cannot be undone, and one value has one
//! time, so the writes of a merged key are not folded where they are stored:
//! the database's merge keeps them apart, each with its time, in one stored
//! value (a *bundle*), and the caller's operator folds the ones that have
//! not expired when the key is read. Compaction drops a write from a bundle
//! once it has expired, which a read was ignoring already, so what a read
//! returns does not depend on which writes a compaction pass met, nor on
//! when it ran.
//!
//! A bundle, after the writes it holds:
//!
//! ```text
//! [write]... ["RTTL"][version 2][newest time: u64 BE]
//! write = [flags: u8 (1 the put the merges apply to, 2 has a time)]
//!         [length: u32 BE][bytes][time: u64 BE, when it has one]
//! ```
//!
//! A write with no time was written past the wrapper (through
//! [`super::DbWithTtl::inner`]): it never expires and a read through the
//! wrapper does not see it, as for a plain value written that way.

use std::sync::Arc;

use super::{TTL_MAGIC, TTL_MAGIC_LEN, TTL_SUFFIX_LEN, TTL_TS_LEN, decode_ttl_suffix};
use crate::options::MergeOperator;

/// The version byte of a bundle's suffix (a plain stamped value has 1).
const BUNDLE_VERSION: u8 = 2;

/// The flag of the put a bundle's merges apply to.
const FLAG_BASE: u8 = 1;

/// The flag of a write that carries the time it was written at.
const FLAG_TIMED: u8 = 2;

/// One write a stored value holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Piece<'a> {
    /// The put the merges after it apply to.
    pub(super) base: bool,
    /// What the caller wrote.
    pub(super) value: &'a [u8],
    /// When, or `None` for a write made past the wrapper.
    pub(super) at: Option<u64>,
}

/// The writes `pieces`, kept apart in one bundle.
pub(super) fn encode<'a>(pieces: impl IntoIterator<Item = Piece<'a>>) -> Vec<u8> {
    let mut out = Vec::new();
    let mut newest = 0u64;
    for piece in pieces {
        let flags = u8::from(piece.base) * FLAG_BASE + u8::from(piece.at.is_some()) * FLAG_TIMED;
        out.push(flags);
        // A write longer than 4 GiB cannot reach a merge: the key and
        // value size limits bound every write far below that.
        out.extend_from_slice(&(piece.value.len() as u32).to_be_bytes());
        out.extend_from_slice(piece.value);
        if let Some(at) = piece.at {
            out.extend_from_slice(&at.to_be_bytes());
            newest = newest.max(at);
        }
    }
    out.extend_from_slice(&TTL_MAGIC);
    out.push(BUNDLE_VERSION);
    out.extend_from_slice(&newest.to_be_bytes());
    out
}

/// The writes `stored` holds when it is a bundle, or `None` when it is not
/// one, or is not a whole one.
pub(super) fn decode(stored: &[u8]) -> Option<Vec<Piece<'_>>> {
    let body_len = stored.len().checked_sub(TTL_SUFFIX_LEN)?;
    let (mut body, suffix) = stored.split_at(body_len);
    if suffix[..TTL_MAGIC_LEN] != TTL_MAGIC || suffix[TTL_MAGIC_LEN] != BUNDLE_VERSION {
        return None;
    }
    let mut pieces = Vec::new();
    while let Some((&flags, rest)) = body.split_first() {
        if flags & !(FLAG_BASE | FLAG_TIMED) != 0 {
            return None;
        }
        let (len, rest) = rest.split_first_chunk::<4>()?;
        let len = usize::try_from(u32::from_be_bytes(*len)).ok()?;
        let (value, rest) = rest.split_at_checked(len)?;
        let (at, rest) = if flags & FLAG_TIMED != 0 {
            let (at, rest) = rest.split_first_chunk::<TTL_TS_LEN>()?;
            (Some(u64::from_be_bytes(*at)), rest)
        } else {
            (None, rest)
        };
        pieces.push(Piece {
            base: flags & FLAG_BASE != 0,
            value,
            at,
        });
        body = rest;
    }
    Some(pieces)
}

/// The writes a stored value or operand holds: a bundle's own, or the one
/// write a plain value or operand is, a put the merges apply to when `base`.
fn pieces_of(stored: &[u8], base: bool) -> Vec<Piece<'_>> {
    if let Some(pieces) = decode(stored) {
        return pieces;
    }
    let piece = match decode_ttl_suffix(stored) {
        Some(decoded) => Piece {
            base,
            value: &stored[..decoded.value_len],
            at: Some(decoded.timestamp),
        },
        None => Piece {
            base,
            value: stored,
            at: None,
        },
    };
    vec![piece]
}

/// What a read returns from the writes `live` of `key`, which have not
/// expired: the put they apply to, folded with the merges after it by the
/// caller's operator. `Ok(None)` when there is none.
pub(super) fn fold(
    operator: Option<&dyn MergeOperator>,
    key: &[u8],
    live: &[Piece<'_>],
) -> crate::Result<Option<Vec<u8>>> {
    let (base, operands) = match live.split_first() {
        None => return Ok(None),
        Some((first, rest)) if first.base => (Some(first.value), rest),
        Some(_) => (None, live),
    };
    if operands.is_empty() {
        return Ok(base.map(<[u8]>::to_vec));
    }
    let Some(operator) = operator else {
        return Err(crate::Error::NoMergeOperator);
    };
    let operands: Vec<&[u8]> = operands.iter().map(|piece| piece.value).collect();
    operator
        .full_merge(key, base, &operands)
        .map(Some)
        .ok_or_else(|| crate::Error::MergeFailed(key.to_vec()))
}

/// The database's merge on a TTL database: it keeps the writes apart, so a
/// read can fold the ones that have not expired.
pub(super) struct TtlMergeOperator {
    pub(super) callers: Arc<dyn MergeOperator>,
}

impl MergeOperator for TtlMergeOperator {
    fn full_merge(&self, _key: &[u8], base: Option<&[u8]>, operands: &[&[u8]]) -> Option<Vec<u8>> {
        let base = base.map(|base| pieces_of(base, true)).unwrap_or_default();
        let operands = operands
            .iter()
            .flat_map(|operand| pieces_of(operand, false));
        Some(encode(base.into_iter().chain(operands)))
    }

    fn partial_merge(&self, _key: &[u8], left: &[u8], right: &[u8]) -> Option<Vec<u8>> {
        Some(encode(
            pieces_of(left, false)
                .into_iter()
                .chain(pieces_of(right, false)),
        ))
    }

    fn touches(&self, key: &[u8], operand: &[u8], parts: &[u32]) -> bool {
        pieces_of(operand, false)
            .iter()
            .any(|piece| self.callers.touches(key, piece.value, parts))
    }

    fn name(&self) -> &'static str {
        self.callers.name()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ttl::stamp;

    /// Concatenates, base first.
    struct Concat;

    impl MergeOperator for Concat {
        fn full_merge(&self, _: &[u8], base: Option<&[u8]>, operands: &[&[u8]]) -> Option<Vec<u8>> {
            let mut out = base.map(<[u8]>::to_vec).unwrap_or_default();
            out.extend(operands.iter().flat_map(|o| o.iter().copied()));
            Some(out)
        }

        fn name(&self) -> &'static str {
            "concat"
        }
    }

    fn piece(base: bool, value: &[u8], at: Option<u64>) -> Piece<'_> {
        Piece { base, value, at }
    }

    #[test]
    fn a_bundle_round_trips_every_write_and_its_time() {
        let pieces = [
            piece(true, b"base", Some(7)),
            piece(false, b"", Some(9)),
            piece(false, b"raw", None),
        ];
        let bundle = encode(pieces);
        assert_eq!(decode(&bundle).unwrap(), pieces);
        // It is not a plain stamped value, and a plain one is not a bundle.
        assert!(decode_ttl_suffix(&bundle).is_none());
        assert!(decode(&stamp(b"v", 3)).is_none());
        assert_eq!(decode(&encode([])).unwrap(), []);
    }

    #[test]
    fn a_damaged_bundle_is_not_read_as_one() {
        let bundle = encode([piece(false, b"op", Some(1))]);
        let body = bundle.len() - TTL_SUFFIX_LEN;
        // A byte of the body missing: the last write runs past it.
        let mut short = bundle[..body - 1].to_vec();
        short.extend_from_slice(&bundle[body..]);
        assert!(decode(&short).is_none());
        // A flag no write has.
        let mut flagged = bundle.clone();
        flagged[0] = 0x80;
        assert!(decode(&flagged).is_none());
        // A length past the body.
        let mut long_length = bundle.clone();
        long_length[1..5].copy_from_slice(&u32::MAX.to_be_bytes());
        assert!(decode(&long_length).is_none());
    }

    #[test]
    fn a_merge_keeps_every_write_apart_with_its_time() {
        let op = TtlMergeOperator {
            callers: Arc::new(Concat),
        };
        let merged = op
            .full_merge(b"k", Some(&stamp(b"a", 1)), &[&stamp(b"b", 2), b"raw"])
            .unwrap();
        assert_eq!(
            decode(&merged).unwrap(),
            [
                piece(true, b"a", Some(1)),
                piece(false, b"b", Some(2)),
                piece(false, b"raw", None)
            ]
        );
        // Folded again as a base, and two operands folded ahead of it.
        let ops = op
            .partial_merge(b"k", &stamp(b"c", 3), &stamp(b"d", 4))
            .unwrap();
        let again = op.full_merge(b"k", Some(&merged), &[&ops]).unwrap();
        let values: Vec<&[u8]> = decode(&again).unwrap().iter().map(|p| p.value).collect();
        assert_eq!(values, [&b"a"[..], b"b", b"raw", b"c", b"d"]);
    }

    #[test]
    fn a_fold_applies_the_live_merges_to_the_live_put() {
        let concat = Concat;
        let live = [piece(true, b"a", Some(1)), piece(false, b"b", Some(2))];
        assert_eq!(
            fold(Some(&concat), b"k", &live).unwrap(),
            Some(b"ab".to_vec())
        );
        // The put expired: the merges alone.
        assert_eq!(
            fold(Some(&concat), b"k", &live[1..]).unwrap(),
            Some(b"b".to_vec())
        );
        // Only the put: no operator is asked.
        assert_eq!(fold(None, b"k", &live[..1]).unwrap(), Some(b"a".to_vec()));
        assert_eq!(fold(None, b"k", &[]).unwrap(), None);
        assert!(matches!(
            fold(None, b"k", &live),
            Err(crate::Error::NoMergeOperator)
        ));
    }
}
