//! The value stored under a list-append key, and the merge operator that
//! appends to it.
//!
//! A list is its elements as comma-separated decimals (`1,2,3`). A merge
//! operand is a list of the elements to append. Concatenation is
//! associative and keeps operand order, which is all a merge operator may
//! assume: the engine folds a chain at read time, at flush and in
//! compaction, in whatever grouping of adjacent operands it meets.

use regolith::MergeOperator;

/// Join `lists` with the element separator, skipping empty ones. The
/// encoder and the merge operator both go through this, so they cannot
/// disagree on the format.
fn concat<T: AsRef<[u8]>>(lists: impl IntoIterator<Item = T>) -> Vec<u8> {
    let mut out = Vec::new();
    for list in lists.into_iter().filter(|list| !list.as_ref().is_empty()) {
        if !out.is_empty() {
            out.push(b',');
        }
        out.extend_from_slice(list.as_ref());
    }
    out
}

pub fn encode(list: &[i64]) -> Vec<u8> {
    concat(list.iter().map(i64::to_string))
}

/// `None` when the key is absent or its value is not a list.
pub fn decode(raw: Option<&[u8]>) -> Option<Vec<i64>> {
    let text = std::str::from_utf8(raw?).ok()?;
    if text.is_empty() {
        return Some(Vec::new());
    }
    text.split(',')
        .map(|part| part.parse::<i64>().ok())
        .collect()
}

/// Appends operands to the base list, oldest first.
pub struct ListAppend;

impl MergeOperator for ListAppend {
    fn full_merge(&self, _key: &[u8], base: Option<&[u8]>, operands: &[&[u8]]) -> Option<Vec<u8>> {
        Some(concat(base.into_iter().chain(operands.iter().copied())))
    }

    fn partial_merge(&self, _key: &[u8], left: &[u8], right: &[u8]) -> Option<Vec<u8>> {
        Some(concat([left, right]))
    }

    fn name(&self) -> &'static str {
        "elle-list-append"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Lists chosen so that every empty/non-empty and one/many-element
    /// combination of three operands occurs.
    const LISTS: [&[i64]; 4] = [&[], &[1], &[2, 3], &[4, 5, 6]];

    fn partial(left: &[u8], right: &[u8]) -> Vec<u8> {
        ListAppend.partial_merge(b"k", left, right).unwrap()
    }

    fn full(base: Option<&[u8]>, operands: &[&[u8]]) -> Vec<u8> {
        ListAppend.full_merge(b"k", base, operands).unwrap()
    }

    #[test]
    fn encode_and_decode_round_trip() {
        for list in LISTS {
            assert_eq!(decode(Some(&encode(list))).as_deref(), Some(list));
        }
        assert_eq!(encode(&[7, 8]), b"7,8");
    }

    #[test]
    fn a_missing_or_malformed_value_is_not_a_list() {
        assert_eq!(decode(None), None);
        assert_eq!(decode(Some(b"1,x")), None);
        assert_eq!(decode(Some(&[0xff])), None);
    }

    #[test]
    fn full_merge_appends_operands_to_the_base_in_order() {
        assert_eq!(full(Some(b"9"), &[b"1", b"2,3"]), b"9,1,2,3");
        assert_eq!(full(None, &[b"1", b"2"]), b"1,2");
        assert_eq!(full(Some(b"9"), &[]), b"9");
        assert_eq!(full(None, &[]), b"");
        assert_eq!(full(Some(b""), &[b"1"]), b"1");
    }

    #[test]
    fn partial_merge_is_associative_and_order_preserving() {
        for a in LISTS {
            for b in LISTS {
                for c in LISTS {
                    let (a, b, c) = (encode(a), encode(b), encode(c));
                    let left_first = partial(&partial(&a, &b), &c);
                    let right_first = partial(&a, &partial(&b, &c));
                    assert_eq!(left_first, right_first);
                    // Folding the chain pairwise equals applying it to the
                    // base in one step, whatever the grouping.
                    assert_eq!(left_first, full(Some(&a), &[&b, &c]));
                    assert_eq!(left_first, full(None, &[&a, &b, &c]));
                }
            }
        }
        assert_eq!(partial(b"1,2", b"3"), b"1,2,3");
        assert_eq!(partial(b"3", b"1,2"), b"3,1,2");
    }
}
