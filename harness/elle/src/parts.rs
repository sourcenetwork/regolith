//! The value stored under a document whose parts are lists, and the merge
//! operator that appends to a part.
//!
//! A document is its parts separated by `;`, each `part=` followed by the
//! part's list in the format of [`crate::list`], sorted by part
//! (`0=1,2;1=7`). A merge operand has the same form and names the parts it
//! appends to. Appending part by part is associative and keeps operand order,
//! so the engine may fold a chain in whatever grouping of adjacent operands
//! it meets. An operand touches exactly the parts it names, which is what
//! `touches` reports.

use std::collections::BTreeMap;

use regolith::MergeOperator;

use crate::list;

/// Parts in one document: two list-append keys share a key of the database.
pub const PARTS: i64 = 2;

/// The parts a value or an operand holds, or `None` when it is neither.
fn decode(raw: &[u8]) -> Option<BTreeMap<u32, Vec<i64>>> {
    let text = std::str::from_utf8(raw).ok()?;
    text.split(';')
        .filter(|pair| !pair.is_empty())
        .map(|pair| {
            let (part, elements) = pair.split_once('=')?;
            Some((part.parse().ok()?, list::decode(Some(elements.as_bytes()))?))
        })
        .collect()
}

fn encode(parts: &BTreeMap<u32, Vec<i64>>) -> Vec<u8> {
    let pairs: Vec<String> = parts
        .iter()
        .map(|(part, elements)| {
            let elements = list::encode(elements);
            format!("{part}={}", String::from_utf8_lossy(&elements))
        })
        .collect();
    pairs.join(";").into_bytes()
}

/// Appends each part of `more` to the same part of `parts`.
fn extend(parts: &mut BTreeMap<u32, Vec<i64>>, more: BTreeMap<u32, Vec<i64>>) {
    for (part, elements) in more {
        parts.entry(part).or_default().extend(elements);
    }
}

/// The operand that appends `value` to `part`.
pub fn append(part: u32, value: i64) -> Vec<u8> {
    encode(&BTreeMap::from([(part, vec![value])]))
}

/// The list `part` holds in a document, `None` when the document is absent
/// or nothing was ever appended to the part.
pub fn list_of(raw: Option<&[u8]>, part: u32) -> Option<Vec<i64>> {
    decode(raw?)?.remove(&part)
}

/// Appends to the parts each operand names, oldest operand first.
pub struct AppendToParts;

impl MergeOperator for AppendToParts {
    fn full_merge(&self, _key: &[u8], base: Option<&[u8]>, operands: &[&[u8]]) -> Option<Vec<u8>> {
        let mut parts = base.map_or_else(|| Some(BTreeMap::new()), decode)?;
        for operand in operands {
            extend(&mut parts, decode(operand)?);
        }
        Some(encode(&parts))
    }

    fn partial_merge(&self, _key: &[u8], left: &[u8], right: &[u8]) -> Option<Vec<u8>> {
        let mut parts = decode(left)?;
        extend(&mut parts, decode(right)?);
        Some(encode(&parts))
    }

    fn touches(&self, _key: &[u8], operand: &[u8], parts: &[u32]) -> bool {
        // An operand that cannot be read is taken to change everything.
        decode(operand).is_none_or(|named| named.keys().any(|part| parts.contains(part)))
    }

    fn name(&self) -> &'static str {
        "elle-append-to-parts"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Operands chosen so that every pair overlaps, is disjoint or is empty.
    const OPERANDS: [&[u8]; 4] = [b"", b"0=1", b"1=2,3", b"0=4;1=5"];

    fn full(base: Option<&[u8]>, operands: &[&[u8]]) -> Vec<u8> {
        AppendToParts.full_merge(b"k", base, operands).unwrap()
    }

    fn partial(left: &[u8], right: &[u8]) -> Vec<u8> {
        AppendToParts.partial_merge(b"k", left, right).unwrap()
    }

    #[test]
    fn an_operand_appends_to_its_part_and_leaves_the_others() {
        assert_eq!(full(None, &[&append(0, 7)]), b"0=7");
        assert_eq!(full(Some(b"0=7"), &[&append(1, 9)]), b"0=7;1=9");
        assert_eq!(full(Some(b"0=7;1=9"), &[&append(0, 8)]), b"0=7,8;1=9");
        assert_eq!(list_of(Some(b"0=7,8;1=9"), 0), Some(vec![7, 8]));
        assert_eq!(list_of(Some(b"0=7,8"), 1), None);
        assert_eq!(list_of(None, 0), None);
    }

    #[test]
    fn partial_merge_is_associative_and_agrees_with_full_merge() {
        for a in OPERANDS {
            for b in OPERANDS {
                for c in OPERANDS {
                    let left_first = partial(&partial(a, b), c);
                    let right_first = partial(a, &partial(b, c));
                    assert_eq!(left_first, right_first);
                    assert_eq!(left_first, full(Some(a), &[b, c]));
                    assert_eq!(left_first, full(None, &[a, b, c]));
                }
            }
        }
        assert_eq!(partial(b"0=1;1=2", b"0=3"), b"0=1,3;1=2");
        assert_eq!(partial(b"0=3", b"0=1;1=2"), b"0=3,1;1=2");
    }

    #[test]
    fn a_folded_operand_touches_what_either_operand_touched() {
        let sets: [&[u32]; 4] = [&[], &[0], &[1], &[0, 1]];
        for a in OPERANDS {
            for b in OPERANDS {
                for parts in sets {
                    let folded = partial(a, b);
                    assert_eq!(
                        AppendToParts.touches(b"k", &folded, parts),
                        AppendToParts.touches(b"k", a, parts)
                            || AppendToParts.touches(b"k", b, parts),
                        "{a:?} {b:?} {parts:?}"
                    );
                }
            }
        }
        assert!(
            AppendToParts.touches(b"k", &[0xff], &[0]),
            "an operand that cannot be read touches everything"
        );
    }
}
