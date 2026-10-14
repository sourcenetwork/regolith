//! What a validated scan ([`crate::ScanCheck::Range`]) records: the key range
//! it covered, so the commit can refuse any write that landed in it.
//!
//! One [`RangeRecord`] per cursor, registered with the transaction when the
//! cursor is made and moved forward by the cursor at the end of every page.
//! It covers exactly what the caller consumed: from the scan's start to the
//! last key handed out, or to the end of the range once the scan was
//! exhausted. A cursor that stops early validates only what it read. At
//! commit the records become disjoint [`RangeCheck`]s, overlapping and
//! touching ones coalesced.

use std::sync::Arc;

use crate::engine::RangeCheck;
use crate::sync::internal::Mutex;

/// A key range `[lo, hi)` in prefixed keys, empty when `hi <= lo`.
pub(super) struct RangeRecord {
    // vertexia: a mutex, taken once per page by the cursor and once per record
    // by the commit; the commit also reads it while a cursor is mid-page.
    span: Mutex<(Vec<u8>, Vec<u8>)>,
}

impl RangeRecord {
    /// A record covering `[lo, hi)`.
    pub(super) fn new(lo: Vec<u8>, hi: Vec<u8>) -> Arc<Self> {
        Arc::new(Self {
            span: Mutex::new((lo, hi)),
        })
    }

    /// Move the exclusive upper bound, for a forward cursor.
    pub(super) fn set_hi(&self, hi: &[u8]) {
        let mut span = self.span.lock();
        span.1.clear();
        span.1.extend_from_slice(hi);
    }

    /// Move the inclusive lower bound, for a reverse cursor.
    pub(super) fn set_lo(&self, lo: &[u8]) {
        let mut span = self.span.lock();
        span.0.clear();
        span.0.extend_from_slice(lo);
    }

    fn get(&self) -> (Vec<u8>, Vec<u8>) {
        self.span.lock().clone()
    }
}

/// The records as the ranges a commit validates against `observed_seq`:
/// empty ones dropped, the rest sorted and disjoint.
pub(super) fn checks(records: &[Arc<RangeRecord>], observed_seq: u64) -> Vec<RangeCheck> {
    let mut spans: Vec<(Vec<u8>, Vec<u8>)> = records
        .iter()
        .map(|record| record.get())
        .filter(|(lo, hi)| lo < hi)
        .collect();
    spans.sort_unstable();
    let mut merged: Vec<RangeCheck> = Vec::with_capacity(spans.len());
    for (lo, hi) in spans {
        match merged.last_mut() {
            Some(prev) if lo <= prev.hi => prev.hi = prev.hi.clone().max(hi),
            _ => merged.push(RangeCheck {
                lo,
                hi,
                observed_seq,
            }),
        }
    }
    merged
}

#[cfg(test)]
mod tests {
    use super::*;

    fn record(lo: &[u8], hi: &[u8]) -> Arc<RangeRecord> {
        RangeRecord::new(lo.to_vec(), hi.to_vec())
    }

    fn spans(checks: &[RangeCheck]) -> Vec<(&[u8], &[u8])> {
        checks
            .iter()
            .map(|c| (c.lo.as_slice(), c.hi.as_slice()))
            .collect()
    }

    #[test]
    fn overlapping_and_touching_records_coalesce_and_empty_ones_drop() {
        let records = [
            record(b"m", b"p"),
            record(b"b", b"d"),
            record(b"p", b"q"),
            record(b"c", b"e"),
            record(b"x", b"x"),
            record(b"z", b"y"),
        ];
        let got = checks(&records, 7);
        assert_eq!(
            spans(&got),
            [(&b"b"[..], &b"e"[..]), (&b"m"[..], &b"q"[..])]
        );
        assert!(got.iter().all(|check| check.observed_seq == 7));
    }

    #[test]
    fn a_record_moved_by_its_cursor_is_read_as_moved() {
        let forward = record(b"a", b"a");
        assert!(checks(&[Arc::clone(&forward)], 1).is_empty());
        forward.set_hi(b"f\0");
        assert_eq!(spans(&checks(&[forward], 1)), [(&b"a"[..], &b"f\0"[..])]);

        let reverse = record(b"z", b"z");
        reverse.set_lo(b"q");
        assert_eq!(spans(&checks(&[reverse], 1)), [(&b"q"[..], &b"z"[..])]);
    }
}
