//! Reserving a range of a `u64` counter in the ordered step.
//!
//! The counter lives at a key as the last value reserved, eight big-endian
//! bytes, absent meaning zero. `allocate` takes a slot of the commit ring
//! like a write: when its turn comes, whichever thread decides the slot reads
//! the counter from the view, which by then holds every commit decided before
//! it, reserves the next `n` values, and logs the new counter as a write of
//! its own. This follows `Allocate.tla` and `Allocate.lean`:
//!
//! - The record is in the WAL before `allocate` returns, so before any commit
//!   that uses a value from it, because that commit starts after `allocate`
//!   returned. A crash that keeps a prefix of the log and a surviving use
//!   therefore keeps the allocation, and the counter recovers at or above
//!   every value in use. Nothing is handed out ahead of the log (RED
//!   LogAfterUse), and the counter is never part of a transaction's write set
//!   (RED InTxn), so it never conflicts.
//! - The record asks for no sync of its own. It becomes durable with the next
//!   sync, at the latest with the first commit that uses one of its values,
//!   which is ordered after it. The caller waits for the device only when a
//!   commit ahead of it asked for `Immediate` and its sync is under way: the
//!   reservation is handed out once its slot is published, so a failed sync
//!   never hands out a value the log lost.
//! - It does not wait for write capacity. A stall delays commits, not the
//!   counter, and the record is a few bytes.

use std::io;
use std::ops::Range;

use super::super::RegolithEngine;
use super::descriptor::{After, Decision, Descriptor, FAILED, Verdict as Fate, Work};
use crate::WriteBatchOp;
use crate::sync::internal::Arc as RingArc;

impl RegolithEngine {
    /// Reserves `n` values of the counter at `key` (column-family prefixed)
    /// and returns them as a range. `n == 0` reserves nothing and writes
    /// nothing: the range is empty and starts at the next value.
    ///
    /// The counter holds the last value reserved, so the range starts one
    /// past it. A counter that would pass `u64::MAX - 1` is refused with
    /// `InvalidInput`, since a `Range<u64>` cannot end past `u64::MAX`; so is
    /// a counter that holds anything but eight bytes. Neither changes the
    /// counter.
    pub(crate) fn allocate(&self, key: Vec<u8>, n: u64) -> io::Result<Range<u64>> {
        self.ensure_writable()?;
        let pipe = self.pipe()?;
        let desc = RingArc::new(Descriptor::new(Work::Allocate { key, n }));
        let index = self.enter(pipe, &desc);
        self.drive(pipe, index, &desc);
        if desc.is(FAILED) {
            return Err(desc.failure.take().unwrap_or_else(|| {
                io::Error::other("the write-ahead log failed and this reservation was discarded")
            }));
        }
        match desc.decision().map(|decision| &decision.verdict) {
            Some(Fate::Allocated(range)) => Ok(range.clone()),
            Some(Fate::Refused(err)) => Err(crate::Error::clone_io(err)),
            _ => Err(io::Error::other(
                "a counter reservation settled as something else",
            )),
        }
    }

    /// Decide a reservation of `n` values of the counter at `key` from
    /// `base`: read the counter, which the view holds as of every commit
    /// decided before this slot, and set the verdict and the put that logs
    /// the new counter.
    pub(super) fn decide_allocation(
        &self,
        key: &[u8],
        n: u64,
        base: &After,
        decision: &mut Decision,
    ) -> io::Result<()> {
        let _ = base;
        let view = self.view.load();
        let last = self.read_u64_in_view(key, &view)?.unwrap_or(0);
        let first = last.saturating_add(1);
        if n == 0 {
            decision.verdict = Fate::Allocated(first..first);
            return Ok(());
        }
        let end = first
            .checked_add(n)
            .filter(|_| last < u64::MAX)
            .ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!(
                        "the counter cannot reserve {n} more values below the largest 64-bit number"
                    ),
                )
            })?;
        decision.verdict = Fate::Allocated(first..end);
        decision.batch = Some(vec![WriteBatchOp::Put {
            key: key.to_vec(),
            value: (end - 1).to_be_bytes().to_vec(),
        }]);
        Ok(())
    }
}
