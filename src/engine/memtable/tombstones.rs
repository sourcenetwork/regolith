//! A memtable's range tombstones: an append-only log that readers walk
//! without a lock, and that an append never blocks.
//!
//! # Invariants
//!
//! * **T1, one writer.** Appends come from the one thread that applies
//!   writes to the memtable: the commit leader under the pipeline mutex, or
//!   recovery's replay. That is the skip list's own contract (S2 in
//!   `engine::skiplist`), and debug builds check it the same way.
//! * **T2, prefix publication.** An append writes its tombstone into slot
//!   `len` first and only then publishes `len + 1` with a release store. A
//!   reader acquires `len` and reads only the slots below it, so it sees a
//!   prefix of the appends, in append order, every one of them whole. Seeing
//!   an append before its contents is the defect T2 rules out.
//! * **T3, never moved, never removed.** A published slot is never written
//!   again and is freed only when the memtable is dropped, so a reader needs
//!   no reclamation for the log itself.
//! * **T4, the index is an optimization over a prefix.** Every
//!   [`REBUILD`] appends the writer publishes, through kovan, a sorted view
//!   of the first `covered` appends with a running maximum of their ends. A
//!   reader binary-searches that view and scans the at most `REBUILD - 1`
//!   appends past it, so a point lookup costs `O(log n)` rather than `O(n)`.
//!   A loom build has no index and scans the whole prefix, which is the
//!   protocol T2 is about.
//!
//! Why a tombstone a commit published is seen by every read after it: the
//! leader appends (T2's release on `len`) before it publishes the commit's
//! sequence through the read horizon, itself a release read-modify-write. A
//! reader whose snapshot includes the tombstone acquired a horizon at or
//! past it, so `len` covers the append for that reader. A reader under the
//! pipeline mutex is ordered by the mutex.

#![allow(unsafe_code)]

use std::cmp::Ordering as CmpOrdering;
use std::mem::{MaybeUninit, size_of};
use std::ptr;

use super::super::range_tombstone::RangeTombstone;
#[cfg(debug_assertions)]
use crate::sync::internal::{AtomicBool, SingleWriterGuard};
use crate::sync::internal::{AtomicPtr, AtomicUsize, Ordering, UnsafeCell};

/// Slots in the first segment; each later segment doubles.
const FIRST_SEGMENT: usize = 8;

/// Segments a log can have: `FIRST_SEGMENT * (2^SEGMENTS - 1)` slots, past
/// what a `u32` position (the index's element) can name.
const SEGMENTS: usize = 30;

/// Appends between two index rebuilds, and so the most appends a reader
/// scans past the index.
#[cfg(not(loom))]
pub(crate) const REBUILD: usize = 16;

/// One slot: a tombstone once the slot's position is below `len`.
type Slot = UnsafeCell<MaybeUninit<RangeTombstone>>;

/// Which segment `position` lives in, and its offset there.
#[inline]
fn locate(position: usize) -> (usize, usize) {
    let bucket = position / FIRST_SEGMENT + 1;
    let segment = (usize::BITS - 1 - bucket.leading_zeros()) as usize;
    let start = FIRST_SEGMENT * ((1usize << segment) - 1);
    (segment, position - start)
}

/// Slots in `segment`.
#[inline]
fn segment_len(segment: usize) -> usize {
    FIRST_SEGMENT << segment
}

/// The order a memtable has always reported its tombstones in: by start,
/// then end, then newest first. `clone_range_tombstones` and
/// `newer_range_tombstone` answer in it.
fn listing_order(a: &RangeTombstone, b: &RangeTombstone) -> CmpOrdering {
    a.start
        .cmp(&b.start)
        .then_with(|| a.end.cmp(&b.end))
        .then_with(|| b.seq.cmp(&a.seq))
}

/// A sorted view over the first `covered` appends. A loom build never
/// makes one (T4).
#[cfg_attr(loom, allow(dead_code))]
struct TombstoneIndex {
    /// How many appends, from the first, the view covers.
    covered: usize,
    /// Positions of those appends in [`listing_order`].
    order: Box<[u32]>,
    /// `reach[j]` is the position, among `order[..=j]`, of the tombstone
    /// with the greatest end: a walk down `order` from a key's insertion
    /// point stops once no earlier tombstone reaches the key.
    reach: Box<[u32]>,
}

/// The log. See the module docs for its invariants.
pub(crate) struct TombstoneLog {
    /// Segment `k` holds `FIRST_SEGMENT << k` slots; null until the writer
    /// first needs it. Written only by the writer, before the `len` release
    /// that publishes the first slot in it.
    segments: [AtomicPtr<Slot>; SEGMENTS],
    /// Appends published (T2).
    len: AtomicUsize,
    /// Heap bytes the published tombstones own, for the memtable's size.
    bytes: AtomicUsize,
    /// The sorted view of a prefix (T4); empty until the first rebuild.
    #[cfg(not(loom))]
    index: kovan::AtomOption<TombstoneIndex>,
    /// T1's debug detector.
    #[cfg(debug_assertions)]
    writing: AtomicBool,
}

// SAFETY: a slot is written only by the single writer (T1) before the
// release that publishes it, and read only after the acquire that observes
// that release (T2); a `RangeTombstone` is `Send + Sync`. Segment pointers
// and counters are atomics.
unsafe impl Send for TombstoneLog {}
// SAFETY: as above.
unsafe impl Sync for TombstoneLog {}

impl TombstoneLog {
    /// An empty log. Allocates nothing until the first append.
    pub(crate) fn new() -> Self {
        Self {
            segments: std::array::from_fn(|_| AtomicPtr::new(ptr::null_mut())),
            len: AtomicUsize::new(0),
            bytes: AtomicUsize::new(0),
            #[cfg(not(loom))]
            index: kovan::AtomOption::none(),
            #[cfg(debug_assertions)]
            writing: AtomicBool::new(false),
        }
    }

    /// Appends published so far, acquired: every slot below it is whole.
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.len.load(Ordering::Acquire)
    }

    /// Heap bytes the published tombstones own.
    pub(crate) fn bytes(&self) -> usize {
        self.bytes.load(Ordering::Relaxed)
    }

    /// The tombstone at `position`, which must be below a `len` this thread
    /// acquired.
    #[inline]
    fn get(&self, position: usize) -> &RangeTombstone {
        let (segment, offset) = locate(position);
        let base = self.segments[segment].load(Ordering::Acquire);
        // SAFETY: `position` is below an acquired `len`, so the writer
        // allocated this segment and wrote this slot before the release
        // this thread observed (T2), and never writes it again (T3). The
        // reference lives no longer than `self`, which owns the slot.
        unsafe { (*base.add(offset)).with(|slot| (*slot).assume_init_ref()) }
    }

    /// Append `tombstone`. Only the memtable's one writer calls this (T1).
    pub(crate) fn push(&self, tombstone: RangeTombstone) {
        #[cfg(debug_assertions)]
        let _single = SingleWriterGuard::enter(
            &self.writing,
            "range tombstones are appended by one writer at a time (T1)",
        );
        let heap = tombstone.start.len() + tombstone.end.len() + size_of::<RangeTombstone>();
        // Only this thread writes `len`, so its own last store is current.
        let position = self.len.load(Ordering::Relaxed);
        let (segment, offset) = locate(position);
        let mut base = self.segments[segment].load(Ordering::Relaxed);
        if base.is_null() {
            let slots: Box<[Slot]> = (0..segment_len(segment))
                .map(|_| UnsafeCell::new(MaybeUninit::uninit()))
                .collect();
            base = Box::into_raw(slots).cast::<Slot>();
            self.segments[segment].store(base, Ordering::Release);
        }
        // SAFETY: the slot is past every published position, so no reader
        // reaches it (T2), and this is the one writer (T1).
        unsafe {
            (*base.add(offset)).with_mut(|slot| {
                (*slot).write(tombstone);
            });
        }
        self.bytes.fetch_add(heap, Ordering::Relaxed);
        // T2: the slot is whole before the length that names it.
        self.len.store(position + 1, Ordering::Release);
        #[cfg(not(loom))]
        self.maybe_rebuild(position + 1);
    }

    /// Publish a sorted view of the first `published` appends once
    /// [`REBUILD`] appends have gathered past the current one. Writer only.
    #[cfg(not(loom))]
    fn maybe_rebuild(&self, published: usize) {
        let (covered, old_order) = match self.index.load() {
            Some(index) => (index.covered, index.order.to_vec()),
            None => (0, Vec::new()),
        };
        if published - covered < REBUILD {
            return;
        }
        // Positions past `u32::MAX` are never indexed; a log that long is
        // read by its tail scan instead, which is slower and still exact.
        let Ok(last) = u32::try_from(published) else {
            return;
        };
        let Ok(first_new) = u32::try_from(covered) else {
            return;
        };
        let by_listing =
            |a: &u32, b: &u32| listing_order(self.get(*a as usize), self.get(*b as usize));
        let mut fresh: Vec<u32> = (first_new..last).collect();
        fresh.sort_by(by_listing);
        let mut order = Vec::with_capacity(published);
        let (mut old, mut new) = (
            old_order.into_iter().peekable(),
            fresh.into_iter().peekable(),
        );
        loop {
            let take_old = match (old.peek(), new.peek()) {
                (Some(a), Some(b)) => by_listing(a, b) != CmpOrdering::Greater,
                (Some(_), None) => true,
                (None, Some(_)) => false,
                (None, None) => break,
            };
            let next = if take_old { old.next() } else { new.next() };
            order.extend(next);
        }
        let mut reach = Vec::with_capacity(order.len());
        for &position in &order {
            let farthest = match reach.last() {
                Some(&prev) if self.get(prev as usize).end >= self.get(position as usize).end => {
                    prev
                }
                _ => position,
            };
            reach.push(farthest);
        }
        self.index.store_some(TombstoneIndex {
            covered: published,
            order: order.into_boxed_slice(),
            reach: reach.into_boxed_slice(),
        });
        // The view this replaced can be as large as the log; hand it to
        // the reclaimer now rather than when this thread next fills a
        // batch.
        super::super::reclaim::submit();
    }

    /// The largest sequence of a tombstone covering `user_key` that a
    /// snapshot at `snapshot_seq` sees, or `0` when there is none.
    pub(crate) fn covering_seq(&self, user_key: &[u8], snapshot_seq: u64) -> u64 {
        let mut best = 0;
        let covered = self.scan_index(|index| {
            let mut j = index
                .order
                .partition_point(|&p| self.get(p as usize).start.as_slice() <= user_key);
            while j > 0 {
                j -= 1;
                if self.get(index.reach[j] as usize).end.as_slice() <= user_key {
                    break;
                }
                let tombstone = self.get(index.order[j] as usize);
                if tombstone.seq <= snapshot_seq && tombstone.covers(user_key) {
                    best = best.max(tombstone.seq);
                }
            }
        });
        // The index is loaded before `len`, so `len` is never below what it
        // covers and the two together read one prefix.
        for position in covered..self.len() {
            let tombstone = self.get(position);
            if tombstone.seq <= snapshot_seq && tombstone.covers(user_key) {
                best = best.max(tombstone.seq);
            }
        }
        best
    }

    /// The first tombstone in listing order with a sequence above `floor`
    /// that overlaps `[lo, hi)`.
    pub(crate) fn first_newer_overlap(
        &self,
        lo: &[u8],
        hi: &[u8],
        floor: u64,
    ) -> Option<&RangeTombstone> {
        let matches = |t: &RangeTombstone| t.seq > floor && t.overlaps(lo, hi);
        let mut found: Option<&RangeTombstone> = None;
        let covered = self.scan_index(|index| {
            found = index
                .order
                .iter()
                .map(|&p| self.get(p as usize))
                .find(|t| matches(t));
        });
        for position in covered..self.len() {
            let tombstone = self.get(position);
            if matches(tombstone)
                && found.is_none_or(|best| listing_order(tombstone, best) == CmpOrdering::Less)
            {
                found = Some(tombstone);
            }
        }
        found
    }

    /// Whether any published tombstone satisfies `pred`.
    pub(crate) fn any(&self, mut pred: impl FnMut(&RangeTombstone) -> bool) -> bool {
        (0..self.len()).any(|position| pred(self.get(position)))
    }

    /// Every published tombstone, sorted and deduplicated as the memtable
    /// has always listed them.
    ///
    /// The index is already in listing order, so only the tail past it is
    /// sorted and merged in: `O(n + t log t)` for `t < REBUILD`, not a sort
    /// of the whole log on every iterator built over the memtable.
    pub(crate) fn to_sorted_vec(&self) -> Vec<RangeTombstone> {
        let mut indexed: Vec<RangeTombstone> = Vec::new();
        let covered = self.scan_index(|index| {
            indexed = index
                .order
                .iter()
                .map(|&position| self.get(position as usize).clone())
                .collect();
        });
        let mut tail: Vec<RangeTombstone> = (covered..self.len())
            .map(|position| self.get(position).clone())
            .collect();
        tail.sort_by(listing_order);
        let mut merged = Vec::with_capacity(indexed.len() + tail.len());
        let (mut left, mut right) = (indexed.into_iter().peekable(), tail.into_iter().peekable());
        loop {
            let take_left = match (left.peek(), right.peek()) {
                (Some(a), Some(b)) => listing_order(a, b) != CmpOrdering::Greater,
                (Some(_), None) => true,
                (None, Some(_)) => false,
                (None, None) => break,
            };
            merged.extend(if take_left { left.next() } else { right.next() });
        }
        merged.dedup_by(|a, b| a.start == b.start && a.end == b.end && a.seq == b.seq);
        merged
    }

    /// Run `walk` over the index when there is one; returns how many
    /// appends it covers, from which the caller's tail scan starts.
    #[cfg(not(loom))]
    fn scan_index(&self, walk: impl FnOnce(&TombstoneIndex)) -> usize {
        match self.index.load() {
            Some(index) => {
                walk(&index);
                index.covered
            }
            None => 0,
        }
    }

    /// Without an index the whole prefix is the tail.
    #[cfg(loom)]
    fn scan_index(&self, _walk: impl FnOnce(&TombstoneIndex)) -> usize {
        0
    }
}

impl Drop for TombstoneLog {
    fn drop(&mut self) {
        // `&mut self`: no other thread can touch the log, so relaxed loads
        // read the final values.
        let len = self.len.load(Ordering::Relaxed);
        for position in 0..len {
            let (segment, offset) = locate(position);
            let base = self.segments[segment].load(Ordering::Relaxed);
            // SAFETY: `&mut self` excludes every reader, and each position
            // below `len` was written exactly once (T2, T3).
            unsafe { (*base.add(offset)).with_mut(|slot| (*slot).assume_init_drop()) };
        }
        for (segment, base) in self.segments.iter().enumerate() {
            let base = base.load(Ordering::Relaxed);
            if !base.is_null() {
                // SAFETY: allocated in `push` as a boxed slice of exactly
                // this many slots, and freed once, here.
                drop(unsafe {
                    Box::from_raw(ptr::slice_from_raw_parts_mut(base, segment_len(segment)))
                });
            }
        }
    }
}

#[cfg(all(test, not(loom)))]
#[path = "tombstones_tests.rs"]
mod tests;
