//! The slots the open transactions' claims sit in, for `close` to find.
//!
//! A transaction takes a slot when it begins and gives it back when it ends,
//! each with one compare-and-swap on a stack of free slots, so listing a
//! transaction costs no allocation and no lookup. The table grows to the most
//! claims ever listed at once and never shrinks: a slot given back is the
//! next one taken.
//!
//! A slot holds one reference to its claim, and whoever swaps it out owns
//! it: the transaction when it ends, or `close` when it gets there first.
//! Exactly one of them drops it, so nothing is ever read through a reference
//! another thread may have dropped, and no reclamation scheme is needed.
//! Only the transaction that took a slot gives it back, after it emptied it.

use std::sync::{Arc, OnceLock};

use crate::portability::{AtomicPtr, AtomicU32, AtomicU64, AtomicUsize, Ordering};

/// Slots in the first chunk; chunk `k` holds `FIRST << k`.
const FIRST: usize = 64;

/// As many chunks as keep every slot, plus one, inside the `u32` the free
/// stack links slots by.
const CHUNKS: usize = 26;

/// Every slot the chunks hold.
const CAPACITY: usize = FIRST * ((1 << CHUNKS) - 1);

/// The low half of the free stack's word: the top slot plus one, `0` when the
/// stack is empty.
const TOP: u64 = u32::MAX as u64;

struct Chunk<T> {
    claims: Box<[AtomicPtr<T>]>,
    /// For a free slot, the slot below it on the free stack, plus one.
    below: Box<[AtomicU32]>,
}

impl<T> Chunk<T> {
    fn new(len: usize) -> Self {
        Self {
            claims: (0..len)
                .map(|_| AtomicPtr::new(std::ptr::null_mut()))
                .collect(),
            below: (0..len).map(|_| AtomicU32::new(0)).collect(),
        }
    }
}

/// The table of listed claims; `T` is the claim.
pub(super) struct ClaimSlots<T> {
    chunks: [OnceLock<Chunk<T>>; CHUNKS],
    /// The free stack: the top slot plus one in the low half, and in the high
    /// half a count of the changes made to it, so a compare-and-swap that
    /// read a top since popped and pushed back fails (ABA).
    free: AtomicU64,
    /// Slots ever handed out. Every one below this was handed out once.
    taken: AtomicUsize,
}

/// The chunk `slot` is in, and where in it.
fn place(slot: usize) -> (usize, usize) {
    let run = slot / FIRST + 1;
    let chunk = run.ilog2() as usize;
    (chunk, slot - FIRST * ((1 << chunk) - 1))
}

impl<T> ClaimSlots<T> {
    pub(super) fn new() -> Self {
        Self {
            chunks: std::array::from_fn(|_| OnceLock::new()),
            free: AtomicU64::new(0),
            taken: AtomicUsize::new(0),
        }
    }

    /// The chunk and offset of a slot that was handed out.
    fn chunk(&self, slot: usize) -> (&Chunk<T>, usize) {
        let (chunk, at) = place(slot);
        let chunk = self.chunks[chunk].get_or_init(|| Chunk::new(FIRST << chunk));
        (chunk, at)
    }

    /// A slot of the caller's own, which only [`ClaimSlots::remove`] gives
    /// back. `None` once every slot is taken, more claims at once than memory
    /// can hold: that claim is not listed, and its owner ends it.
    pub(super) fn reserve(&self) -> Option<u32> {
        u32::try_from(self.take()?).ok()
    }

    /// Lists `claim` in `slot`, which the caller reserved.
    pub(super) fn fill(&self, slot: u32, claim: &Arc<T>) {
        let (chunk, at) = self.chunk(slot as usize);
        chunk.claims[at].store(
            Arc::into_raw(Arc::clone(claim)).cast_mut(),
            Ordering::Release,
        );
    }

    /// Ends the listing in `slot`: drops its reference unless `close` took it
    /// first, and gives the slot back.
    pub(super) fn remove(&self, slot: u32) {
        let slot = slot as usize;
        let (chunk, at) = self.chunk(slot);
        drop(take_claim(&chunk.claims[at]));
        let mut head = self.free.load(Ordering::Relaxed);
        loop {
            chunk.below[at].store((head & TOP) as u32, Ordering::Relaxed);
            let next = (head & !TOP).wrapping_add(TOP + 1) | (slot as u64 + 1);
            match self
                .free
                .compare_exchange_weak(head, next, Ordering::Release, Ordering::Relaxed)
            {
                Ok(_) => return,
                Err(current) => head = current,
            }
        }
    }

    /// Takes every claim still listed, emptying its slot; `visit` sees each
    /// once. A slot handed out while this runs may be missed.
    pub(super) fn drain(&self, mut visit: impl FnMut(Arc<T>)) {
        for slot in 0..self.taken.load(Ordering::Acquire).min(CAPACITY) {
            let (chunk, at) = place(slot);
            if let Some(chunk) = self.chunks[chunk].get()
                && let Some(claim) = take_claim(&chunk.claims[at])
            {
                visit(claim);
            }
        }
    }

    /// A free slot: the top of the free stack, or else a new one while any
    /// is left.
    fn take(&self) -> Option<usize> {
        let mut head = self.free.load(Ordering::Acquire);
        while head & TOP != 0 {
            let slot = (head & TOP) as usize - 1;
            let (chunk, at) = place(slot);
            // Every slot on the stack was handed out, so its chunk exists.
            let below = self.chunks[chunk]
                .get()
                .map_or(0, |chunk| chunk.below[at].load(Ordering::Relaxed));
            let next = (head & !TOP).wrapping_add(TOP + 1) | u64::from(below);
            match self
                .free
                .compare_exchange_weak(head, next, Ordering::Acquire, Ordering::Acquire)
            {
                Ok(_) => return Some(slot),
                Err(current) => head = current,
            }
        }
        let slot = self.taken.fetch_add(1, Ordering::AcqRel);
        (slot < CAPACITY).then_some(slot)
    }
}

impl<T> Drop for ClaimSlots<T> {
    fn drop(&mut self) {
        self.drain(drop);
    }
}

/// Swaps the claim out of `cell`, taking the reference it held.
#[allow(unsafe_code)]
fn take_claim<T>(cell: &AtomicPtr<T>) -> Option<Arc<T>> {
    let claim = cell.swap(std::ptr::null_mut(), Ordering::AcqRel);
    // SAFETY: a non-null pointer in a slot came from `Arc::into_raw` in
    // `fill` and stands for one strong reference. The swap hands that
    // reference to this caller alone: any other swap of the cell reads null
    // until `fill` stores a new reference.
    (!claim.is_null()).then(|| unsafe { Arc::from_raw(claim) })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A slot given back is the next one taken, so the table stays as large
    /// as the most claims listed at once.
    #[test]
    fn a_slot_given_back_is_taken_again() {
        let slots = ClaimSlots::new();
        let claim = Arc::new(7u64);
        let first: Vec<u32> = (0..3).map(|_| slots.reserve().unwrap()).collect();
        assert_eq!(first, vec![0, 1, 2]);
        for &slot in &first {
            slots.fill(slot, &claim);
        }
        assert_eq!(Arc::strong_count(&claim), 4);
        slots.remove(1);
        slots.remove(0);
        assert_eq!(Arc::strong_count(&claim), 2);
        assert_eq!(slots.reserve(), Some(0));
        assert_eq!(slots.reserve(), Some(1));
        assert_eq!(slots.reserve(), Some(3));
    }

    /// `drain` takes each listed claim once, and an owner ending after it
    /// finds its slot empty and gives the slot back: every reference is
    /// dropped exactly once.
    #[test]
    fn a_drained_claim_is_dropped_once_and_its_slot_comes_back() {
        let slots = ClaimSlots::new();
        let claims: Vec<Arc<u64>> = (0..200).map(Arc::new).collect();
        let listed: Vec<u32> = claims
            .iter()
            .map(|claim| {
                let slot = slots.reserve().unwrap();
                slots.fill(slot, claim);
                slot
            })
            .collect();
        let mut seen = Vec::new();
        slots.drain(|claim| seen.push(*claim));
        seen.sort_unstable();
        assert_eq!(seen, (0..200).collect::<Vec<u64>>());
        assert!(claims.iter().all(|claim| Arc::strong_count(claim) == 1));
        for slot in listed {
            slots.remove(slot);
        }
        slots.drain(|_| panic!("nothing is listed"));
        assert!(slots.reserve().unwrap() < 200);
    }

    /// Owners list and end claims on several threads while another drains:
    /// each reference is dropped once, by its owner or by the drain, and no
    /// slot is ever held by two owners.
    #[cfg(not(target_arch = "wasm32"))]
    #[test]
    fn concurrent_owners_and_drains_drop_every_reference_once() {
        use std::sync::atomic::AtomicBool;

        let slots = Arc::new(ClaimSlots::new());
        let held: Arc<Vec<AtomicBool>> =
            Arc::new((0..1024).map(|_| AtomicBool::new(false)).collect());
        let stop = Arc::new(AtomicBool::new(false));
        let owners: Vec<_> = (0..4)
            .map(|_| {
                let (slots, held) = (Arc::clone(&slots), Arc::clone(&held));
                std::thread::spawn(move || {
                    let claim = Arc::new(());
                    for _ in 0..20_000 {
                        let slot = slots.reserve().unwrap();
                        assert!(
                            !held[slot as usize].swap(true, Ordering::AcqRel),
                            "slot {slot} held twice"
                        );
                        slots.fill(slot, &claim);
                        held[slot as usize].store(false, Ordering::Release);
                        slots.remove(slot);
                    }
                    claim
                })
            })
            .collect();
        let drainer = {
            let (slots, stop) = (Arc::clone(&slots), Arc::clone(&stop));
            std::thread::spawn(move || {
                while !stop.load(Ordering::Acquire) {
                    slots.drain(drop);
                }
            })
        };
        let claims: Vec<Arc<()>> = owners
            .into_iter()
            .map(|owner| owner.join().unwrap())
            .collect();
        stop.store(true, Ordering::Release);
        drainer.join().unwrap();
        assert!(claims.iter().all(|claim| Arc::strong_count(claim) == 1));
    }

    #[test]
    fn a_slot_is_placed_in_the_chunk_that_holds_it() {
        assert_eq!(place(0), (0, 0));
        assert_eq!(place(63), (0, 63));
        assert_eq!(place(64), (1, 0));
        assert_eq!(place(191), (1, 127));
        assert_eq!(place(192), (2, 0));
        let last = CAPACITY - 1;
        assert_eq!(place(last), (CHUNKS - 1, (FIRST << (CHUNKS - 1)) - 1));
        assert!(u32::try_from(last + 1).is_ok());
    }
}
