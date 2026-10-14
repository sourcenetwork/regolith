//! What landed for one queue, as its owner keeps it, and when it lets each
//! landing go.
//!
//! A read run again after a wait finds its block in the block cache or in
//! what landed for its queue (`QueueShared::landed`). That table is bounded
//! by the queue's bytes: past the bound the oldest landings go. A call that
//! needs several blocks at once (a `multi_get`, a collecting scan, a read
//! merging operands from several tables) starts over each time it is run,
//! so evicting the blocks it found on its earlier runs could keep it from
//! ever finishing: two blocks that each take most of the bound would evict
//! each other on every run.
//!
//! So a landing a call still needs is held, and only the others count
//! against the bound:
//!
//! - a wait carries the landed blocks its call read before it
//!   ([`WaitSlot::holds`]): they are held while the wait is pending;
//! - once the wait completes it is *kept*: its holds, and the block it waited
//!   for, stay held until the call is seen again: a later wait whose holds
//!   cover them (the call was run again and waits for one more block), or a
//!   call that read all of them and finished ([`Message::Finished`]);
//! - a kept wait whose call is never run again is let go after
//!   [`KEEP_ROUNDS`] polls that land something, so a call abandoned after a
//!   wait holds nothing for long.
//!
//! The landings no call holds go oldest first, at the end of a poll, until
//! the rest fit the bound. A call run again within [`KEEP_ROUNDS`] landing
//! polls of each wait's completion therefore finds every block it found
//! before and the one it waited for, and finishes in one run more than the
//! blocks it misses. What stays past the bound is what calls in progress
//! need, which the reads they were asked for need anyway.
//! `proofs/tla/LandingHold.tla` checks that such a call finishes, and that
//! the eviction this replaces (oldest first, holding nothing) never lets it.
//!
//! [`WaitSlot::holds`]: crate::engine::io::shared::WaitSlot::holds
//! [`Message::Finished`]: crate::engine::io::shared::Message::Finished

use std::collections::{HashMap, VecDeque};
use std::sync::Arc;

use crate::engine::io::shared::{QueueShared, WaitSlot};
use crate::engine::io::unit::UnitKey;

/// Landing polls a completed wait is kept for when its call is not seen
/// again: the slack a caller has to run a call again after its wait
/// completes.
pub(super) const KEEP_ROUNDS: u64 = 4;

/// The owner's account of what landed for its queue. Only the owner touches
/// it, at its polls.
#[derive(Default)]
pub(super) struct Ledger {
    /// Each landing, oldest first, with what it costs. A block landed twice
    /// is here twice; the table keeps the newer.
    order: VecDeque<(UnitKey, usize)>,
    /// What `order` costs.
    bytes: usize,
    /// How many pending or kept waits hold each block. A block held by none
    /// has no entry.
    held: HashMap<UnitKey, u32>,
    /// Completed waits whose call has not been seen again, oldest first.
    kept: VecDeque<Kept>,
    /// Polls that landed something: what a kept wait is aged by.
    round: u64,
    /// Something landed since the last [`Ledger::settle`].
    landed: bool,
}

/// A completed wait, kept for its call's next run.
struct Kept {
    /// The block it waited for; `None` for a wait for room.
    awaited: Option<UnitKey>,
    /// The wait itself, which carries what its call read before it.
    slot: Arc<WaitSlot>,
    /// The landing poll it completed in.
    round: u64,
}

impl Ledger {
    /// `key` landed, costing `charge` bytes.
    pub(super) fn land(&mut self, key: UnitKey, charge: usize) {
        self.order.push_back((key, charge));
        self.bytes = self.bytes.saturating_add(charge);
        self.landed = true;
    }

    /// A wait recorded on the queue: hold what its call read.
    pub(super) fn hold(&mut self, slot: &WaitSlot) {
        for key in slot.holds() {
            self.pin(*key);
        }
    }

    /// A wait held by [`Ledger::hold`] completed, for the block `awaited`
    /// (`None` for room): keep it, and what it holds, for its call's next
    /// run. A wait that holds nothing and waited for no block keeps nothing.
    pub(super) fn completed(&mut self, awaited: Option<UnitKey>, slot: Arc<WaitSlot>) {
        if awaited.is_none() && slot.holds().is_empty() {
            return;
        }
        if let Some(key) = awaited {
            self.pin(key);
        }
        self.kept.push_back(Kept {
            awaited,
            slot,
            round: self.round,
        });
    }

    /// A call read `read` (sorted): every kept wait it covers, the block
    /// waited for and everything it holds, was that call's earlier run, and
    /// is let go. The call holds what it needs again by its own wait, or
    /// finished.
    pub(super) fn seen(&mut self, read: &[UnitKey]) {
        if read.is_empty() || self.kept.is_empty() {
            return;
        }
        let covered = |kept: &Kept| {
            kept.awaited
                .is_none_or(|key| read.binary_search(&key).is_ok())
                && kept
                    .slot
                    .holds()
                    .iter()
                    .all(|key| read.binary_search(key).is_ok())
        };
        let mut i = 0;
        while i < self.kept.len() {
            if covered(&self.kept[i]) {
                if let Some(kept) = self.kept.remove(i) {
                    self.release(&kept);
                }
            } else {
                i += 1;
            }
        }
    }

    /// The end of a poll: when something landed, a round passed, and a kept
    /// wait past [`KEEP_ROUNDS`] of them is let go; then the landings no
    /// wait holds go, oldest first, until the rest fit `queue`'s bound.
    pub(super) fn settle(&mut self, queue: &QueueShared) {
        if !std::mem::take(&mut self.landed) {
            return;
        }
        self.round += 1;
        while self
            .kept
            .front()
            .is_some_and(|kept| self.round - kept.round > KEEP_ROUNDS)
        {
            if let Some(kept) = self.kept.pop_front() {
                self.release(&kept);
            }
        }
        let mut i = 0;
        while self.bytes > queue.bound() && i < self.order.len() {
            let (key, charge) = self.order[i];
            if self.held.contains_key(&key) {
                i += 1;
                continue;
            }
            self.order.remove(i);
            self.bytes -= charge;
            if !self.order.iter().any(|(other, _)| *other == key) {
                queue.forget(&key);
            }
        }
    }

    /// Let go of every landing: the queue is being dropped.
    pub(super) fn clear(&mut self, queue: &QueueShared) {
        for (key, _) in self.order.drain(..) {
            queue.forget(&key);
        }
        self.bytes = 0;
        self.held.clear();
        self.kept.clear();
    }

    fn pin(&mut self, key: UnitKey) {
        *self.held.entry(key).or_insert(0) += 1;
    }

    fn unpin(&mut self, key: UnitKey) {
        if let Some(count) = self.held.get_mut(&key) {
            *count -= 1;
            if *count == 0 {
                self.held.remove(&key);
            }
        }
    }

    fn release(&mut self, kept: &Kept) {
        if let Some(key) = kept.awaited {
            self.unpin(key);
        }
        for key in kept.slot.holds() {
            self.unpin(*key);
        }
    }

    /// How many completed waits are kept.
    pub(super) fn kept(&self) -> usize {
        self.kept.len()
    }

    /// Bytes of what landed and is still kept.
    #[cfg(test)]
    pub(super) fn bytes(&self) -> usize {
        self.bytes
    }

    /// Whether `key` is held by a pending or kept wait.
    #[cfg(test)]
    pub(super) fn is_held(&self, key: &UnitKey) -> bool {
        self.held.contains_key(key)
    }

    /// The blocks still landed, oldest first.
    #[cfg(test)]
    pub(super) fn keys(&self) -> Vec<UnitKey> {
        self.order.iter().map(|(key, _)| *key).collect()
    }
}

#[cfg(all(test, not(loom)))]
#[path = "ledger_tests.rs"]
mod tests;
