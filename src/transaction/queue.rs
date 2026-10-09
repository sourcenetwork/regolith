//! The queue a transaction keeps its callbacks in.

use std::collections::VecDeque;

/// Entries a [`Queue`] holds in place before it allocates.
const INLINE: usize = 4;

/// A first-in first-out queue whose first `INLINE` entries live in the struct,
/// so a transaction with a few callbacks allocates nothing for the queue
/// itself.
///
/// `pushed` counts every entry ever pushed and not rewound, so it doubles as a
/// mark: [`Queue::truncate`] to an earlier value takes back what was pushed
/// since, and never an entry already popped.
pub(super) struct Queue<T> {
    slots: [Option<T>; INLINE],
    spill: VecDeque<T>,
    pushed: usize,
    popped: usize,
}

impl<T> Default for Queue<T> {
    fn default() -> Self {
        Self {
            slots: [const { None }; INLINE],
            spill: VecDeque::new(),
            pushed: 0,
            popped: 0,
        }
    }
}

impl<T> Queue<T> {
    pub(super) fn push(&mut self, entry: T) {
        match self.slots.get_mut(self.pushed) {
            Some(slot) => *slot = Some(entry),
            None => self.spill.push_back(entry),
        }
        self.pushed += 1;
    }

    pub(super) fn pop(&mut self) -> Option<T> {
        if self.popped == self.pushed {
            return None;
        }
        let entry = match self.slots.get_mut(self.popped) {
            Some(slot) => slot.take(),
            None => self.spill.pop_front(),
        };
        self.popped += 1;
        entry
    }

    /// The mark to hand [`Queue::truncate`].
    pub(super) fn mark(&self) -> usize {
        self.pushed
    }

    /// Take back the entries pushed after `mark` was read.
    pub(super) fn truncate(&mut self, mark: usize) {
        while self.pushed > mark.max(self.popped) {
            self.pushed -= 1;
            match self.slots.get_mut(self.pushed) {
                Some(slot) => *slot = None,
                None => drop(self.spill.pop_back()),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn entries_come_out_in_the_order_they_went_in_across_the_inline_edge() {
        let mut queue = Queue::default();
        for i in 0..(INLINE * 3) {
            queue.push(i);
        }
        let out: Vec<usize> = std::iter::from_fn(|| queue.pop()).collect();
        assert_eq!(out, (0..INLINE * 3).collect::<Vec<_>>());
    }

    #[test]
    fn the_first_entries_do_not_touch_the_heap() {
        let mut queue = Queue::default();
        for i in 0..INLINE {
            queue.push(i);
        }
        assert_eq!(queue.spill.capacity(), 0);
        queue.push(INLINE);
        assert!(queue.spill.capacity() > 0);
    }

    #[test]
    fn truncate_takes_back_only_what_was_pushed_after_the_mark() {
        let mut queue = Queue::default();
        queue.push(1);
        let mark = queue.mark();
        for i in 2..=8 {
            queue.push(i);
        }
        queue.truncate(mark);
        assert_eq!(queue.pop(), Some(1));
        assert_eq!(queue.pop(), None);
        queue.push(9);
        assert_eq!(queue.pop(), Some(9));
    }

    #[test]
    fn truncate_never_takes_back_a_popped_entry() {
        let mut queue = Queue::default();
        queue.push(1);
        let mark = queue.mark();
        queue.push(2);
        assert_eq!(queue.pop(), Some(1));
        assert_eq!(queue.pop(), Some(2));
        queue.truncate(mark);
        assert_eq!(queue.pop(), None);
        queue.push(3);
        assert_eq!(queue.pop(), Some(3));
    }

    #[derive(Debug, Clone)]
    enum Op {
        Push(u32),
        Pop,
        Truncate(usize),
    }

    proptest! {
        /// The queue agrees with a plain list and a cursor, whatever the mix
        /// of pushes, pops and rewinds.
        #[test]
        fn the_queue_matches_a_list_and_a_cursor(
            ops in prop::collection::vec(
                prop_oneof![
                    5 => any::<u32>().prop_map(Op::Push),
                    4 => Just(Op::Pop),
                    2 => (0usize..20).prop_map(Op::Truncate),
                ],
                0..120,
            )
        ) {
            let mut queue = Queue::default();
            let mut all: Vec<u32> = Vec::new();
            let mut popped = 0;
            for op in ops {
                match op {
                    Op::Push(x) => {
                        queue.push(x);
                        all.push(x);
                    }
                    Op::Pop => {
                        let expected = all.get(popped).copied();
                        popped += usize::from(expected.is_some());
                        prop_assert_eq!(queue.pop(), expected);
                    }
                    Op::Truncate(mark) => {
                        queue.truncate(mark);
                        all.truncate(mark.max(popped));
                    }
                }
                prop_assert_eq!(queue.mark(), all.len());
            }
        }
    }
}
