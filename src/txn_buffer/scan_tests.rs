use super::TxnBuffer;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

struct CountedValue {
    value: Option<usize>,
    copies: Arc<AtomicUsize>,
}

impl Clone for CountedValue {
    fn clone(&self) -> Self {
        self.copies.fetch_add(1, Ordering::Relaxed);
        Self {
            value: self.value,
            copies: self.copies.clone(),
        }
    }
}

#[test]
fn narrow_snapshot_copies_only_matching_latest_values() {
    for spill_at in [0, 16] {
        let copies = Arc::new(AtomicUsize::new(0));
        let buffer = TxnBuffer::new(spill_at);
        for key in 0..12_000 {
            buffer.insert(
                key,
                CountedValue {
                    value: Some(key),
                    copies: copies.clone(),
                },
            );
        }
        buffer.insert(
            5,
            CountedValue {
                value: Some(99),
                copies: copies.clone(),
            },
        );
        buffer.insert(
            6,
            CountedValue {
                value: None,
                copies: copies.clone(),
            },
        );
        copies.store(0, Ordering::Relaxed);
        let mut range = buffer.chains_matching(|key| (5..7).contains(key), |_| true);
        range.sort_by_key(|(key, _)| *key);
        assert_eq!(range.len(), 2);
        assert_eq!(range[0].1.value, Some(99));
        assert_eq!(range[1].1.value, None);
        assert_eq!(copies.load(Ordering::Relaxed), 2);
        assert!(
            buffer
                .chains_matching(|key| *key >= 12_000, |_| true)
                .is_empty()
        );
        assert_eq!(copies.load(Ordering::Relaxed), 2);
        assert_eq!(buffer.chains_matching(|_| true, |_| true).len(), 12_000);
    }
}

#[test]
fn a_chain_runs_newest_first_through_the_last_replacement() {
    for spill_at in [0, 2] {
        let buffer = TxnBuffer::new(spill_at);
        // A negative value replaces its key outright; any other is an operand.
        for (key, value) in [
            (1, -1),
            (1, 10),
            (2, 20),
            (1, -2),
            (1, 30),
            (2, 40),
            (1, 50),
        ] {
            buffer.insert(key, value);
        }
        let replaces = |value: &i32| *value < 0;

        assert_eq!(buffer.chain(&1, replaces), [50, 30, -2]);
        assert_eq!(buffer.chain(&2, replaces), [40, 20]);
        assert!(buffer.chain(&3, replaces).is_empty());

        let mut all = buffer.chains_matching(|_| true, replaces);
        // Stable, so a key keeps its newest-first order.
        all.sort_by_key(|(key, _)| *key);
        assert_eq!(all, [(1, 50), (1, 30), (1, -2), (2, 40), (2, 20)]);
        assert_eq!(
            buffer.chains_matching(|key| *key == 2, replaces),
            [(2, 40), (2, 20)]
        );
    }
}
