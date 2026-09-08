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
        let mut range = buffer.snapshot_matching(|key| (5..7).contains(key));
        range.sort_by_key(|(key, _)| *key);
        assert_eq!(range.len(), 2);
        assert_eq!(range[0].1.value, Some(99));
        assert_eq!(range[1].1.value, None);
        assert_eq!(copies.load(Ordering::Relaxed), 2);
        assert!(buffer.snapshot_matching(|key| *key >= 12_000).is_empty());
        assert_eq!(copies.load(Ordering::Relaxed), 2);
        assert_eq!(buffer.snapshot().len(), 12_000);
    }
}
