//! Projected reads: [`Transaction::get_parts`] and what the transaction
//! remembers about a key it read by parts.
//!
//! A key read only through `get_parts` is recorded with the parts it was read
//! by, one set per key. The set only widens: a later `get_parts` adds its
//! parts, and a `get`, `get_for_update` or scan yield of the key widens it to
//! the whole value. At commit the set becomes the read's rule (see
//! `Transaction::validation_set`).
//!
//! Only an optimistic transaction at DefraLevel projects. Anywhere else
//! `get_parts` is a plain read and is validated as the level validates any
//! read.

use crate::sync::internal::Mutex;

use super::{
    Arc, AtomicBool, DEFAULT_CF_ID, DbSlice, IsolationLevel, KeyState, Ordering, Transaction,
    TxMode, TxResult, prefix_key, read_error,
};

/// The part ids that fit beside the cell without a second allocation; a read
/// by more parts than this moves them to the heap.
const INLINE: usize = 8;

/// A sorted set of part ids.
enum PartSet {
    Inline { len: u8, ids: [u32; INLINE] },
    Heap(Vec<u32>),
}

impl PartSet {
    fn as_slice(&self) -> &[u32] {
        match self {
            Self::Inline { len, ids } => &ids[..usize::from(*len)],
            Self::Heap(ids) => ids,
        }
    }

    fn insert(&mut self, part: u32) {
        let Err(at) = self.as_slice().binary_search(&part) else {
            return;
        };
        match self {
            Self::Inline { len, ids } if usize::from(*len) < INLINE => {
                let n = usize::from(*len);
                ids.copy_within(at..n, at + 1);
                ids[at] = part;
                *len += 1;
            }
            Self::Inline { .. } => {
                let mut heap = self.as_slice().to_vec();
                heap.insert(at, part);
                *self = Self::Heap(heap);
            }
            Self::Heap(ids) => ids.insert(at, part),
        }
    }
}

/// The parts one key was read by.
pub(super) struct Projection {
    /// A read of the whole value has happened, which no set of parts
    /// narrows again.
    full: AtomicBool,
    /// The parts read. Meaningless once `full`.
    //
    // vertexia: a mutex, taken only by `get_parts` and the commit, on a set a
    // handful of ids long; a lock-free append list if one projected key is
    // ever read from many threads at once.
    parts: Mutex<PartSet>,
}

impl Projection {
    pub(super) fn new(parts: &[u32]) -> Self {
        let projection = Self {
            full: AtomicBool::new(false),
            parts: Mutex::new(PartSet::Inline {
                len: 0,
                ids: [0; INLINE],
            }),
        };
        projection.widen(parts);
        projection
    }

    /// Add `parts` to the set.
    pub(super) fn widen(&self, parts: &[u32]) {
        let mut held = self.parts.lock();
        parts.iter().for_each(|part| held.insert(*part));
    }

    /// The key was read in whole.
    pub(super) fn widen_to_full(&self) {
        self.full.store(true, Ordering::Release);
    }

    /// Run `f` on the sorted parts, or on `None` when the key was read in
    /// whole.
    pub(super) fn with_parts<R>(&self, f: impl FnOnce(Option<&[u32]>) -> R) -> R {
        if self.full.load(Ordering::Acquire) {
            f(None)
        } else {
            f(Some(self.parts.lock().as_slice()))
        }
    }
}

impl KeyState {
    /// A cell for a key first read by `parts`.
    pub(super) fn projected(horizon: u64, parts: &[u32]) -> Self {
        Self {
            projection: Some(Box::new(Projection::new(parts))),
            ..Self::new(horizon, false)
        }
    }
}

impl Transaction {
    /// Read `key` like [`Transaction::get_slice`], and record that the
    /// decision rests only on `parts`: sorted part ids that the database's
    /// [`crate::MergeOperator::touches`] understands. The whole value comes
    /// back, with no extra read.
    ///
    /// At [`IsolationLevel::DefraLevel`], for an optimistic transaction, the
    /// commit validates the read against newer writes that change one of
    /// `parts` and no others: a newer put, delete or covering range delete
    /// changes them unless it leaves exactly the bytes read, and a merge
    /// operand does when `touches` says it touches one of them. Two
    /// fallbacks widen the check to the whole value, because a decision on
    /// parts always includes the key's existence and a put replaces every
    /// part: the read found nothing, or this transaction puts or deletes the
    /// key. With no `parts` the read is never validated. Each key carries one
    /// set of parts, which only widens: reading it again by other parts adds
    /// them, and [`Transaction::get`], [`Transaction::get_for_update`] and a
    /// scan that yields the key widen it to the whole value. A conflict names
    /// [`crate::Access::ReadParts`].
    ///
    /// At any other level, and for a pessimistic transaction, this is
    /// [`Transaction::get_slice`] and is validated as that level validates a
    /// read.
    ///
    /// The caller must name every part its decision used. A decision that
    /// also depends on a part it left out can commit on a value that changed
    /// under it, and regolith cannot see that. A key that does not hold
    /// the parts scheme the operator's `touches` understands should not be
    /// read this way.
    ///
    /// # Example
    ///
    /// `Fields` is the operator of the [`crate::MergeOperator::touches`]
    /// example: a value is a stock level and a price, one byte each, and an
    /// operand adds to one of them.
    ///
    /// ```
    /// use std::sync::Arc;
    ///
    /// use regolith::{
    ///     IsolationLevel, OptimisticTransactionDb, Options, TransactionError, TxnOptions,
    /// };
    /// # use regolith::MergeOperator;
    /// # const STOCK: u8 = 0;
    /// # const PRICE: u8 = 1;
    /// # struct Fields;
    /// # impl MergeOperator for Fields {
    /// #     fn name(&self) -> &'static str {
    /// #         "fields"
    /// #     }
    /// #     fn full_merge(&self, _key: &[u8], base: Option<&[u8]>, operands: &[&[u8]]) -> Option<Vec<u8>> {
    /// #         let mut fields: [u8; 2] = base.map_or(Some([0; 2]), |base| base.try_into().ok())?;
    /// #         for &operand in operands {
    /// #             let &[part, delta] = operand else { return None };
    /// #             let field = fields.get_mut(usize::from(part))?;
    /// #             *field = field.wrapping_add(delta);
    /// #         }
    /// #         Some(fields.to_vec())
    /// #     }
    /// #     fn touches(&self, _key: &[u8], operand: &[u8], parts: &[u32]) -> bool {
    /// #         operand.first().is_none_or(|part| parts.contains(&u32::from(*part)))
    /// #     }
    /// # }
    ///
    /// let options = Options::memory().merge_operator(Some(Arc::new(Fields)));
    /// let db = OptimisticTransactionDb::open("items", options)?
    ///     .with_isolation(IsolationLevel::DefraLevel);
    /// db.db().put(b"item", &[10, 50])?;
    /// let price = [u32::from(PRICE)];
    ///
    /// // The whole value comes back, and the decision rests on the price:
    /// // stock that arrives before the commit is no conflict.
    /// let txn = db.begin(&TxnOptions::new());
    /// let item = txn.get_parts(b"item", &price)?.expect("the item exists");
    /// assert_eq!(item, [10, 50]);
    /// db.db().merge(b"item", &[STOCK, 5])?;
    /// txn.put(b"quote", &item[1..])?;
    /// txn.commit()?;
    ///
    /// // A read that found nothing decided on the key's absence, which any
    /// // write of the key ends.
    /// let txn = db.begin(&TxnOptions::new());
    /// assert!(txn.get_parts(b"new-item", &price)?.is_none());
    /// db.db().merge(b"new-item", &[STOCK, 1])?;
    /// txn.put(b"quote", b"none")?;
    /// assert!(matches!(txn.commit(), Err(TransactionError::Conflict(_))));
    ///
    /// // Naming no parts reads the value and validates nothing.
    /// let txn = db.begin(&TxnOptions::new());
    /// txn.get_parts(b"item", &[])?;
    /// db.db().merge(b"item", &[PRICE, 5])?;
    /// txn.put(b"note", b"seen")?;
    /// txn.commit()?;
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn get_parts(&self, key: &[u8], parts: &[u32]) -> TxResult<Option<DbSlice>> {
        let _scope = self.read_scope();
        if !self.projects() {
            return self.get_slice(key);
        }
        let prefixed = prefix_key(DEFAULT_CF_ID, key);
        let committed = || self.read_projected(&prefixed, parts);
        match self.read_own(&prefixed, committed)? {
            Some(own) => Ok(own.map(DbSlice::from)),
            None => committed().map_err(|e| read_error(e, &prefixed)),
        }
    }

    /// Whether this transaction records a read by its parts.
    pub(super) fn projects(&self) -> bool {
        matches!(self.mode, TxMode::Optimistic) && self.isolation == IsolationLevel::DefraLevel
    }

    /// What the database holds for `prefixed` at the begin snapshot, noted as
    /// read by `parts`. A read by no parts is never validated, so it leaves
    /// no record at all.
    fn read_projected(&self, prefixed: &[u8], parts: &[u32]) -> std::io::Result<Option<DbSlice>> {
        if parts.is_empty() {
            return self.engine.get_slice_at(prefixed, self.snapshot_seq);
        }
        let state = self.tracked.get_or_insert(
            prefixed.to_vec(),
            Arc::new(KeyState::projected(self.snapshot_seq, parts)),
        );
        // Whichever cell won, add this read's parts: a no-op for a cell this
        // call made, and for one that already reads the key in whole.
        if let Some(projection) = &state.projection {
            projection.widen(parts);
        }
        self.read_noting(&state, prefixed, self.snapshot_seq)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parts(projection: &Projection) -> Option<Vec<u32>> {
        projection.with_parts(|parts| parts.map(<[u32]>::to_vec))
    }

    #[test]
    fn the_set_is_sorted_without_repeats_and_spills_past_the_inline_ids() {
        let projection = Projection::new(&[5, 1, 5]);
        assert_eq!(parts(&projection), Some(vec![1, 5]));
        projection.widen(&[3, 1]);
        assert_eq!(parts(&projection), Some(vec![1, 3, 5]));
        let many: Vec<u32> = (0..20).rev().collect();
        projection.widen(&many);
        assert_eq!(parts(&projection), Some((0..20).collect::<Vec<_>>()));
        projection.widen(&[7, 99]);
        assert_eq!(parts(&projection).unwrap().len(), 21);
    }

    #[test]
    fn a_whole_read_ends_the_set() {
        let projection = Projection::new(&[1]);
        projection.widen_to_full();
        projection.widen(&[2]);
        assert_eq!(parts(&projection), None);
    }

    #[test]
    fn no_parts_is_an_empty_set_not_a_whole_read() {
        assert_eq!(parts(&Projection::new(&[])), Some(Vec::new()));
    }
}
