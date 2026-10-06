//! Versionstamped puts: a write whose key or value carries the sequence its
//! commit assigns it.

/// Bytes a stamp occupies: the commit sequence as a big-endian `u64`, so
/// stamped keys sort in commit order.
pub const STAMP_LEN: usize = 8;

/// Where [`crate::Transaction::put_stamped`] writes the commit sequence: the
/// byte offset of an [`STAMP_LEN`]-byte placeholder in the key or the value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stamp {
    /// Stamp the key: the final key is unique, so the write never conflicts.
    Key(usize),
    /// Stamp the value of an ordinary, conflict-checked key.
    Value(usize),
}

/// A put buffered by a transaction until its commit sequence is known.
/// `key` is column-family prefixed, and a [`Stamp::Key`] offset is relative
/// to that prefixed key.
#[derive(Clone, Debug)]
pub(crate) struct StampedPut {
    pub key: Vec<u8>,
    pub value: Vec<u8>,
    pub at: Stamp,
}

pub(crate) fn fits(offset: usize, len: usize) -> bool {
    offset.checked_add(STAMP_LEN).is_some_and(|end| end <= len)
}

pub(crate) fn write(bytes: &mut [u8], offset: usize, seq: u64) {
    bytes[offset..offset + STAMP_LEN].copy_from_slice(&seq.to_be_bytes());
}
