//! Conflict-free allocation of ranges from a `u64` counter: [`Db::allocate`].

use std::ops::Range;

use crate::column_family::{DEFAULT_CF_ID, prefix_key};
use crate::{Db, Error, Result};

impl Db {
    /// Reserves `n` consecutive values from the counter stored at `key` in
    /// the default column family, and returns them as a range.
    ///
    /// The key holds the last value reserved as an 8-byte big-endian `u64`,
    /// and absent means 0, so the first call on a new key returns `1..n + 1`.
    /// A later call returns a range that starts after the end of every range
    /// before it, so no value is returned twice and ranges only grow.
    /// `allocate(key, 0)` reserves nothing, writes nothing and returns an
    /// empty range at the next value.
    ///
    /// # Guarantees
    ///
    /// - **Never a conflict.** The reservation happens in the commit pipeline
    ///   and is not part of any transaction, so it cannot fail a transaction
    ///   or be failed by one, and concurrent callers all succeed.
    /// - **Unique across crashes.** The reservation is written to the
    ///   write-ahead log before this call returns, so before any commit that
    ///   uses one of its values. A crash that keeps a commit using a value
    ///   keeps the reservation, and the counter recovers at or above every
    ///   value in use: after a crash no value that a surviving commit used is
    ///   returned again.
    /// - **No wait for the device.** The reservation does not sync the log. It
    ///   becomes durable with the next sync, at the latest with the first
    ///   commit that uses one of its values. A value that was only handed to
    ///   the outside world, and not used by a committed write, can be returned
    ///   again after a crash.
    /// - **Not stalled.** It does not wait while writes are stalled.
    /// - **Gaps.** Values reserved by code that never commits a use, such as
    ///   a transaction that aborts, are skipped for good.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidArgument`], with nothing reserved, when `key` is
    /// longer than [`Options::max_key_size`](crate::Options::max_key_size),
    /// when the key holds anything but eight bytes, or when fewer than `n`
    /// values remain below `u64::MAX`. [`Error::ReadOnly`] and
    /// [`Error::Closed`] as for any write.
    ///
    /// # Preconditions
    ///
    /// Only this call writes the key. A write by anything else, a [`Db::put`]
    /// or a transaction included, can move the counter back or fill it with
    /// bytes that are no number, and regolith cannot tell.
    pub fn allocate(&self, key: &[u8], n: u64) -> Result<Range<u64>> {
        self.ensure_writable()?;
        self.validate_key_size(key)?;
        self.engine
            .allocate(prefix_key(DEFAULT_CF_ID, key), n)
            .map_err(Error::from)
    }
}
