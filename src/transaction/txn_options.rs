//! Per-transaction settings passed to `begin`.
//!
//! A [`TxnOptions`] is plain data: copying it is free and it holds no
//! reference to a database. Anything it leaves unset falls back to what the
//! database it is begun on is configured with.

use super::IsolationLevel;

/// Settings for one transaction, passed to
/// [`OptimisticTransactionDb::begin`](super::OptimisticTransactionDb::begin) or
/// [`TransactionDb::begin`](super::TransactionDb::begin).
///
/// ```
/// use regolith::{IsolationLevel, TxnOptions};
///
/// let default = TxnOptions::new();
/// let serializable = TxnOptions::new().isolation(IsolationLevel::Serializable);
/// ```
#[derive(Clone, Copy, Debug, Default)]
#[non_exhaustive]
pub struct TxnOptions {
    isolation: Option<IsolationLevel>,
    early_validation: bool,
}

impl TxnOptions {
    /// Options that leave every setting at the database's configured value.
    pub const fn new() -> Self {
        Self {
            isolation: None,
            early_validation: false,
        }
    }

    /// Begin the transaction at `isolation`, whatever the database default is.
    ///
    /// The level is a property of what a unit of work needs rather than of the
    /// database: a read-mostly query and a read-modify-write against the same
    /// database want different answers, and paying serializable validation for
    /// the former is waste. Unset, the transaction uses the level the database
    /// was configured with through `with_isolation`.
    pub const fn isolation(mut self, isolation: IsolationLevel) -> Self {
        self.isolation = Some(isolation);
        self
    }

    /// Check each write against newer versions as it is made, and fail the
    /// write at once with [`crate::TransactionError::Conflict`] when the commit
    /// could only lose, instead of at commit after the rest of the work is
    /// done. Off by default: it costs one probe of the key per write (a read
    /// of its value too, for a put or delete that is about to conflict).
    ///
    /// Only an optimistic transaction validates early; a pessimistic one
    /// ignores this, its locks already order its writes. The check is the
    /// commit's own check of one written key, so it never fails a write the
    /// commit would pass at that moment, with two limits that keep it from
    /// failing one that a later read would clear: a key this transaction has
    /// read, and every key once it has scanned, are left to the commit. A
    /// write that passes may still conflict at commit, because the key can
    /// change after the check, and one that fails may have passed had the
    /// transaction waited, because the newer version can be rewritten back.
    /// With a [`crate::KeyClassifier`] installed at
    /// [`IsolationLevel::DefraLevel`] the classifier is asked about each
    /// written key as well, and a put or merge of a content-addressed key is
    /// not checked.
    pub const fn early_validation(mut self, on: bool) -> Self {
        self.early_validation = on;
        self
    }

    /// Whether writes are checked as they are made.
    pub(super) fn early(&self) -> bool {
        self.early_validation
    }

    /// The level this transaction runs at, given the database's configured
    /// `default`. The one place both database flavors resolve it.
    pub(super) fn resolve_isolation(&self, default: IsolationLevel) -> IsolationLevel {
        self.isolation.unwrap_or(default)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unset_isolation_takes_the_database_default() {
        let opts = TxnOptions::new();
        for default in [
            IsolationLevel::ReadCommitted,
            IsolationLevel::SnapshotIsolation,
            IsolationLevel::Serializable,
            IsolationLevel::DefraLevel,
        ] {
            assert_eq!(opts.resolve_isolation(default), default);
        }
    }

    #[test]
    fn explicit_isolation_overrides_the_database_default() {
        let opts = TxnOptions::new().isolation(IsolationLevel::Serializable);
        assert_eq!(
            opts.resolve_isolation(IsolationLevel::ReadCommitted),
            IsolationLevel::Serializable
        );
    }

    #[test]
    fn early_validation_is_off_until_asked_for() {
        assert!(!TxnOptions::new().early());
        assert!(TxnOptions::new().early_validation(true).early());
        assert!(
            !TxnOptions::new()
                .early_validation(true)
                .early_validation(false)
                .early()
        );
        assert!(!TxnOptions::default().early());
    }

    #[test]
    fn default_is_new() {
        assert_eq!(
            TxnOptions::default().resolve_isolation(IsolationLevel::RepeatableRead),
            TxnOptions::new().resolve_isolation(IsolationLevel::RepeatableRead)
        );
    }
}
