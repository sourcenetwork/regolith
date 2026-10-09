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
}

impl TxnOptions {
    /// Options that leave every setting at the database's configured value.
    pub const fn new() -> Self {
        Self { isolation: None }
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
    fn default_is_new() {
        assert_eq!(
            TxnOptions::default().resolve_isolation(IsolationLevel::RepeatableRead),
            TxnOptions::new().resolve_isolation(IsolationLevel::RepeatableRead)
        );
    }
}
