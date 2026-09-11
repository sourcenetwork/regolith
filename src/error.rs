/// Errors returned by regolith operations.
#[non_exhaustive]
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// A caller supplied an invalid option, key, value, range, or
    /// other API argument.
    #[error("invalid argument: {0}")]
    InvalidArgument(String),
    /// On-disk database, WAL, SSTable, manifest, or backup data was
    /// malformed or truncated.
    #[error("corruption: {0}")]
    Corruption(#[source] std::io::Error),
    /// A mutating operation was attempted through a read-only handle.
    #[error("database was opened read-only")]
    ReadOnly,
    /// An operation was attempted after the database handle was closed.
    #[error("database is closed")]
    Closed,
    /// A column-family handle or id is stale, dropped, or belongs to a
    /// different database handle.
    #[error("invalid column family: {0}")]
    InvalidColumnFamily(String),
    /// The engine refused to block the caller and returned early.
    /// Returned when [`crate::WriteOptions::no_slowdown`] is set and
    /// the engine is currently stalling writes (too many L0 files,
    /// too many unflushed memtables, or pending compaction bytes
    /// over the hard limit). The included string names the active
    /// stall condition for diagnostics.
    #[error("engine busy: {0}")]
    Busy(&'static str),
    /// The configured [`crate::MergeOperator`] returned `None` when
    /// asked to combine a value with one or more merge operands,
    /// indicating that the operands were corrupt or the merge
    /// semantics failed. The offending user key is included for
    /// diagnostics.
    #[error("merge operator failed for key {0:?}")]
    MergeFailed(Vec<u8>),
    /// An underlying I/O error from the filesystem or operating system.
    #[error("I/O error: {0}")]
    Io(#[source] std::io::Error),
}

impl Error {
    pub(crate) fn invalid_argument(message: impl Into<String>) -> Self {
        Self::InvalidArgument(message.into())
    }

    pub(crate) fn invalid_column_family(message: impl Into<String>) -> Self {
        Self::InvalidColumnFamily(message.into())
    }

    pub(crate) fn corruption(message: impl Into<String>) -> Self {
        Self::Corruption(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            message.into(),
        ))
    }

    /// Render this engine error as the `io::Error` a caller on an
    /// `io::Result` boundary sees, preserving the kind and message a
    /// direct `io::Error` path (a closed handle, a read-only handle)
    /// already uses for the same condition. The one function both
    /// [`crate::transaction::TransactionError`]'s `From<Error>` impl and
    /// the engine's own `io::Result` commit path call, so the two never
    /// drift apart on what a given `Error` variant reads as.
    pub(crate) fn into_io_error(self) -> std::io::Error {
        match self {
            Self::Io(io) | Self::Corruption(io) => io,
            Self::InvalidArgument(message) | Self::InvalidColumnFamily(message) => {
                std::io::Error::new(std::io::ErrorKind::InvalidInput, message)
            }
            Self::ReadOnly => std::io::Error::new(
                std::io::ErrorKind::PermissionDenied,
                "database was opened read-only",
            ),
            Self::Closed => {
                std::io::Error::new(std::io::ErrorKind::NotConnected, "database is closed")
            }
            other => std::io::Error::other(other.to_string()),
        }
    }
}

impl From<std::io::Error> for Error {
    fn from(err: std::io::Error) -> Self {
        match err.kind() {
            std::io::ErrorKind::InvalidInput => Self::InvalidArgument(err.to_string()),
            std::io::ErrorKind::InvalidData | std::io::ErrorKind::UnexpectedEof => {
                Self::Corruption(err)
            }
            std::io::ErrorKind::NotConnected if err.to_string() == "database is closed" => {
                Self::Closed
            }
            _ => Self::Io(err),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn io_error_converts_via_from_when_filesystem_related() {
        let ioe = std::io::Error::new(std::io::ErrorKind::NotFound, "nope");
        let e: Error = ioe.into();
        assert!(matches!(e, Error::Io(_)));
    }

    #[test]
    fn invalid_input_converts_to_invalid_argument() {
        let ioe = std::io::Error::new(std::io::ErrorKind::InvalidInput, "bad key");
        let e: Error = ioe.into();
        assert!(matches!(e, Error::InvalidArgument(msg) if msg.contains("bad key")));
    }

    #[test]
    fn corruption_kinds_convert_to_corruption() {
        for kind in [
            std::io::ErrorKind::InvalidData,
            std::io::ErrorKind::UnexpectedEof,
        ] {
            let ioe = std::io::Error::new(kind, "bad bytes");
            let e: Error = ioe.into();
            assert!(matches!(e, Error::Corruption(source) if source.kind() == kind));
        }
    }

    #[test]
    fn busy_display_contains_reason() {
        let e = Error::Busy("too many L0 files");
        let msg = format!("{e}");
        assert!(msg.contains("too many L0 files"));
        assert!(msg.contains("busy"));
    }

    #[test]
    fn merge_failed_display_contains_key_bytes() {
        let e = Error::MergeFailed(b"k".to_vec());
        let msg = format!("{e}");
        assert!(msg.contains("merge"));
        // Debug-printed key bytes show up as `[107]`.
        assert!(msg.contains("107"));
    }
}
