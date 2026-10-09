/// Errors returned by regolith operations.
#[non_exhaustive]
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// A caller supplied an invalid option, key, value, range, or
    /// other API argument.
    #[error("invalid argument: {0}")]
    InvalidArgument(String),
    /// A size read exceeded its per-SST-data-block frame plus decoded-buffer limit.
    #[error("SST data block exceeds allocation limit of {max_data_block_bytes} bytes")]
    DataBlockLimitExceeded {
        /// The caller's limit, not the size of the block or value.
        max_data_block_bytes: usize,
    },
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
    /// A write was stalled behind background work (a flush or a
    /// compaction) whose most recent attempt failed, so waiting would not
    /// end. `source` carries the failure, OS error code included, so a
    /// caller can tell a full disk (ENOSPC) or an exhausted descriptor
    /// table (EMFILE) from anything else. The engine keeps retrying; a
    /// later write succeeds once the job does.
    #[error("background {job} is failing ({hazard}), so writes cannot proceed: {source}")]
    BackgroundFailed {
        /// The job the write was waiting on: `"flush"` or `"compaction"`.
        job: &'static str,
        /// The class of the failure, such as `"disk full"`.
        hazard: &'static str,
        /// The failure itself.
        #[source]
        source: std::io::Error,
    },
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
    /// already uses for the same condition.
    ///
    /// The variants that carry no payload beyond what the error itself says
    /// travel inside the `io::Error` as its source, and `From<io::Error>`
    /// takes them back out, so a caller on the other side matches the
    /// variant and never the message. Every `io::Result` path in the engine
    /// goes through this one function, so none drifts from the others on what
    /// a given `Error` variant reads as.
    pub(crate) fn into_io_error(self) -> std::io::Error {
        match self {
            Self::Io(io) | Self::Corruption(io) => io,
            Self::BackgroundFailed { source, .. } => source,
            Self::InvalidArgument(message) | Self::InvalidColumnFamily(message) => {
                std::io::Error::new(std::io::ErrorKind::InvalidInput, message)
            }
            Self::ReadOnly => {
                std::io::Error::new(std::io::ErrorKind::PermissionDenied, Self::ReadOnly)
            }
            Self::Closed => std::io::Error::new(std::io::ErrorKind::NotConnected, Self::Closed),
            typed @ (Self::DataBlockLimitExceeded { .. } | Self::Busy(_)) => {
                std::io::Error::other(typed)
            }
            other => std::io::Error::other(other.to_string()),
        }
    }
}

/// The payload-free variant `err` carries as its source, if
/// [`Error::into_io_error`] built it from one.
fn carried(err: &std::io::Error) -> Option<Error> {
    match err.get_ref()?.downcast_ref::<Error>()? {
        Error::DataBlockLimitExceeded {
            max_data_block_bytes,
        } => Some(Error::DataBlockLimitExceeded {
            max_data_block_bytes: *max_data_block_bytes,
        }),
        Error::Closed => Some(Error::Closed),
        Error::ReadOnly => Some(Error::ReadOnly),
        Error::Busy(reason) => Some(Error::Busy(reason)),
        _ => None,
    }
}

impl Error {
    /// A copy of `err`, for a failure handed to several callers:
    /// `io::Error` is not `Clone`. Kind and message are rebuilt, and a typed
    /// variant the error carries stays that variant.
    pub(crate) fn clone_io(err: &std::io::Error) -> std::io::Error {
        match carried(err) {
            Some(typed) => typed.into_io_error(),
            None => std::io::Error::new(err.kind(), err.to_string()),
        }
    }
}

impl From<std::io::Error> for Error {
    fn from(err: std::io::Error) -> Self {
        if let Some(typed) = carried(&err) {
            return typed;
        }
        match err.kind() {
            std::io::ErrorKind::InvalidInput => Self::InvalidArgument(err.to_string()),
            std::io::ErrorKind::InvalidData | std::io::ErrorKind::UnexpectedEof => {
                Self::Corruption(err)
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
    fn typed_variants_survive_a_round_trip_through_io_error() {
        for typed in [
            Error::Closed,
            Error::ReadOnly,
            Error::Busy("too many L0 files"),
            Error::DataBlockLimitExceeded {
                max_data_block_bytes: 4096,
            },
        ] {
            let text = typed.to_string();
            let io = typed.into_io_error();
            assert_eq!(io.to_string(), text);
            let back = Error::from(io);
            assert_eq!(back.to_string(), text);
            assert!(!matches!(back, Error::Io(_)), "{back:?} lost its variant");
        }
    }

    #[test]
    fn a_cloned_io_error_keeps_its_variant() {
        for typed in [Error::Closed, Error::ReadOnly, Error::Busy("stalled")] {
            let text = typed.to_string();
            let copy = Error::clone_io(&typed.into_io_error());
            assert_eq!(copy.to_string(), text);
            assert!(!matches!(Error::from(copy), Error::Io(_)));
        }
    }

    #[test]
    fn closed_keeps_its_io_kind_and_message() {
        let io = Error::Closed.into_io_error();
        assert_eq!(io.kind(), std::io::ErrorKind::NotConnected);
        assert_eq!(io.to_string(), "database is closed");
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
