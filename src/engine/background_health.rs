//! Whether the engine's background jobs are currently failing, and why.
//!
//! A flush or compaction that fails does not stop the engine: the job is
//! retried later. That is the right response to a passing fault and the
//! wrong one to a lasting one. While the disk is full, the descriptor
//! table is exhausted, or a file the engine needs has gone missing, every
//! retry fails the same way, and a writer stalled behind that work would
//! wait for it forever. The engine records the most recent failure of
//! each job here so a stalled writer can fail with the real cause instead,
//! and clears it on the job's next success.

use std::io;

use crate::portability::{AtomicU64, Ordering};
use crate::sync::internal::Mutex;

/// The background jobs a stalled writer can be waiting on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Job {
    Flush,
    Compaction,
}

impl Job {
    pub(crate) fn name(self) -> &'static str {
        match self {
            Job::Flush => "flush",
            Job::Compaction => "compaction",
        }
    }
}

/// The class of a failure, for operators deciding what to fix.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Hazard {
    DiskFull,
    OutOfFileDescriptors,
    MissingFile,
    Other,
}

impl Hazard {
    pub(crate) fn of(err: &io::Error) -> Self {
        match err.kind() {
            io::ErrorKind::StorageFull | io::ErrorKind::QuotaExceeded => return Hazard::DiskFull,
            io::ErrorKind::NotFound => return Hazard::MissingFile,
            _ => {}
        }
        if is_descriptor_exhaustion(err) {
            return Hazard::OutOfFileDescriptors;
        }
        Hazard::Other
    }

    pub(crate) fn label(self) -> &'static str {
        match self {
            Hazard::DiskFull => "disk full",
            Hazard::OutOfFileDescriptors => "out of file descriptors",
            Hazard::MissingFile => "missing file",
            Hazard::Other => "i/o error",
        }
    }
}

/// EMFILE and ENFILE have no `io::ErrorKind` of their own.
#[cfg(unix)]
fn is_descriptor_exhaustion(err: &io::Error) -> bool {
    const ENFILE: i32 = 23;
    const EMFILE: i32 = 24;
    matches!(err.raw_os_error(), Some(ENFILE | EMFILE))
}

#[cfg(windows)]
fn is_descriptor_exhaustion(err: &io::Error) -> bool {
    const ERROR_TOO_MANY_OPEN_FILES: i32 = 4;
    err.raw_os_error() == Some(ERROR_TOO_MANY_OPEN_FILES)
}

#[cfg(not(any(unix, windows)))]
fn is_descriptor_exhaustion(_err: &io::Error) -> bool {
    false
}

/// A recorded failure. `io::Error` is not `Clone`, so the parts needed to
/// rebuild an equivalent one are kept instead.
#[derive(Debug, Clone)]
pub(crate) struct Failure {
    pub(crate) job: Job,
    pub(crate) hazard: Hazard,
    kind: io::ErrorKind,
    raw_os_error: Option<i32>,
    message: String,
}

impl Failure {
    /// An `io::Error` equivalent to the one recorded: the OS error code
    /// when there was one, so a caller can still match on ENOSPC.
    pub(crate) fn to_io_error(&self) -> io::Error {
        match self.raw_os_error {
            Some(code) => io::Error::from_raw_os_error(code),
            None => io::Error::new(self.kind, self.message.clone()),
        }
    }
    /// The error a writer stalled behind this job returns.
    pub(crate) fn to_error(&self) -> crate::Error {
        crate::Error::BackgroundFailed {
            job: self.job.name(),
            hazard: self.hazard.label(),
            source: self.to_io_error(),
        }
    }
}

#[derive(Debug)]
pub(crate) struct BackgroundHealth {
    errors: AtomicU64,
    flush: Mutex<Option<Failure>>,
    compaction: Mutex<Option<Failure>>,
}

impl Default for BackgroundHealth {
    fn default() -> Self {
        Self {
            errors: AtomicU64::new(0),
            flush: Mutex::new(None),
            compaction: Mutex::new(None),
        }
    }
}

impl BackgroundHealth {
    fn slot(&self, job: Job) -> &Mutex<Option<Failure>> {
        match job {
            Job::Flush => &self.flush,
            Job::Compaction => &self.compaction,
        }
    }

    pub(crate) fn record_failure(&self, job: Job, err: &io::Error) -> Hazard {
        self.errors.fetch_add(1, Ordering::Relaxed);
        let hazard = Hazard::of(err);
        *self.slot(job).lock() = Some(Failure {
            job,
            hazard,
            kind: err.kind(),
            raw_os_error: err.raw_os_error(),
            message: err.to_string(),
        });
        hazard
    }

    pub(crate) fn record_success(&self, job: Job) {
        let mut slot = self.slot(job).lock();
        if slot.is_some() {
            *slot = None;
        }
    }

    /// The most recent failure of `job`, if its last attempt failed.
    pub(crate) fn failing(&self, job: Job) -> Option<Failure> {
        self.slot(job).lock().clone()
    }

    /// Failed background job attempts since open.
    pub(crate) fn error_count(&self) -> u64 {
        self.errors.load(Ordering::Relaxed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classifies_the_hazards_operators_act_on() {
        let full = io::Error::from(io::ErrorKind::StorageFull);
        assert_eq!(Hazard::of(&full), Hazard::DiskFull);
        let gone = io::Error::from(io::ErrorKind::NotFound);
        assert_eq!(Hazard::of(&gone), Hazard::MissingFile);
        let other = io::Error::other("boom");
        assert_eq!(Hazard::of(&other), Hazard::Other);
    }

    #[cfg(unix)]
    #[test]
    fn classifies_raw_errno_values() {
        assert_eq!(
            Hazard::of(&io::Error::from_raw_os_error(24)),
            Hazard::OutOfFileDescriptors
        );
        assert_eq!(
            Hazard::of(&io::Error::from_raw_os_error(23)),
            Hazard::OutOfFileDescriptors
        );
        // ENOSPC is 28 on every unix regolith targets.
        assert_eq!(
            Hazard::of(&io::Error::from_raw_os_error(28)),
            Hazard::DiskFull
        );
    }

    #[test]
    fn a_failure_is_cleared_by_the_same_jobs_next_success() {
        let health = BackgroundHealth::default();
        health.record_failure(Job::Compaction, &io::Error::other("boom"));
        assert!(health.failing(Job::Compaction).is_some());
        assert!(health.failing(Job::Flush).is_none());

        health.record_success(Job::Flush);
        assert!(health.failing(Job::Compaction).is_some());
        health.record_success(Job::Compaction);
        assert!(health.failing(Job::Compaction).is_none());
        assert_eq!(health.error_count(), 1);
    }

    #[cfg(unix)]
    #[test]
    fn the_rebuilt_error_keeps_the_os_error_code() {
        let health = BackgroundHealth::default();
        health.record_failure(Job::Flush, &io::Error::from_raw_os_error(28));
        let rebuilt = health.failing(Job::Flush).unwrap().to_io_error();
        assert_eq!(rebuilt.raw_os_error(), Some(28));
        assert_eq!(rebuilt.kind(), io::ErrorKind::StorageFull);
    }
}
