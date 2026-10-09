//! Failed repair I/O must fail the open and leave the old inputs recoverable.

use std::time::Duration;

use super::legacy_overlap_tests::{assert_layout, fixture};
use super::*;
use crate::env::{Capabilities, DirEntry, FileLock, FileMeta, JoinHandle, ReadFile, WriteFile};

#[derive(Clone, Copy, Debug)]
enum Failure {
    Write,
    Sync,
}

struct FailingWriter {
    inner: Box<dyn WriteFile>,
    failure: Failure,
}

impl WriteFile for FailingWriter {
    fn write_all(&mut self, bytes: &[u8]) -> io::Result<()> {
        if matches!(self.failure, Failure::Write) {
            self.inner.write_all(&bytes[..bytes.len() / 2])?;
            return Err(io::Error::other("injected repair append failure"));
        }
        self.inner.write_all(bytes)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }

    fn sync_all(&mut self) -> io::Result<()> {
        if matches!(self.failure, Failure::Sync) {
            return Err(io::Error::other("injected repair sync failure"));
        }
        self.inner.sync_all()
    }

    fn set_len(&mut self, len: u64) -> io::Result<()> {
        self.inner.set_len(len)
    }

    fn len(&self) -> io::Result<u64> {
        self.inner.len()
    }
}

#[derive(Debug)]
struct FailingEnv {
    inner: Arc<dyn Env>,
    failure: Failure,
}

impl Env for FailingEnv {
    fn create_dir_all(&self, path: &Path) -> io::Result<()> {
        self.inner.create_dir_all(path)
    }

    fn read_dir(&self, path: &Path) -> io::Result<Vec<DirEntry>> {
        self.inner.read_dir(path)
    }

    fn open_read(&self, path: &Path) -> io::Result<Box<dyn ReadFile>> {
        self.inner.open_read(path)
    }

    fn open_write(&self, path: &Path, mode: WriteMode) -> io::Result<Box<dyn WriteFile>> {
        let inner = self.inner.open_write(path, mode)?;
        if matches!(mode, WriteMode::Append) && path.file_name().is_some_and(|n| n == "MANIFEST") {
            return Ok(Box::new(FailingWriter {
                inner,
                failure: self.failure,
            }));
        }
        Ok(inner)
    }

    fn metadata(&self, path: &Path) -> io::Result<FileMeta> {
        self.inner.metadata(path)
    }

    fn remove_file(&self, path: &Path) -> io::Result<()> {
        self.inner.remove_file(path)
    }

    fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        self.inner.rename(from, to)
    }

    fn hard_link(&self, from: &Path, to: &Path) -> io::Result<()> {
        self.inner.hard_link(from, to)
    }

    fn sync_dir(&self, path: &Path) -> io::Result<()> {
        self.inner.sync_dir(path)
    }

    fn lock_file(&self, path: &Path, exclusive: bool) -> io::Result<Box<dyn FileLock>> {
        self.inner.lock_file(path, exclusive)
    }

    fn capabilities(&self) -> Capabilities {
        self.inner.capabilities()
    }

    fn now_micros(&self) -> Option<u64> {
        self.inner.now_micros()
    }

    fn unix_secs(&self) -> Option<u64> {
        self.inner.unix_secs()
    }

    fn spawn(
        &self,
        name: &str,
        body: Box<dyn FnOnce() + Send + 'static>,
    ) -> io::Result<Box<dyn JoinHandle>> {
        self.inner.spawn(name, body)
    }

    fn sleep(&self, duration: Duration) {
        self.inner.sleep(duration)
    }
}

#[test]
fn repair_append_and_sync_failures_fail_the_open_and_keep_every_table() {
    for failure in [Failure::Write, Failure::Sync] {
        let (dir, _) = fixture();
        let sst_dir = dir.path().join("sst");
        let env: Arc<dyn Env> = Arc::new(FailingEnv {
            inner: crate::env::std_env(),
            failure,
        });
        let error =
            VersionSet::open_with_policy(&env, dir.path(), &sst_dir, MetadataPolicy::Pinned)
                .err()
                .expect("repair I/O must fail the open");
        assert!(error.to_string().contains("injected repair"));
        for id in [8, 3, 10, 90, 77] {
            assert!(
                sst_dir.join(sst_filename(id)).exists(),
                "table {id} after {failure:?}"
            );
        }
        let vs = VersionSet::open(dir.path(), &sst_dir).unwrap();
        assert_layout(&vs.current());
    }
}
