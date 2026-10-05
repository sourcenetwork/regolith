use crate::env::{
    Capabilities, DirEntry, Env, FileLock, FileMeta, JoinHandle, ReadFile, StdEnv, WriteFile,
    WriteMode,
};
use std::{
    io,
    path::Path,
    sync::{Arc, Mutex},
};

#[derive(Debug, Default)]
pub(super) struct Recording {
    pub writes: Vec<Vec<u8>>,
    pub data_syncs: usize,
    pub fail_on_write: Option<usize>,
    pub partial_failures: usize,
}

#[derive(Debug, Default)]
pub(super) struct RecordingEnv {
    inner: StdEnv,
    pub events: Arc<Mutex<Recording>>,
}

struct RecordingWrite {
    inner: Box<dyn WriteFile>,
    events: Arc<Mutex<Recording>>,
}

impl WriteFile for RecordingWrite {
    fn write_all(&mut self, bytes: &[u8]) -> io::Result<()> {
        let mut events = self.events.lock().unwrap();
        events.writes.push(bytes.to_vec());
        if events.fail_on_write == Some(events.writes.len()) {
            events.fail_on_write = None;
            events.partial_failures += 1;
            drop(events);
            self.inner.write_all(&bytes[..7])?;
            return Err(io::Error::other("injected partial recovery write"));
        }
        drop(events);
        self.inner.write_all(bytes)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }

    fn sync_all(&mut self) -> io::Result<()> {
        self.inner.sync_all()
    }

    fn sync_data(&mut self) -> io::Result<()> {
        self.events.lock().unwrap().data_syncs += 1;
        self.inner.sync_data()
    }

    fn set_len(&mut self, len: u64) -> io::Result<()> {
        self.inner.set_len(len)
    }

    fn len(&self) -> io::Result<u64> {
        self.inner.len()
    }
}

impl Env for RecordingEnv {
    fn open_write(&self, path: &Path, mode: WriteMode) -> io::Result<Box<dyn WriteFile>> {
        let inner = self.inner.open_write(path, mode)?;
        let is_wal = path.extension().is_some_and(|extension| extension == "wal")
            || path
                .parent()
                .and_then(Path::file_name)
                .is_some_and(|name| name == "wal");
        if !is_wal {
            return Ok(inner);
        }
        Ok(Box::new(RecordingWrite {
            inner,
            events: Arc::clone(&self.events),
        }))
    }
    fn create_dir_all(&self, path: &Path) -> io::Result<()> {
        self.inner.create_dir_all(path)
    }
    fn read_dir(&self, path: &Path) -> io::Result<Vec<DirEntry>> {
        self.inner.read_dir(path)
    }
    fn open_read(&self, path: &Path) -> io::Result<Box<dyn ReadFile>> {
        self.inner.open_read(path)
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
    fn sleep(&self, duration: std::time::Duration) {
        self.inner.sleep(duration)
    }
}
