#![cfg(not(target_arch = "wasm32"))]

use regolith::env::{
    Capabilities, DirEntry, Env, FileLock, FileMeta, JoinHandle, MemEnv, ReadFile, WriteFile,
    WriteMode,
};
use regolith::{CompactionStyle, Db, DurabilityMode, Options};
use std::io;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::Duration;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Failure {
    Create,
    Write,
    Sync,
    ReaderOpen,
    Metadata,
    ManifestWrite,
    ManifestSync,
}

#[derive(Debug, Default)]
struct FailureState {
    failure: Option<Failure>,
    remaining: usize,
    fired: bool,
    error: i32,
}

fn fail(state: &Mutex<FailureState>, failure: Failure, path: &Path) -> io::Result<()> {
    let mut state = state.lock().unwrap();
    let manifest = path.file_name().is_some_and(|name| name == "MANIFEST");
    let table = path.extension().is_some_and(|ext| ext == "sst");
    if state.failure == Some(failure)
        && (table || manifest && matches!(failure, Failure::ManifestWrite | Failure::ManifestSync))
    {
        if state.remaining == 0 {
            state.fired = true;
            return Err(io::Error::from_raw_os_error(state.error));
        }
        state.remaining -= 1;
    }
    Ok(())
}

#[derive(Debug, Default)]
struct FailureEnv {
    inner: MemEnv,
    state: Arc<Mutex<FailureState>>,
}
impl FailureEnv {
    fn fail(&self, failure: Failure, path: &Path) -> io::Result<()> {
        fail(&self.state, failure, path)
    }
    fn arm(&self, failure: Failure, remaining: usize, error: i32) {
        *self.state.lock().unwrap() = FailureState {
            failure: Some(failure),
            remaining,
            fired: false,
            error,
        };
    }
    fn disarm(&self) {
        self.state.lock().unwrap().failure = None;
    }
}
struct FailureFile {
    inner: Box<dyn WriteFile>,
    path: PathBuf,
    state: Arc<Mutex<FailureState>>,
}
impl WriteFile for FailureFile {
    fn write_all(&mut self, bytes: &[u8]) -> io::Result<()> {
        let manifest = self.path.file_name().is_some_and(|name| name == "MANIFEST");
        // Reservations cannot publish an output. Fail the replacement batch.
        if !manifest || bytes.get(4) == Some(&2) {
            fail(
                &self.state,
                if manifest {
                    Failure::ManifestWrite
                } else {
                    Failure::Write
                },
                &self.path,
            )?;
        }
        self.inner.write_all(bytes)
    }
    fn sync_all(&mut self) -> io::Result<()> {
        let failure = if self.path.file_name().is_some_and(|name| name == "MANIFEST") {
            Failure::ManifestSync
        } else {
            Failure::Sync
        };
        fail(&self.state, failure, &self.path)?;
        self.inner.sync_all()
    }
    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
    fn set_len(&mut self, len: u64) -> io::Result<()> {
        self.inner.set_len(len)
    }
    fn len(&self) -> io::Result<u64> {
        self.inner.len()
    }
}
impl Env for FailureEnv {
    fn create_dir_all(&self, path: &Path) -> io::Result<()> {
        self.inner.create_dir_all(path)
    }

    fn read_dir(&self, path: &Path) -> io::Result<Vec<DirEntry>> {
        self.inner.read_dir(path)
    }

    fn open_read(&self, path: &Path) -> io::Result<Box<dyn ReadFile>> {
        self.fail(Failure::ReaderOpen, path)?;
        self.inner.open_read(path)
    }

    fn open_write(&self, path: &Path, mode: WriteMode) -> io::Result<Box<dyn WriteFile>> {
        self.fail(Failure::Create, path)?;
        let inner = self.inner.open_write(path, mode)?;
        Ok(Box::new(FailureFile {
            inner,
            path: path.to_owned(),
            state: self.state.clone(),
        }))
    }

    fn metadata(&self, path: &Path) -> io::Result<FileMeta> {
        self.fail(Failure::Metadata, path)?;
        self.inner.metadata(path)
    }

    fn remove_file(&self, path: &Path) -> io::Result<()> {
        self.inner.remove_file(path)
    }

    fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        self.inner.rename(from, to)
    }

    fn hard_link(&self, src: &Path, dst: &Path) -> io::Result<()> {
        self.inner.hard_link(src, dst)
    }

    fn sync_dir(&self, path: &Path) -> io::Result<()> {
        self.inner.sync_dir(path)
    }

    fn lock_file(&self, path: &Path, exclusive: bool) -> io::Result<Box<dyn FileLock>> {
        self.inner.lock_file(path, exclusive)
    }

    fn capabilities(&self) -> Capabilities {
        let mut capabilities = self.inner.capabilities();
        capabilities.durable_sync = true;
        capabilities
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

    fn sleep(&self, dur: Duration) {
        self.inner.sleep(dur);
    }
}

fn options(env: Arc<FailureEnv>) -> Options {
    Options {
        env,
        durability: DurabilityMode::Immediate,
        max_background_compactions: 0,
        compaction_style: CompactionStyle::Level,
        write_buffer_size: 1 << 20,
        l0_compaction_trigger: 1_000_000,
        target_file_size: 128,
        block_size: 64,
        ..Options::default()
    }
}
fn seed(env: &Arc<FailureEnv>) -> Db {
    let db = Db::open("compaction-cleanup", options(env.clone())).unwrap();
    for file in 0..4 {
        for key in 0..32 {
            db.put(format!("key-{file}-{key:02}").as_bytes(), &[b'v'; 128])
                .unwrap();
        }
        db.flush().unwrap();
    }
    db
}
fn tables(env: &FailureEnv) -> Vec<PathBuf> {
    let mut files: Vec<_> = env
        .read_dir(Path::new("compaction-cleanup/sst"))
        .unwrap()
        .into_iter()
        .map(|entry| entry.path)
        .collect();
    files.sort();
    files
}
fn assert_keys(db: &Db) {
    for file in 0..4 {
        for key in 0..32 {
            assert_eq!(
                db.get(format!("key-{file}-{key:02}").as_bytes()).unwrap(),
                Some(vec![b'v'; 128])
            );
        }
    }
}
#[test]
fn failed_compactions_remove_only_their_unpublished_outputs() {
    for error in [24, 28] {
        for failure in [
            Failure::Create,
            Failure::Write,
            Failure::Sync,
            Failure::ReaderOpen,
            Failure::Metadata,
        ] {
            for remaining in [0, 1, 3] {
                let env = Arc::new(FailureEnv::default());
                let db = seed(&env);
                let original = tables(&env);
                for _ in 0..3 {
                    env.arm(failure, remaining, error);
                    let result = db.compact_range(None, None);
                    assert!(
                        env.state.lock().unwrap().fired,
                        "{failure:?}/{remaining}: {result:?}"
                    );
                    assert!(result.is_err());
                    env.disarm();
                    assert_eq!(tables(&env), original, "{failure:?}/{remaining}");
                    assert_keys(&db);
                }
                db.compact_range(None, None).unwrap();
                assert_keys(&db);
                db.close().unwrap();
                drop(db);
                let reopened = Db::open("compaction-cleanup", options(env)).unwrap();
                assert_keys(&reopened);
                reopened.close().unwrap();
            }
        }
    }
}

#[test]
fn uncertain_manifest_publication_preserves_recoverable_outputs() {
    for failure in [Failure::ManifestWrite, Failure::ManifestSync] {
        let env = Arc::new(FailureEnv::default());
        let db = seed(&env);
        let original = tables(&env);
        env.arm(failure, 0, 28);
        assert!(db.compact_range(None, None).is_err());
        assert!(env.state.lock().unwrap().fired);
        env.disarm();
        assert!(tables(&env).len() > original.len());
        let pending = tables(&env);
        for _ in 0..3 {
            assert!(db.compact_range(None, None).is_err());
            assert_eq!(tables(&env), pending);
        }
        assert_keys(&db);
        drop(db);
        let reopened = Db::open("compaction-cleanup", options(env)).unwrap();
        assert_keys(&reopened);
        reopened.close().unwrap();
    }
}

#[test]
fn failed_tombstone_only_outputs_are_removed() {
    for failure in [
        Failure::Create,
        Failure::Write,
        Failure::Sync,
        Failure::ReaderOpen,
        Failure::Metadata,
    ] {
        let env = Arc::new(FailureEnv::default());
        let db = Db::open("compaction-cleanup", options(env.clone())).unwrap();
        db.delete_range(b"a", b"z").unwrap();
        db.flush().unwrap();
        let original = tables(&env);
        assert!(!original.is_empty());
        env.arm(failure, 0, 28);
        assert!(db.compact_range(None, None).is_err());
        assert!(env.state.lock().unwrap().fired, "{failure:?}");
        env.disarm();
        assert_eq!(tables(&env), original, "{failure:?}");
        db.compact_range(None, None).unwrap();
        db.close().unwrap();
    }
}
