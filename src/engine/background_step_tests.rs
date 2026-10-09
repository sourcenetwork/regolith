//! Flushes off the commit path (E9) and their order in L0 (`LsmOrder.tla`,
//! RED FlushAnyOrder).

use std::sync::mpsc;
use std::sync::{Arc, OnceLock, Weak};
use std::time::Duration;

use tempfile::TempDir;

use super::{DurabilityMode, EngineOptions, RegolithEngine};
use crate::WriteBatchOp;
use crate::column_family::{DEFAULT_CF_ID, prefix_key};
use crate::event_listener::{EventListener, FlushJobInfo};

fn key_of(name: &[u8]) -> Vec<u8> {
    prefix_key(DEFAULT_CF_ID, name)
}

fn put(engine: &RegolithEngine, name: &[u8], value: &[u8]) -> std::io::Result<u64> {
    engine.apply_batch(
        vec![WriteBatchOp::Put {
            key: key_of(name),
            value: value.to_vec(),
        }],
        DurabilityMode::Eventual,
        false,
    )
}

/// A buffer that two 1 KiB puts fill, so the third rotates it.
fn tiny(workers: usize) -> EngineOptions {
    EngineOptions {
        write_buffer_size: 2 * 1024,
        max_background_compactions: workers,
        ..EngineOptions::default()
    }
}

/// Write until the active memtable is sealed, returning how many puts it took.
fn write_until_sealed(engine: &RegolithEngine, prefix: &str) -> usize {
    let frozen_before = engine.view.load().frozen.len();
    let active_before = Arc::clone(&engine.view.load().active);
    for i in 0..64 {
        put(engine, format!("{prefix}{i:03}").as_bytes(), &[7u8; 1024]).unwrap();
        let view = engine.view.load();
        if !Arc::ptr_eq(&view.active, &active_before) {
            assert!(view.frozen.len() <= frozen_before + 1);
            return i + 1;
        }
    }
    panic!("64 puts of 1 KiB never rotated a 2 KiB buffer");
}

/// A rotating write seals the memtable and returns without flushing it: with
/// the flush exclusion held by this test, a write that flushed under the
/// commit mutex would wait here instead of returning.
#[test]
fn a_rotating_write_returns_without_flushing() {
    let dir = TempDir::new().unwrap();
    let engine = RegolithEngine::open(dir.path(), tiny(1)).unwrap();
    let flushing = engine.flusher.flushing.lock();
    let (done, returned) = mpsc::channel();
    std::thread::scope(|scope| {
        scope.spawn(|| {
            done.send(write_until_sealed(&engine, "k")).unwrap();
        });
        returned
            .recv_timeout(Duration::from_secs(30))
            .expect("the rotating write waited for a flush");
        assert_eq!(
            engine.view.load().frozen.len(),
            1,
            "the sealed memtable waits for the background"
        );
        drop(flushing);
    });
}

/// The worker writes out what writers seal: the frozen list drains with no
/// call that flushes.
#[test]
fn the_worker_flushes_what_a_rotation_sealed() {
    let dir = TempDir::new().unwrap();
    let engine = RegolithEngine::open(dir.path(), tiny(1)).unwrap();
    write_until_sealed(&engine, "k");
    let deadline = std::time::Instant::now() + Duration::from_secs(60);
    let mut pause = Duration::from_millis(1);
    while !engine.view.load().frozen.is_empty() {
        assert!(
            std::time::Instant::now() < deadline,
            "the worker never flushed the sealed memtable"
        );
        std::thread::sleep(pause);
        pause = (pause * 2).min(Duration::from_millis(50));
    }
    assert!(!engine.view.load().version.levels[0].is_empty());
    assert_eq!(
        engine.get(&key_of(b"k000"), u64::MAX).unwrap(),
        Some(vec![7u8; 1024])
    );
}

/// Checks, when it is told of a flush, whether the commit pipeline is free.
#[derive(Default)]
struct PipelineFreeDuringFlush {
    engine: OnceLock<Weak<RegolithEngine>>,
    free: std::sync::Mutex<Vec<bool>>,
}

impl EventListener for PipelineFreeDuringFlush {
    fn on_flush_completed(&self, _: &FlushJobInfo) {
        if let Some(engine) = self.engine.get().and_then(Weak::upgrade) {
            let free = engine.pipeline.try_lock().is_some();
            self.free.lock().unwrap().push(free);
        }
    }
}

/// Without a worker the write that sealed the memtable flushes it, once its
/// own commit has left the pipeline: the flush is done when the write
/// returns, and the pipeline was free while it ran.
#[test]
fn without_a_worker_the_sealing_write_flushes_after_it_commits() {
    let dir = TempDir::new().unwrap();
    let listener = Arc::new(PipelineFreeDuringFlush::default());
    let engine = RegolithEngine::open(
        dir.path(),
        EngineOptions {
            listeners: vec![listener.clone()],
            ..tiny(0)
        },
    )
    .unwrap();
    let _ = listener.engine.set(Arc::downgrade(&engine));
    for round in 0..3 {
        write_until_sealed(&engine, &format!("r{round}-"));
        assert!(
            engine.view.load().frozen.is_empty(),
            "the sealing write returned with its memtable still frozen"
        );
    }
    let free = listener.free.lock().unwrap().clone();
    assert!(free.len() >= 3, "{free:?}");
    assert!(
        free.iter().all(|&free| free),
        "a flush ran while the commit pipeline was held: {free:?}"
    );
}

/// RED FlushAnyOrder: frozen memtables install in L0 in the order they were
/// sealed, whoever flushes them and however many flush at once, so a read
/// never goes back from a newer version to an older one.
#[test]
fn frozen_memtables_install_in_l0_oldest_first_whoever_flushes() {
    let dir = TempDir::new().unwrap();
    // No cap, so the memtables stay frozen while this test holds the flush
    // exclusion, and the worker waits on it.
    let engine = RegolithEngine::open(
        dir.path(),
        EngineOptions {
            max_write_buffer_number: 0,
            ..tiny(1)
        },
    )
    .unwrap();
    const ROUNDS: u8 = 6;
    {
        let _held = engine.flusher.flushing.lock();
        // Each round seals a memtable holding `k = round`.
        for round in 0..ROUNDS {
            put(&engine, b"k", &[round]).unwrap();
            write_until_sealed(&engine, &format!("fill{round}-"));
        }
        assert_eq!(engine.view.load().frozen.len(), ROUNDS as usize);
    }

    // The worker and three more threads flush at once, and a reader checks
    // that every answer is at least the last one it saw.
    std::thread::scope(|scope| {
        let reader = scope.spawn(|| {
            let mut seen = 0u8;
            loop {
                let draining = !engine.view.load().frozen.is_empty();
                let value = engine.get(&key_of(b"k"), u64::MAX).unwrap().unwrap();
                assert!(
                    value[0] >= seen,
                    "a read went back from {seen} to {}",
                    value[0]
                );
                seen = value[0];
                if !draining {
                    break;
                }
            }
        });
        for _ in 0..3 {
            scope.spawn(|| engine.flusher.flush_all_frozen());
        }
        reader.join().unwrap();
    });
    assert!(engine.view.load().frozen.is_empty());
    assert_eq!(
        engine.get(&key_of(b"k"), u64::MAX).unwrap(),
        Some(vec![ROUNDS - 1]),
        "the newest version answers once every memtable is in L0"
    );
}

/// A rotation leaves at most `max_write_buffer_number` memtables: when the
/// flush before it has not finished, the write that fills the next memtable
/// writes the oldest out itself, and waits for the flush exclusion to do so.
#[test]
fn a_rotation_never_leaves_more_memtables_than_the_cap() {
    let dir = TempDir::new().unwrap();
    // The default cap of two: the active memtable and one frozen.
    let engine = RegolithEngine::open(dir.path(), tiny(1)).unwrap();
    let held = engine.flusher.flushing.lock();
    write_until_sealed(&engine, "first");
    assert_eq!(engine.view.load().frozen.len(), 1);
    let (done, returned) = mpsc::channel();
    std::thread::scope(|scope| {
        scope.spawn(|| {
            done.send(write_until_sealed(&engine, "second")).unwrap();
        });
        // The worker cannot flush while the exclusion is held, so the
        // second rotation has to wait to write the first memtable out.
        assert!(
            returned.recv_timeout(Duration::from_millis(200)).is_err(),
            "a second rotation sealed past the cap while the first flush was pending"
        );
        assert!(engine.view.load().frozen.len() <= 1);
        drop(held);
        returned
            .recv_timeout(Duration::from_secs(30))
            .expect("the rotation finished once the exclusion was free");
    });
    assert!(engine.view.load().frozen.len() <= 1);
    assert_eq!(
        engine.get(&key_of(b"first000"), u64::MAX).unwrap(),
        Some(vec![7u8; 1024])
    );
}

/// E16: with no worker, the write after the flush that brings L0 to
/// `l0_compaction_trigger` compacts it, so L0 stays at the trigger instead of
/// growing to the slowdown trigger before anything compacts.
#[test]
fn without_a_worker_writes_compact_once_l0_reaches_its_trigger() {
    let dir = TempDir::new().unwrap();
    let engine = RegolithEngine::open(
        dir.path(),
        EngineOptions {
            l0_compaction_trigger: 2,
            level0_slowdown_writes_trigger: 20,
            level0_stop_writes_trigger: 36,
            ..tiny(0)
        },
    )
    .unwrap();
    let mut peak_l0 = 0;
    for round in 0..12 {
        write_until_sealed(&engine, &format!("r{round:02}-"));
        peak_l0 = peak_l0.max(engine.view.load().version.levels[0].len());
    }
    assert!(
        peak_l0 <= 2,
        "L0 reached {peak_l0} tables with a trigger of 2: nothing compacted"
    );
    assert!(
        !engine.view.load().version.levels[1].is_empty(),
        "nothing was compacted into L1"
    );
    for round in 0..12 {
        assert_eq!(
            engine
                .get(&key_of(format!("r{round:02}-000").as_bytes()), u64::MAX)
                .unwrap(),
            Some(vec![7u8; 1024])
        );
    }
}
