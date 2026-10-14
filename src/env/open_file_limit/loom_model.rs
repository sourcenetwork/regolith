//! Loom models of the open-file slot table: acquire, evict and release.
//!
//! ```text
//! RUSTFLAGS="--cfg loom" cargo test --release --test loom_tables
//! ```
//!
//! Each model drives the production [`SlotTable`], whose state words, owner
//! words and descriptor cells come from `crate::sync::internal` and so are
//! loom's under `--cfg loom`. The descriptor is a [`ModelFile`] that knows
//! when it is being read and fails the model if it is closed (dropped) then,
//! or read after. What each proves:
//!
//! - **Never above the limit**: every model counts the descriptors alive at
//!   once and fails above the capacity.
//! - **Never closed in use**: a reader inside a read and a claimer evicting
//!   the same slot race; the claim waits for the read or takes another slot.
//! - **A reader reads its own file**: a reader joining from a stale hint
//!   races the slot being reloaded for another file; it reads its own bytes
//!   or misses, never the other file's.
//! - **A starved reader drains**: with one slot held by a reader, a second
//!   file's open waits for that read and then takes the slot.
//!
//! Each is paired with a calibration that plants one step wrong
//! ([`Mutant`]) and must fail.

use std::io;
use std::sync::Arc as StdArc;

use loom::sync::Arc;
use loom::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use loom::thread;

use super::slots::{Mutant, SlotTable};
use crate::engine::loom_model::{Witness, explore};
use crate::env::ReadFile;

/// What every file of one model run shares: how many are open right now.
struct Device {
    open: AtomicUsize,
    capacity: usize,
}

/// A descriptor for file `id`: a read fills the buffer with `id`, and the
/// file fails the model if it is closed during a read or read after a close.
struct ModelFile {
    id: u8,
    device: Arc<Device>,
    reading: AtomicUsize,
    closed: AtomicBool,
}

impl ModelFile {
    fn open(id: u8, device: &Arc<Device>) -> io::Result<StdArc<dyn ReadFile>> {
        let now = device.open.fetch_add(1, Ordering::SeqCst) + 1;
        assert!(
            now <= device.capacity,
            "{now} descriptors open, over the capacity {}",
            device.capacity
        );
        Ok(StdArc::new(Self {
            id,
            device: Arc::clone(device),
            reading: AtomicUsize::new(0),
            closed: AtomicBool::new(false),
        }))
    }
}

impl ReadFile for ModelFile {
    fn read_exact_at(&self, _offset: u64, buf: &mut [u8]) -> io::Result<()> {
        self.reading.fetch_add(1, Ordering::SeqCst);
        assert!(!self.closed.load(Ordering::SeqCst), "read a closed file");
        buf.fill(self.id);
        assert!(
            !self.closed.load(Ordering::SeqCst),
            "a file was closed in use"
        );
        self.reading.fetch_sub(1, Ordering::SeqCst);
        Ok(())
    }

    fn len(&self) -> io::Result<u64> {
        Ok(1)
    }
}

impl Drop for ModelFile {
    fn drop(&mut self) {
        assert_eq!(
            self.reading.load(Ordering::SeqCst),
            0,
            "a file was closed in use"
        );
        self.closed.store(true, Ordering::SeqCst);
        self.device.open.fetch_sub(1, Ordering::SeqCst);
    }
}

/// Read file `owner`'s byte through `table`: join the hinted slot, or load
/// a slot. Returns the byte read.
fn read(table: &SlotTable, device: &Arc<Device>, owner: u64, hint: usize) -> u8 {
    let held = match table.join(hint, owner) {
        Some(held) => held,
        None => table
            .load(owner, || ModelFile::open(owner as u8, device))
            .expect("model opens never fail"),
    };
    let mut byte = [0u8; 1];
    held.file().read_exact_at(0, &mut byte).expect("model read");
    byte[0]
}

fn setup(capacity: usize, mutant: Mutant) -> (Arc<SlotTable>, Arc<Device>) {
    (
        Arc::new(SlotTable::with_mutant(capacity, mutant)),
        Arc::new(Device {
            open: AtomicUsize::new(0),
            capacity,
        }),
    )
}

/// One slot; file 1 is loaded and read again from its hint while file 2's
/// load evicts it. Each reads its own byte, at most one descriptor is open,
/// and none is closed in use.
fn acquire_evict_release(mutant: Mutant, witness: &Witness) {
    let (table, device) = setup(1, mutant);
    // File 1 is in slot 0, idle.
    assert_eq!(read(&table, &device, 1, usize::MAX), 1);
    let first = {
        let (table, device) = (Arc::clone(&table), Arc::clone(&device));
        thread::spawn(move || read(&table, &device, 1, 0))
    };
    let second = {
        let (table, device) = (Arc::clone(&table), Arc::clone(&device));
        thread::spawn(move || read(&table, &device, 2, 0))
    };
    let (one, two) = (
        first.join().expect("reader 1"),
        second.join().expect("reader 2"),
    );
    assert_eq!(one, 1, "file 1's reader read file {one}");
    assert_eq!(two, 2, "file 2's reader read file {two}");
    assert!(table.open_count() <= 1);
    // The interesting schedules: file 1's second read missed its hint
    // because file 2 took the slot.
    if table.join(0, 2).is_some() {
        witness.record();
    }
}

/// Two files share one slot: loads, evictions and hinted joins race. Every
/// read returns its own file, the bound holds, nothing is closed in use.
pub fn a_slot_is_never_closed_in_use_and_never_over_the_limit() {
    explore(
        "a_slot_is_never_closed_in_use_and_never_over_the_limit",
        20,
        1,
        |witness| acquire_evict_release(Mutant::None, witness),
    );
}

/// File 1 holds the only slot mid-read; file 2's open drains it: it waits
/// for that one read and then takes the slot.
pub fn a_starved_open_drains_a_busy_slot() {
    explore("a_starved_open_drains_a_busy_slot", 10, 1, |witness| {
        let (table, device) = setup(1, Mutant::None);
        let held = table
            .load(1, || ModelFile::open(1, &device))
            .expect("model open");
        let opener = {
            let (table, device) = (Arc::clone(&table), Arc::clone(&device));
            thread::spawn(move || read(&table, &device, 2, usize::MAX))
        };
        let mut byte = [0u8; 1];
        held.file().read_exact_at(0, &mut byte).expect("model read");
        assert_eq!(byte[0], 1);
        drop(held);
        assert_eq!(opener.join().expect("opener"), 2);
        assert!(table.open_count() <= 1);
        witness.record();
    });
}

/// Calibration: a claim that takes an open slot whatever its readers closes
/// a file a reader is using. Must fail.
pub fn calibration_an_eviction_that_ignores_readers_closes_a_file_in_use() {
    explore(
        "calibration_an_eviction_that_ignores_readers_closes_a_file_in_use",
        1,
        0,
        |witness| acquire_evict_release(Mutant::IgnoreReaders, witness),
    );
}

/// Calibration: a join that trusts the owner it saw before its CAS reads
/// another file when the slot is reloaded in between. Must fail.
pub fn calibration_a_join_without_the_owner_recheck_reads_another_file() {
    explore(
        "calibration_a_join_without_the_owner_recheck_reads_another_file",
        1,
        0,
        |witness| acquire_evict_release(Mutant::NoOwnerRecheck, witness),
    );
}
