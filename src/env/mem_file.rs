//! A file held in memory that readers read without any lock: the contents
//! behind [`super::MemEnv`] and the OPFS mirror.
//!
//! # Shape
//!
//! A file is one *extent* at a time, published through a [`kovan::Atom`]:
//! a buffer with spare capacity and one state word holding the published
//! length and two flags.
//!
//! - **Bytes below the published length never change.** A reader loads the
//!   extent, loads the length (Acquire), and copies from below it, with no
//!   lock and no retry, while writers work above it or on a new extent.
//! - **An append in place.** A write at the end that fits the spare capacity
//!   sets `WRITER` with one CAS, copies its bytes above the length, and
//!   publishes the new length with a second CAS that clears the flag. The
//!   bytes it copies are above every published length, so no reader can be
//!   reading them.
//! - **Everything else copies.** An overwrite below the length, a shrink, or
//!   an append past the capacity builds a new extent from the published
//!   bytes, *freezes* the old one (a CAS that sets `FROZEN`, after which no
//!   append can publish there), and swaps the new one in with a CAS on the
//!   `Atom`. An append whose publishing CAS meets `FROZEN` lost the race and
//!   writes again, on the new extent. The copy reads only below the length
//!   it froze, never the bytes a concurrent appender may be writing.
//!
//! Every write is lock-free (a failed CAS means another write landed), and a
//! read is wait-free. A read sees every write that finished before it began:
//! a finished append published its length on the extent every later load
//! returns, or on one a later copy copied from; a finished copy is the extent
//! every later load returns. `proofs/tla/EnvFiles.tla` models this protocol,
//! and the shared file cursor positional reads replace.

#![allow(unsafe_code)]

use std::cell::UnsafeCell;
use std::io;

use kovan::{Atom, AtomGuard};

use crate::portability::{AtomicU64, Ordering};

/// The published length.
const LEN: u64 = (1 << 62) - 1;
/// An append in place holds the spare capacity.
const WRITER: u64 = 1 << 62;
/// A copy replaced or is replacing this extent: nothing more publishes here.
const FROZEN: u64 = 1 << 63;

/// The smallest buffer a file grows into, so a file of a few small appends
/// does not reallocate on each.
const MIN_CAPACITY: usize = 64;

/// What a write costs the memory it is charged to, if anything: the OPFS
/// mirror bounds its resident bytes, `MemEnv` charges nothing.
pub(crate) trait Charge {
    /// Reserve `bytes` more before a write makes them visible. An error
    /// refuses the write, which then changes nothing.
    fn reserve(&self, bytes: u64) -> io::Result<()>;
    /// Give back `bytes`: a reservation whose attempt lost a race, or a
    /// file that shrank.
    fn release(&self, bytes: u64);
}

/// Charges nothing.
pub(crate) struct Free;

impl Charge for Free {
    fn reserve(&self, _bytes: u64) -> io::Result<()> {
        Ok(())
    }

    fn release(&self, _bytes: u64) {}
}

/// The same allocation, as cells a shared reference may write through.
fn cells(bytes: Box<[u8]>) -> Box<[UnsafeCell<u8>]> {
    // SAFETY: `UnsafeCell<u8>` is `repr(transparent)` over `u8`, so the
    // slice has the same layout, and the box keeps its allocation.
    unsafe { Box::from_raw(Box::into_raw(bytes) as *mut [UnsafeCell<u8>]) }
}

/// One buffer and its published length.
struct Extent {
    bytes: Box<[UnsafeCell<u8>]>,
    state: AtomicU64,
}

// SAFETY: bytes below the published length are never written while the
// extent can be reached (only read), and bytes at or above it are written
// only by the one thread holding `WRITER`, which no reader reads: a reader
// copies only below a length it loaded with Acquire, which the writer's
// publishing CAS (Release) made visible after the bytes.
unsafe impl Sync for Extent {}

impl Extent {
    fn with_capacity(capacity: usize) -> io::Result<Self> {
        let mut bytes = Vec::new();
        bytes.try_reserve_exact(capacity).map_err(|_| {
            io::Error::new(
                io::ErrorKind::OutOfMemory,
                format!("cannot hold a {capacity} byte file in memory"),
            )
        })?;
        bytes.resize(capacity, 0);
        Ok(Self {
            bytes: cells(bytes.into_boxed_slice()),
            state: AtomicU64::new(0),
        })
    }

    fn capacity(&self) -> usize {
        self.bytes.len()
    }

    fn base(&self) -> *mut u8 {
        UnsafeCell::raw_get(self.bytes.as_ptr())
    }

    /// Copy `out.len()` published bytes starting at `at`.
    ///
    /// # Safety
    ///
    /// `at + out.len()` is at most a length this thread loaded from `state`
    /// with Acquire ordering.
    unsafe fn copy_out(&self, at: usize, out: &mut [u8]) {
        // SAFETY: the range is published, so nothing writes it (see the
        // `Sync` impl), and it lies within the buffer.
        unsafe { std::ptr::copy_nonoverlapping(self.base().add(at), out.as_mut_ptr(), out.len()) }
    }

    /// Copy `src` into the buffer at `at`.
    ///
    /// # Safety
    ///
    /// The range is at or above every length published on this extent and
    /// this thread holds `WRITER`, or the extent is not yet published.
    unsafe fn copy_in(&self, at: usize, src: &[u8]) {
        // SAFETY: the caller owns the range exclusively, and it lies within
        // the buffer.
        unsafe { std::ptr::copy_nonoverlapping(src.as_ptr(), self.base().add(at), src.len()) }
    }

    /// Zero `n` bytes at `at`.
    ///
    /// # Safety
    ///
    /// As [`Self::copy_in`].
    unsafe fn zero(&self, at: usize, n: usize) {
        // SAFETY: as `copy_in`.
        unsafe { std::ptr::write_bytes(self.base().add(at), 0, n) }
    }

    /// Copy the first `n` bytes of `src` to the start of this extent.
    ///
    /// # Safety
    ///
    /// `n` is at most a length loaded from `src.state` with Acquire, and this
    /// extent is not yet published.
    unsafe fn copy_prefix(&self, src: &Extent, n: usize) {
        // SAFETY: the source range is published and never written; the
        // destination is this thread's alone. Two allocations, no overlap.
        unsafe { std::ptr::copy_nonoverlapping(src.base(), self.base(), n) }
    }
}

/// What a write does to the file.
enum Change<'a> {
    /// Append these slices at the end, wherever the end is when it lands.
    Append(&'a [&'a [u8]]),
    /// Write these bytes at `at`, extending the file with zeros to reach it.
    /// Only the OPFS mirror writes at an offset.
    #[cfg(any(test, all(target_arch = "wasm32", target_os = "unknown")))]
    At(u64, &'a [u8]),
    /// Make the file this long, cutting it or extending it with zeros.
    SetLen(u64),
}

impl Change<'_> {
    /// Where the write starts and the length after it, for a file now `len`.
    fn bounds(&self, len: u64) -> io::Result<(u64, u64)> {
        let (at, end) = match self {
            Change::Append(slices) => {
                let n: u64 = slices.iter().map(|s| s.len() as u64).sum();
                (len, len.checked_add(n))
            }
            #[cfg(any(test, all(target_arch = "wasm32", target_os = "unknown")))]
            Change::At(at, buf) => (*at, at.checked_add(buf.len() as u64).map(|e| e.max(len))),
            Change::SetLen(new) => (len.min(*new), Some(*new)),
        };
        match end {
            Some(end) if end <= LEN => Ok((at, end)),
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "the write would make the file too large to address",
            )),
        }
    }

    /// Write this change's bytes into `extent`, starting at `at`.
    ///
    /// # Safety
    ///
    /// The caller owns `[at, to)` of `extent` exclusively (see
    /// [`Extent::copy_in`]).
    unsafe fn fill(&self, extent: &Extent, at: usize) {
        match self {
            Change::Append(slices) => {
                let mut at = at;
                for slice in slices.iter() {
                    // SAFETY: forwarded from the caller.
                    unsafe { extent.copy_in(at, slice) };
                    at += slice.len();
                }
            }
            // SAFETY: forwarded from the caller.
            #[cfg(any(test, all(target_arch = "wasm32", target_os = "unknown")))]
            Change::At(_, buf) => unsafe { extent.copy_in(at, buf) },
            // A new extent is zeroed; an extension in place zeroes below.
            Change::SetLen(_) => {}
        }
    }
}

/// A file held in memory, read without any lock. See the module docs.
pub(crate) struct MemFile {
    current: Atom<Extent>,
}

fn to_usize(n: u64) -> io::Result<usize> {
    usize::try_from(n).map_err(|_| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "offset is too large to address",
        )
    })
}

impl MemFile {
    /// An empty file.
    pub(crate) fn new() -> Self {
        Self {
            current: Atom::new(Extent {
                bytes: Box::new([]),
                state: AtomicU64::new(0),
            }),
        }
    }

    /// A file holding `bytes`.
    #[cfg(any(test, all(target_arch = "wasm32", target_os = "unknown")))]
    pub(crate) fn from_vec(bytes: Vec<u8>) -> Self {
        let len = bytes.len() as u64;
        Self {
            current: Atom::new(Extent {
                bytes: cells(bytes.into_boxed_slice()),
                state: AtomicU64::new(len),
            }),
        }
    }

    /// The file's length now.
    pub(crate) fn len(&self) -> u64 {
        self.current.load().state.load(Ordering::Acquire) & LEN
    }

    /// Copy the bytes at `offset` into `buf`, as many as the file holds
    /// there, and return how many. Never blocks.
    #[cfg(any(test, all(target_arch = "wasm32", target_os = "unknown")))]
    pub(crate) fn read_at(&self, offset: u64, buf: &mut [u8]) -> usize {
        let extent = self.current.load();
        let len = extent.state.load(Ordering::Acquire) & LEN;
        if offset >= len {
            return 0;
        }
        // Below `len`, which fits the buffer, so fits `usize`.
        let n = buf.len().min((len - offset) as usize);
        // SAFETY: `offset + n <= len`, loaded above with Acquire.
        unsafe { extent.copy_out(offset as usize, &mut buf[..n]) };
        n
    }

    /// Fill `buf` from `offset`, or fail with `UnexpectedEof` when the file
    /// is shorter.
    pub(crate) fn read_exact_at(&self, offset: u64, buf: &mut [u8]) -> io::Result<()> {
        let end = offset
            .checked_add(buf.len() as u64)
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "read range overflows"))?;
        let extent = self.current.load();
        let len = extent.state.load(Ordering::Acquire) & LEN;
        if end > len {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "failed to fill whole buffer",
            ));
        }
        // SAFETY: `end <= len`, loaded above with Acquire.
        unsafe { extent.copy_out(to_usize(offset)?, buf) };
        Ok(())
    }

    /// The whole file, as one copy.
    #[cfg(any(test, all(target_arch = "wasm32", target_os = "unknown")))]
    pub(crate) fn to_vec(&self) -> Vec<u8> {
        let extent = self.current.load();
        let len = (extent.state.load(Ordering::Acquire) & LEN) as usize;
        let mut out = vec![0u8; len];
        // SAFETY: `len` loaded above with Acquire.
        unsafe { extent.copy_out(0, &mut out) };
        out
    }

    /// Append `slices` at the end. Returns the length before and after.
    pub(crate) fn append(&self, slices: &[&[u8]], charge: &dyn Charge) -> io::Result<(u64, u64)> {
        self.change(&Change::Append(slices), charge)
    }

    /// Write `buf` at `at`. Returns the length before and after.
    #[cfg(any(test, all(target_arch = "wasm32", target_os = "unknown")))]
    pub(crate) fn write_at(
        &self,
        at: u64,
        buf: &[u8],
        charge: &dyn Charge,
    ) -> io::Result<(u64, u64)> {
        self.change(&Change::At(at, buf), charge)
    }

    /// Cut or zero-extend the file to `len`. Returns the length before and
    /// after.
    pub(crate) fn set_len(&self, len: u64, charge: &dyn Charge) -> io::Result<(u64, u64)> {
        self.change(&Change::SetLen(len), charge)
    }

    fn change(&self, change: &Change<'_>, charge: &dyn Charge) -> io::Result<(u64, u64)> {
        loop {
            let extent = self.current.load();
            let state = settled(&extent);
            let len = state & LEN;
            let (at, end) = change.bounds(len)?;
            let grow = end.saturating_sub(len);
            charge.reserve(grow)?;
            let landed = if state & (WRITER | FROZEN) == 0
                && at == len
                && end >= len
                && to_usize(end)? <= extent.capacity()
            {
                self.in_place(&extent, state, change, len, end)
            } else {
                self.copy(&extent, state, change, at, len, end)?
            };
            if landed {
                if end < len {
                    charge.release(len - end);
                }
                return Ok((len, end));
            }
            charge.release(grow);
        }
    }

    /// Append at the end of `extent`, within its capacity. `false` when
    /// another write got there first.
    fn in_place(
        &self,
        extent: &AtomGuard<'_, Extent>,
        state: u64,
        change: &Change<'_>,
        len: u64,
        end: u64,
    ) -> bool {
        if extent
            .state
            .compare_exchange(state, state | WRITER, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            return false;
        }
        let (from, to) = (len as usize, end as usize);
        if let Change::SetLen(_) = change {
            // Bytes above the length may hold a lost attempt's bytes.
            // SAFETY: `WRITER` is held and the range is above the length.
            unsafe { extent.zero(from, to - from) };
        }
        // SAFETY: `WRITER` is held, and `[from, to)` is above every length
        // published on this extent.
        unsafe { change.fill(extent, from) };
        #[cfg(test)]
        if let Some(hook) = BETWEEN_WRITE_AND_PUBLISH.with(|slot| slot.borrow_mut().take()) {
            hook();
        }
        // Release: the bytes are visible to every reader that loads this
        // length. Fails only when a copy froze the extent meanwhile.
        extent
            .state
            .compare_exchange(state | WRITER, end, Ordering::Release, Ordering::Relaxed)
            .is_ok()
    }

    /// Build a new extent holding the file after `change`, freeze `extent`,
    /// and swap the new one in. `Ok(false)` when another write got there
    /// first.
    fn copy(
        &self,
        extent: &AtomGuard<'_, Extent>,
        state: u64,
        change: &Change<'_>,
        at: u64,
        len: u64,
        end: u64,
    ) -> io::Result<bool> {
        // Grows by doubling only when the bytes need more room; a copy for an
        // overwrite or a lost race keeps the capacity it had.
        let need = to_usize(end)?;
        let capacity = if need <= extent.capacity() {
            extent.capacity()
        } else {
            need.max(extent.capacity().saturating_mul(2))
                .max(MIN_CAPACITY)
        };
        let fresh = Extent::with_capacity(capacity)?;
        let kept = len.min(end) as usize;
        // SAFETY: `kept <= len`, loaded with Acquire by the caller; `fresh`
        // is not published, so this thread owns all of it.
        unsafe {
            fresh.copy_prefix(extent, kept);
            change.fill(&fresh, at as usize);
        }
        fresh.state.store(end, Ordering::Relaxed);
        #[cfg(test)]
        if let Some(hook) = BETWEEN_BUILD_AND_FREEZE.with(|slot| slot.borrow_mut().take()) {
            hook();
        }
        // Freeze: from here no append publishes on the old extent, so the
        // bytes copied above are all it will ever hold. A frozen extent
        // stays frozen; only the swap below decides.
        if state & FROZEN == 0
            && extent
                .state
                .compare_exchange(state, state | FROZEN, Ordering::AcqRel, Ordering::Relaxed)
                .is_err()
        {
            return Ok(false);
        }
        Ok(self.current.compare_and_swap(extent, fresh).is_ok())
    }
}

/// How many times an append looks again at an extent another append is
/// writing in place before it copies instead. Only an optimization: a copy
/// is always correct, and costs a whole file.
const SETTLE_SPINS: u32 = 64;

/// The extent's state, looked at again a few times while another append
/// holds `WRITER`, so a short race ends in place rather than in a copy.
/// Never waits beyond the bound: what it returns may still hold `WRITER`.
fn settled(extent: &Extent) -> u64 {
    let mut state = extent.state.load(Ordering::Acquire);
    for _ in 0..SETTLE_SPINS {
        if state & WRITER == 0 || state & FROZEN != 0 {
            break;
        }
        std::hint::spin_loop();
        state = extent.state.load(Ordering::Acquire);
    }
    state
}

impl Default for MemFile {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
thread_local! {
    /// Runs once, on this thread, inside the next copy, after it built its
    /// new extent and before it freezes the old one: the window where
    /// another write may publish or freeze.
    static BETWEEN_BUILD_AND_FREEZE: std::cell::RefCell<Option<Box<dyn FnOnce()>>> =
        const { std::cell::RefCell::new(None) };
}

/// Run `hook` inside this thread's next copy, between its build and its
/// freeze.
#[cfg(test)]
fn between_build_and_freeze(hook: impl FnOnce() + 'static) {
    BETWEEN_BUILD_AND_FREEZE.with(|slot| *slot.borrow_mut() = Some(Box::new(hook)));
}

#[cfg(test)]
thread_local! {
    /// Runs once, on this thread, inside the next append in place, after it
    /// wrote its bytes and before its publishing CAS: the window where a
    /// copy may freeze the extent.
    static BETWEEN_WRITE_AND_PUBLISH: std::cell::RefCell<Option<Box<dyn FnOnce()>>> =
        const { std::cell::RefCell::new(None) };
}

/// Run `hook` inside this thread's next append in place, between its write
/// and its publish.
#[cfg(test)]
fn between_write_and_publish(hook: impl FnOnce() + 'static) {
    BETWEEN_WRITE_AND_PUBLISH.with(|slot| *slot.borrow_mut() = Some(Box::new(hook)));
}

#[cfg(test)]
mod tests;
