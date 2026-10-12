//! The allocations a thread keeps between commits, so that a commit
//! allocates nothing for the pipeline's own objects.
//!
//! A commit needs a descriptor in the ring and a decision in the chain, and a
//! sync round needs the round and its job. Each is shared between threads
//! through an `Arc`, so each would be one allocation a commit, and the write
//! path had none of them before the pipeline. Instead, when the last
//! reference to one of them turns out to be this thread's, the thread moves
//! the value out and keeps the allocation, a *shell*, and its next commit
//! fills the shell instead of allocating. One thread committing on its own
//! reuses the same few allocations for ever; under contention a thread that
//! finds no shell allocates, as it would have.
//!
//! # Invariants
//!
//! - **S1, a shell has one owner.** It is made only from an `Arc` that
//!   [`Arc::get_mut`] says is unique: no other strong reference and no weak
//!   one. Nobody else can reach the allocation, then or later.
//! - **S2, a shell holds no value.** The value was moved out when the shell
//!   was made, and the allocation is typed `MaybeUninit` from then on, so it
//!   is never read or dropped as a value again and pins nothing: no log, no
//!   memtable, no key.
//! - **S3, a thread keeps one shell of each kind.** A second one is freed, so
//!   what a thread holds back is bounded by four small allocations.
//!
//! A loom build keeps no shell: its `Arc` is the model's, and what is reused
//! here is memory, not a protocol.

#![allow(unsafe_code)]

use super::super::io::job::{Job, JobBody};
use super::descriptor::{Decision, Descriptor, Work};
use super::round::Round;
use crate::sync::internal::Arc as RingArc;

#[cfg(not(loom))]
mod shell {
    use std::mem::MaybeUninit;
    use std::ptr;
    use std::sync::Arc;

    /// The allocation of an `Arc<T>` whose value was moved out (S1, S2).
    pub(super) struct Shell<T>(Arc<MaybeUninit<T>>);

    impl<T> Shell<T> {
        /// Move the value out of `arc` and keep its allocation, when `arc`
        /// is the last reference; otherwise hand `arc` back.
        pub(super) fn take(mut arc: Arc<T>) -> Result<(Self, T), Arc<T>> {
            if Arc::get_mut(&mut arc).is_none() {
                return Err(arc);
            }
            let raw = Arc::into_raw(arc);
            // SAFETY (S1): `get_mut` said this is the only reference, strong
            // or weak, so no other thread reads the value, and it is moved
            // out exactly once, here.
            let value = unsafe { ptr::read(raw) };
            // SAFETY (S2): `raw` came from `Arc::into_raw` just above, and
            // `MaybeUninit<T>` has the size and alignment of `T`, which is
            // what `Arc::from_raw` asks for when the type changes. The
            // allocation is only seen as uninitialized from here on, so the
            // value moved out above is never dropped a second time.
            let shell = unsafe { Arc::from_raw(raw.cast::<MaybeUninit<T>>()) };
            Ok((Self(shell), value))
        }

        /// Put `value` in the allocation and hand it out as an `Arc<T>`.
        pub(super) fn fill(self, value: T) -> Arc<T> {
            let mut arc = self.0;
            match Arc::get_mut(&mut arc) {
                Some(slot) => {
                    slot.write(value);
                    // SAFETY: the value was written on the line above.
                    unsafe { arc.assume_init() }
                }
                // S1 makes this unreachable; a new allocation is always
                // right.
                None => Arc::new(value),
            }
        }
    }
}

#[cfg(not(loom))]
mod kept {
    use std::cell::Cell;
    use std::sync::Arc;
    use std::thread::LocalKey;

    use super::shell::Shell;
    use super::{Decision, Descriptor, Job, Round};

    /// Where a thread keeps its shell of one kind (S3).
    pub(super) type Slot<T> = Cell<Option<Shell<T>>>;

    std::thread_local! {
        pub(super) static DESCRIPTOR: Slot<Descriptor> = const { Cell::new(None) };
        pub(super) static DECISION: Slot<Decision> = const { Cell::new(None) };
        pub(super) static ROUND: Slot<Round> = const { Cell::new(None) };
        pub(super) static JOB: Slot<Job> = const { Cell::new(None) };
    }

    /// `value` in this thread's shell, or in a new allocation when the
    /// thread has none (or is past the end of its thread-local storage).
    pub(super) fn make<T>(slot: &'static LocalKey<Slot<T>>, value: T) -> Arc<T> {
        match slot.try_with(Cell::take) {
            Ok(Some(shell)) => shell.fill(value),
            _ => Arc::new(value),
        }
    }

    /// Keep the allocation of `arc` for this thread's next value of the
    /// kind, when `arc` is the last reference, and hand back the value it
    /// held. `None` when it is still shared: it is then only let go of.
    pub(super) fn keep<T>(slot: &'static LocalKey<Slot<T>>, arc: Arc<T>) -> Option<T> {
        let (shell, value) = Shell::take(arc).ok()?;
        // S3: a shell already there is freed by the `set`.
        let _ = slot.try_with(|slot| slot.set(Some(shell)));
        Some(value)
    }
}

/// A descriptor for `work`, in a kept allocation when this thread has one.
pub(super) fn descriptor(work: Work) -> RingArc<Descriptor> {
    let desc = Descriptor::new(work);
    #[cfg(not(loom))]
    {
        kept::make(&kept::DESCRIPTOR, desc)
    }
    #[cfg(loom)]
    {
        RingArc::new(desc)
    }
}

/// Let go of `desc`, a commit's descriptor its owner is done with, keeping
/// its allocation when nobody else holds it.
pub(super) fn keep_descriptor(desc: RingArc<Descriptor>) {
    #[cfg(not(loom))]
    drop(kept::keep(&kept::DESCRIPTOR, desc));
    #[cfg(loom)]
    drop(desc);
}

/// `decision` as the chain holds it, in a kept allocation when this thread
/// has one.
pub(super) fn decision(decision: Decision) -> RingArc<Decision> {
    #[cfg(not(loom))]
    {
        kept::make(&kept::DECISION, decision)
    }
    #[cfg(loom)]
    {
        RingArc::new(decision)
    }
}

/// Let go of `decision`: one that lost its install, or that the tip moved
/// past. Its allocation is kept when nobody else holds it.
pub(super) fn keep_decision(decision: RingArc<Decision>) {
    #[cfg(not(loom))]
    drop(kept::keep(&kept::DECISION, decision));
    #[cfg(loom)]
    drop(decision);
}

/// A round whose job runs `body`, both in kept allocations when this thread
/// has them.
pub(super) fn round(body: Box<dyn JobBody>) -> RingArc<Round> {
    #[cfg(not(loom))]
    {
        let job = kept::make(&kept::JOB, Job::fresh(body));
        kept::make(&kept::ROUND, Round::fresh(job))
    }
    #[cfg(loom)]
    {
        RingArc::new(Round::fresh(Job::new(body)))
    }
}

/// Let go of `round`, one that was run and replaced, keeping its allocation
/// and its job's when nobody else holds them.
pub(super) fn keep_round(round: RingArc<Round>) {
    #[cfg(not(loom))]
    if let Some(round) = kept::keep(&kept::ROUND, round) {
        drop(kept::keep(&kept::JOB, round.into_job()));
    }
    #[cfg(loom)]
    drop(round);
}

#[cfg(all(test, not(loom)))]
mod tests {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    use super::shell::Shell;

    /// Counts its drops.
    struct Counted(Arc<AtomicUsize>, u64);

    impl Drop for Counted {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }

    #[test]
    fn a_shared_value_is_handed_back_untouched() {
        let drops = Arc::new(AtomicUsize::new(0));
        let arc = Arc::new(Counted(Arc::clone(&drops), 7));
        let other = Arc::clone(&arc);
        let Err(back) = Shell::take(arc) else {
            panic!("a shared value was taken");
        };
        assert_eq!(back.1, 7);
        assert_eq!(drops.load(Ordering::SeqCst), 0);
        drop(back);
        drop(other);
        assert_eq!(drops.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn a_weak_reference_keeps_a_value_from_being_taken() {
        let arc = Arc::new(5u64);
        let weak = Arc::downgrade(&arc);
        assert!(Shell::take(arc).is_err());
        assert!(weak.upgrade().is_none());
    }

    #[test]
    fn the_last_reference_gives_its_value_once_and_its_allocation_again() {
        let drops = Arc::new(AtomicUsize::new(0));
        let arc = Arc::new(Counted(Arc::clone(&drops), 1));
        let address = Arc::as_ptr(&arc) as usize;
        let Ok((shell, value)) = Shell::take(arc) else {
            panic!("the last reference was not taken");
        };
        assert_eq!(value.1, 1);
        assert_eq!(drops.load(Ordering::SeqCst), 0, "moved out, not dropped");
        drop(value);
        assert_eq!(drops.load(Ordering::SeqCst), 1);

        let again = shell.fill(Counted(Arc::clone(&drops), 2));
        assert_eq!(again.1, 2);
        assert_eq!(Arc::as_ptr(&again) as usize, address, "the same allocation");
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        drop(again);
        assert_eq!(drops.load(Ordering::SeqCst), 2, "each value dropped once");
    }

    #[test]
    fn a_shell_let_go_drops_no_value() {
        let drops = Arc::new(AtomicUsize::new(0));
        let arc = Arc::new(Counted(Arc::clone(&drops), 1));
        let Ok((shell, value)) = Shell::take(arc) else {
            panic!("the last reference was not taken");
        };
        drop(shell);
        assert_eq!(drops.load(Ordering::SeqCst), 0, "a shell holds no value");
        drop(value);
        assert_eq!(drops.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn a_thread_keeps_one_shell_and_uses_it_for_its_next_value() {
        use std::cell::Cell;

        std::thread_local! {
            static SLOT: super::kept::Slot<u64> = const { Cell::new(None) };
        }
        let first = super::kept::make(&SLOT, 1);
        let second = super::kept::make(&SLOT, 2);
        let kept_address = Arc::as_ptr(&second) as usize;
        assert_eq!(super::kept::keep(&SLOT, first), Some(1));
        // S3: the second shell takes the first one's place.
        assert_eq!(super::kept::keep(&SLOT, second), Some(2));
        let third = super::kept::make(&SLOT, 3);
        assert_eq!(*third, 3);
        assert_eq!(Arc::as_ptr(&third) as usize, kept_address);
        let fourth = super::kept::make(&SLOT, 4);
        assert_ne!(Arc::as_ptr(&fourth) as usize, kept_address, "no shell left");

        let shared = Arc::clone(&third);
        assert_eq!(super::kept::keep(&SLOT, third), None, "still shared");
        assert_eq!(*shared, 3);
    }
}
