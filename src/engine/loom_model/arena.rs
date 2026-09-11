//! Model of invariant A8: at most one thread is ever inside
//! [`super::super::arena::Arena::alloc`] at a time.
//!
//! `alloc` no longer takes a lock: its chunk list is a
//! `crate::sync::UnsafeCell` instead, checked by loom under `--cfg loom`
//! and a plain `std::cell::UnsafeCell` otherwise. This is the
//! calibration that shows loom actually sees the state a `Mutex` used to
//! protect, by racing two allocations with nothing serializing them.

use loom::sync::Arc;

use super::super::arena::{Arena, ArenaProfile, ChunkPool};
use super::explore;

/// One chunk large enough to hold both threads' allocations, so the race
/// under test is the concurrent creation of the arena's first chunk, not
/// a second growth competing with it.
const BUDGET: usize = 4096;

/// A8: two unserialized `alloc` calls must never both touch `state`.
///
/// In a debug build the guard `alloc` carries trips first, before either
/// thread reaches the chunk list, so the panic names the arena's own
/// contract (A8) rather than loom's cell tracker. In a release build the
/// guard is compiled out, so this is what shows loom's tracked cell
/// actually catches the unordered writes the removed `Mutex` used to
/// prevent: without the guard, the two threads race a chunk push and a
/// cursor reset on the same `ArenaState`, and loom's causality check
/// reports the concurrent write. `tests/loom_memtable.rs` runs both
/// expectations, gated by `debug_assertions`, on the profile that proves
/// each.
pub fn two_unserialized_allocations_race_the_arena() {
    explore(
        "two_unserialized_allocations_race_the_arena",
        2,
        1,
        |witness| {
            let profile = ArenaProfile::EMBEDDED;
            let pool = Arc::new(ChunkPool::new(profile, BUDGET, 2));
            let arena = Arc::new(Arena::new(pool, BUDGET, profile));
            witness.record();

            let writers: Vec<_> = (0..2)
                .map(|_| {
                    let arena = Arc::clone(&arena);
                    loom::thread::spawn(move || {
                        arena
                            .alloc(64, 8)
                            .expect("the budget holds two allocations");
                    })
                })
                .collect();

            for writer in writers {
                if let Err(payload) = writer.join() {
                    std::panic::resume_unwind(payload);
                }
            }
        },
    );
}
