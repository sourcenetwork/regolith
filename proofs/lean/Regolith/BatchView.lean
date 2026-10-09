import Regolith.LsmOrder

/-!
# BatchView: a batch read resolves every key against one view (E6)

This file backs the TLA+ model `proofs/tla/BatchRead.tla`, invariants
`BatchConsistent` and `BatchExact` (configurations `MC_BatchRead_Green`,
`MC_BatchRead_Red_ViewPerKey` and `MC_BatchRead_Red_ViewPerKey_Exact`).

The defect: a batch read of several keys (`multi_get`) at one snapshot
sequence that loads a fresh view for each key. The batch registers no
snapshot, so a flush (or a compaction) between two keys may write out only
the newest version of a key and drop the older one the batch's snapshot
needs. A key resolved against the new view then reads absent or older.

What is proved, in plain words:

1. `batch_one_view_point_in_time`: a batch resolved against the view it
   captured at its start answers every key exactly as it would have at the
   start, whatever writes landed in that view meanwhile.
2. `batch_one_view_newest` and `batch_one_view_absent`: each of those
   answers is the newest version of its key the snapshot may see in the
   captured view, or absent when there is none.
3. `view_per_key_breaks_batch`: a batch that loads a view per key, with a
   flush between two keys, answers a key absent although the captured view
   holds a version the snapshot may see. This is the RED configuration as
   a concrete counterexample.

The read order and `read_newest` come from `LsmOrder.lean`.
-/

namespace Regolith.BatchView

open Regolith.LsmOrder

/-- A view: the sources a read walks, in read order (the memtable, the L0
files newest first, the deeper levels), captured at one moment. The engine's
view holds the memtable it captured by reference, so a write made after the
capture lands in the view's first source. Such a write always takes a
sequence newer than any snapshot sampled before it. -/
abbrev View := List Source

/-- A batch read of `keys` at snapshot `snap`, resolved against the one view
`v`. Each key is returned with its answer. -/
def batchOneView (v : View) (keys : List Nat) (snap : Nat) : List (Nat × Option Nat) :=
  keys.map fun k => (k, read v k snap)

/-- A batch read that loads a view per key: key number `i` is resolved
against `views[i]`, whatever view was current when its turn came. -/
def batchPerKey (views : List View) (keys : List Nat) (snap : Nat) : List (Nat × Option Nat) :=
  List.zipWith (fun v k => (k, read v k snap)) views keys

/-- Writes after the capture only add versions newer than the snapshot to
the view's memtable, so the view answers every read at the snapshot as it
did at the capture. -/
theorem read_grow_invisible {mem extra : Source} {rest : List Source} {k snap : Nat}
    -- Every later write is newer than the snapshot.
    (hnew : ∀ e ∈ extra, snap < e.2) :
    read ((extra ++ mem) :: rest) k snap = read (mem :: rest) k snap := by
  -- The memtable's answer is unchanged (`newestIn_append_invisible`), and
  -- the rest of the view is untouched.
  simp only [Regolith.LsmOrder.read, newestIn_append_invisible hnew]

/-- **E6, point in time.** A batch resolved against the view it captured,
`mem :: rest`, after writes `extra` landed in that view's memtable, answers
every key as the captured view did at the start. -/
theorem batch_one_view_point_in_time {mem extra : Source} {rest : List Source}
    {keys : List Nat} {snap : Nat}
    -- Every write after the capture is newer than the snapshot.
    (hnew : ∀ e ∈ extra, snap < e.2) :
    batchOneView ((extra ++ mem) :: rest) keys snap = batchOneView (mem :: rest) keys snap := by
  unfold batchOneView
  -- Key by key, the read is unchanged.
  congr 1
  funext k
  rw [read_grow_invisible hnew]

/-- **E6, every answer is the newest.** In the batch of
`batch_one_view_point_in_time`, every key answered `some v` is answered with
the newest version of that key the snapshot may see in the captured view,
provided the captured view is ordered. -/
theorem batch_one_view_newest {mem extra : Source} {rest : List Source}
    {keys : List Nat} {snap : Nat}
    -- The captured view is ordered: each source newer than the ones after it.
    (hord : Ordered (mem :: rest))
    -- Every write after the capture is newer than the snapshot.
    (hnew : ∀ e ∈ extra, snap < e.2) :
    ∀ p ∈ batchOneView ((extra ++ mem) :: rest) keys snap, ∀ v,
      p.2 = some v → IsNewest (mem :: rest) p.1 snap v := by
  rw [batch_one_view_point_in_time hnew]
  intro p hp v hv
  -- `p` is `(k, read (mem :: rest) k snap)` for some key `k` of the batch.
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hp
  exact read_some_newest hord hv

/-- **E6, every absent answer is right.** In the same batch, a key
answered absent has no version the snapshot may see in the captured view. -/
theorem batch_one_view_absent {mem extra : Source} {rest : List Source}
    {keys : List Nat} {snap : Nat}
    -- Every write after the capture is newer than the snapshot.
    (hnew : ∀ e ∈ extra, snap < e.2) :
    ∀ p ∈ batchOneView ((extra ++ mem) :: rest) keys snap,
      p.2 = none → ∀ s, Holds (mem :: rest) (p.1, s) → snap < s := by
  rw [batch_one_view_point_in_time hnew]
  intro p hp hnone
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hp
  exact read_eq_none.mp hnone

/-- `flushNewest mem` is what a flush writes when no registered snapshot
needs an older version: for each key, only its newest version in `mem`. A
version survives when no version of the same key in `mem` is newer. -/
def flushNewest (mem : Source) : Source :=
  mem.filter fun e => mem.all fun e' => e'.1 != e.1 || decide (e'.2 ≤ e.2)

/-- A flush of view `v`: a new, empty memtable, and the old memtable's
newest versions as the newest L0 file. The deeper sources are unchanged. -/
def flushDrop : View → View
  | [] => []
  | mem :: rest => [] :: flushNewest mem :: rest

/-- The memtable of the counterexample's captured view, after one write
that landed in it after the capture: key 1 at sequence 1, key 2 at
sequence 1, and key 2 at sequence 3 (the later write). The snapshot is 1. -/
def capturedMem : Source := [(2, 3), (2, 1), (1, 1)]

/-- The counterexample's captured view: that memtable and nothing older. -/
def captured : View := [capturedMem, []]

/-- **`view_per_key_breaks_batch`.** The batch reads keys 1 and 2 at
snapshot 1. Between the two keys a flush writes the memtable out keeping
only the newest version of each key, which drops key 2's version at 1.

* One view for the batch answers both keys from the captured view: key 1
  and key 2 both at sequence 1.
* One view per key resolves key 2 against the flushed view, where its only
  version is at 3, too new for the snapshot. It answers key 2 absent,
  although the batch's snapshot holds it at sequence 1. -/
theorem view_per_key_breaks_batch :
    batchOneView captured [1, 2] 1 = [(1, some 1), (2, some 1)] ∧
    batchPerKey [captured, flushDrop captured] [1, 2] 1 = [(1, some 1), (2, none)] := by
  -- Both sides are concrete; Lean evaluates them.
  decide

end Regolith.BatchView
