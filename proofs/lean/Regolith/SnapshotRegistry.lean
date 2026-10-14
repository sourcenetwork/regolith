/-!
# SnapshotRegistry: lock-free registration by announce, sample, confirm

This file backs the TLA+ model `proofs/tla/SnapshotRegistry.tla`,
invariants `MinBelowLive` and `LiveCovered` (configurations
`MC_SnapshotRegistry_*`).

A reader registers a snapshot without a lock. It announces: it reads the
horizon `v` and publishes `v` in its slot. It samples: it reads the horizon
again. It confirms: if the horizon is still `v`, the snapshot is live at
`v`; otherwise it announces the new value and samples again. A compaction
samples the horizon `c`, then reads the slot; its list is what it saw, and
the minimum it may use is the least of `c` and the list.

TLC checks every interleaving of a few readers. Here the argument is made
for any interleaving at once, by naming the moment of each access: a
moment is a natural number, and `H t` is the horizon at moment `t`, which
only rises. Nothing is assumed about how far apart the moments are, nor
about any other reader.

What is proved, in plain words:

1. `scan_respects_live`: for a reader live at `v` while the compaction
   uses its minimum, the minimum is at most `v`, and `v` is in the list or
   at or above `c`. The second is what stripes need
   (`StripeCompaction.tla`): a stripe ends at every live snapshot, or the
   snapshot reads the top stripe of inputs fixed before `c` was sampled.
2. `no_confirm_breaks_min`: a reader that goes live at the value it
   announced, without the confirming sample, can sit below the minimum.
   This is the RED configuration `MC_SnapshotRegistry_Red_NoConfirm`.

Memory ordering is sequentially consistent here: each access happens at
one moment. The loads and stores need SeqCst, which loom checks.
-/

namespace Regolith.SnapshotRegistry

/-- `Rises H`: the horizon never goes down. -/
def Rises (H : Nat → Nat) : Prop := ∀ i j, i ≤ j → H i ≤ H j

/-- One registration, by the moments of its accesses, and the slot's
contents over time.

* `slot t` is what the slot holds at moment `t`: `none` when empty.
* The final announce stores `v` at `tS`; the slot holds `v` from then
  until the release at `tRel`.
* Before `tS` the slot was empty or held an earlier announce's value,
  which was read from the horizon before `v` was, so it is at most `v`.
* The confirming sample at `tC`, after `tS`, read the horizon and found
  `v`: from then the snapshot is live at `v`. -/
structure Registration (H : Nat → Nat) where
  /-- What the slot holds at each moment. -/
  slot : Nat → Option Nat
  /-- The value of the final announce: the snapshot's sequence. -/
  v : Nat
  /-- When the final announce stored `v`. -/
  tS : Nat
  /-- When the confirming sample read the horizon. -/
  tC : Nat
  /-- When the snapshot was released and the slot emptied. -/
  tRel : Nat
  /-- The confirming sample came after the store. -/
  store_before_confirm : tS < tC
  /-- It found the horizon still at `v`. -/
  confirmed : H tC = v
  /-- From the store until the release the slot holds `v`. -/
  holds : ∀ t, tS ≤ t → t < tRel → slot t = some v
  /-- Before the store it was empty or held a value no larger than `v`. -/
  before : ∀ t, t < tS → slot t = none ∨ ∃ w, slot t = some w ∧ w ≤ v

/-- One compaction's view of one slot: it sampled the horizon at `tA`, then
read the slot at `tB`. -/
structure Scan where
  /-- When the compaction sampled the horizon. -/
  tA : Nat
  /-- When it read this slot. -/
  tB : Nat
  /-- The sample came first. -/
  sample_first : tA < tB

/-- The minimum the compaction may use, as far as this slot decides it:
the least of its sampled horizon and what it saw in the slot. -/
def minimum (H : Nat → Nat) (reg : Registration H) (sc : Scan) : Nat :=
  match reg.slot sc.tB with
  | some w => min (H sc.tA) w
  | none => H sc.tA

/-- **`scan_respects_live`.** Let the compaction use its minimum at some
moment `tU` after its scan read the slot, and before the snapshot is
released. Then the minimum is at most `v`, and the scan saw `v` or the
sampled horizon is at most `v`. Whether the snapshot became live before
`tU` or after does not matter: the bound holds either way. -/
theorem scan_respects_live {H : Nat → Nat}
    -- The horizon only rises.
    (hH : Rises H) (reg : Registration H) (sc : Scan) (tU : Nat)
    -- The snapshot is not yet released at `tU` ...
    (hlive : tU < reg.tRel)
    -- ... and the compaction uses its minimum at `tU`, after its scan.
    (huse : sc.tB ≤ tU) :
    minimum H reg sc ≤ reg.v ∧ (reg.slot sc.tB = some reg.v ∨ H sc.tA ≤ reg.v) := by
  have hcs := reg.store_before_confirm
  by_cases hB : reg.tS ≤ sc.tB
  · -- The scan read the slot after the final store: it saw `v`.
    have hslot := reg.holds sc.tB hB (by omega)
    refine ⟨?_, Or.inl hslot⟩
    simp only [minimum, hslot]
    exact Nat.min_le_right _ _
  · -- The scan read it before the final store, so the sample came before
    -- the confirm, which read `v`: the sample is at most `v`.
    have hc : H sc.tA ≤ reg.v := by
      rw [← reg.confirmed]
      exact hH _ _ (by have := sc.sample_first; omega)
    refine ⟨?_, Or.inr hc⟩
    unfold minimum
    split
    · exact Nat.le_trans (Nat.min_le_left _ _) hc
    · exact hc

/-! ## The RED case: going live without the confirm -/

/-- The horizon in the counterexample: 0 at moment 0, then 1. -/
def redH (t : Nat) : Nat := if 1 ≤ t then 1 else 0

/-- The reader's slot in the counterexample: empty until it stores, at
moment 3, the value 0 it read at moment 0. -/
def redSlot (t : Nat) : Option Nat := if 3 ≤ t then some 0 else none

/-- **`no_confirm_breaks_min`.** The reader reads the horizon 0 at moment 0;
the horizon rises to 1 at moment 1; the compaction samples 1 at moment 1
and reads the still-empty slot at moment 2; the reader stores 0 at moment 3
and, without a confirming sample, is live at 0. The compaction's minimum
is 1, above the snapshot. With the confirm, every later sample reads 1,
not 0, so the reader re-announces instead. -/
theorem no_confirm_breaks_min :
    Rises redH ∧ redH 0 = 0 ∧ redSlot 2 = none ∧ redSlot 3 = some 0 ∧
    redH 1 = 1 ∧ 0 < redH 1 ∧ (∀ t, 3 < t → redH t ≠ 0) := by
  refine ⟨?_, by decide, by decide, by decide, by decide, by decide, ?_⟩
  · -- `redH` is 0 then 1: it never goes down.
    intro i j hij
    unfold redH
    split <;> split <;> omega
  · -- After moment 3 the horizon is 1.
    intro t ht
    unfold redH
    split <;> omega

end Regolith.SnapshotRegistry
