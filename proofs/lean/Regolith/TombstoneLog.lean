/-!
# TombstoneLog: readers see a whole prefix of a memtable's range deletes

This file backs the TLA+ model `proofs/tla/TombstoneLog.tla`, invariants
`PrefixWhole` and `PublishedSeen` (configurations `MC_TombstoneLog_*`).

## The story

A memtable keeps its range tombstones in an append-only log
(`src/engine/memtable/tombstones.rs`). The one writer, the commit leader,
appends a tombstone in three steps: it writes the tombstone into slot
`len`, then publishes the length `len + 1`, then publishes the commit's read
horizon. A reader samples the horizon, reads the length, and reads only the
slots below that length.

Tiny example: the leader writes tombstone 0 into slot 0, publishes length
1, then horizon 1. A reader that samples horizon 1 reads a length of at
least 1 and finds slot 0 written.

## What is proved, for any number of appends and readers

1. `writer_inv_reachable`: in every state the writer reaches, every slot
   below the published length is written, and the horizon never passes the
   length.
2. `prefix_whole`: a reader that read the length at one moment and a slot
   below it at a later moment finds the slot written: what it reads is a
   whole prefix of the appends (`PrefixWhole`).
3. `published_seen`: a reader that sampled the horizon and later read the
   length read a length at least that horizon, so it reads every tombstone
   its snapshot includes (`PublishedSeen`).
4. The RED cases as counterexamples: publishing the length before writing
   the slot (`len_first_breaks`) and the horizon before the length
   (`horizon_first_breaks`).
-/

namespace Regolith.TombstoneLog

/-- Where the writer is inside one append, in the real order. -/
inductive Phase where
  /-- Next: write the tombstone into slot `len`. -/
  | write
  /-- Next: publish the length `len + 1`. -/
  | publish
  /-- Next: publish the horizon (the commit becomes visible). -/
  | commit
  deriving DecidableEq

/-- The writer's state. -/
structure Writer where
  /-- `written i`: slot `i` holds its tombstone. -/
  written : Nat → Bool
  /-- The published length (`TombstoneLog::len`). -/
  len : Nat
  /-- The published read horizon: appends whose commit is visible. -/
  horizon : Nat
  /-- The writer's next step. -/
  phase : Phase

/-- The start: nothing written or published. -/
def start : Writer := ⟨fun _ => false, 0, 0, .write⟩

/-- The writer's steps, in the real order. -/
inductive Step : Writer → Writer → Prop where
  /-- Write the tombstone into the next slot, `len`. -/
  | write (w : Writer) (h : w.phase = .write) :
      Step w { w with written := fun i => if i = w.len then true else w.written i,
                      phase := .publish }
  /-- Publish the length: the slot just written joins the prefix. -/
  | publish (w : Writer) (h : w.phase = .publish) :
      Step w { w with len := w.len + 1, phase := .commit }
  /-- Publish the horizon: the commit is visible, the append is done. -/
  | commit (w : Writer) (h : w.phase = .commit) :
      Step w { w with horizon := w.len, phase := .write }

/-- The writer states reachable from the start. -/
inductive Reachable : Writer → Prop where
  /-- The start is reachable. -/
  | start : Reachable start
  /-- One step from a reachable state reaches another. -/
  | step {w v : Writer} : Reachable w → Step w v → Reachable v

/-- What the writer keeps true. -/
structure Inv (w : Writer) : Prop where
  /-- Every slot below the published length is written. -/
  prefix_written : ∀ i, i < w.len → w.written i = true
  /-- During a publish step the slot about to join is already written. -/
  next_written : w.phase = .publish → w.written w.len = true
  /-- The horizon never passes the length. -/
  horizon_le : w.horizon ≤ w.len

/-- The invariant holds at the start. -/
theorem inv_start : Inv start := by
  -- Nothing is published: every field holds trivially.
  constructor <;> simp [start]

/-- Every step keeps the invariant. -/
theorem inv_step {w v : Writer} (hi : Inv w) (hs : Step w v) : Inv v := by
  -- One case per step.
  cases hs with
  | write h =>
    -- Prove the three fields after the write.
    constructor
    -- Slots below `len` were written and stay written; slot `len` is new.
    · intro i hi'
      -- Read the new state's fields as the old state's.
      dsimp only at hi' ⊢
      by_cases hil : i = w.len
      · -- `i = len` is not below `len`: impossible.
        omega
      · -- Another slot keeps its old bit, written because it is below.
        simp [hil]; exact hi.prefix_written i hi'
    -- The slot that will join next is `len`, just written.
    · intro _
      -- The new bit at `len` is true by the step's own definition.
      simp
    -- Neither the length nor the horizon moved.
    · exact hi.horizon_le
  | publish h =>
    -- Prove the three fields after the publish.
    constructor
    -- The new prefix is the old one plus slot `len`, written before.
    · intro i hi'
      -- Read the new state's fields as the old state's.
      dsimp only at hi' ⊢
      by_cases hil : i = w.len
      · -- Slot `len`: written before the publish (the write came first).
        subst hil; exact hi.next_written h
      · -- A slot below the old length: written already.
        exact hi.prefix_written i (by omega)
    -- The next step is a commit, not a publish: nothing to show.
    · intro hp
      simp at hp
    -- The length grew; the horizon did not.
    · dsimp only; have := hi.horizon_le; omega
  | commit h =>
    -- Prove the three fields after the commit.
    constructor
    -- Nothing written or published changes.
    · exact hi.prefix_written
    -- The next step is a write, not a publish: nothing to show.
    · intro hp
      simp at hp
    -- The horizon catches up with the length, no further.
    · dsimp only; omega

/-- **The writer's half, for every reachable state.** Every slot below the
published length is written, and the horizon never passes the length. -/
theorem writer_inv_reachable {w : Writer} (h : Reachable w) :
    (∀ i, i < w.len → w.written i = true) ∧ w.horizon ≤ w.len := by
  -- Induction on how the state was reached ...
  have hi : Inv w := by
    induction h with
    | start =>
      -- The start satisfies it.
      exact inv_start
    | step _ hs ih =>
      -- One more step keeps it.
      exact inv_step ih hs
  -- ... then read off the two fields.
  exact ⟨hi.prefix_written, hi.horizon_le⟩

/-! ## The reader's half, by moments

A reader's loads happen at moments; `W t`, `L t` and `H t` are the writer's
written slots, length and horizon at moment `t`. The writer's steps only
ever write slots, raise the length and raise the horizon; the theorems
below assume exactly that, plus the writer invariant at every moment. -/

/-- What the writer's history gives a reader, at every moment. -/
structure History where
  /-- Which slots are written at each moment. -/
  W : Nat → Nat → Bool
  /-- The published length at each moment. -/
  L : Nat → Nat
  /-- The published horizon at each moment. -/
  H : Nat → Nat
  /-- A written slot stays written. -/
  written_stays : ∀ t t' i, t ≤ t' → W t i = true → W t' i = true
  /-- The length only rises. -/
  len_rises : ∀ t t', t ≤ t' → L t ≤ L t'
  /-- At every moment the prefix is written (`writer_inv_reachable`). -/
  prefix_written : ∀ t i, i < L t → W t i = true
  /-- At every moment the horizon is within the length. -/
  horizon_le : ∀ t, H t ≤ L t

/-- **`PrefixWhole`.** A reader that read the length at `t0` and slot `i`
below it at a later moment `t1` finds the slot written. -/
theorem prefix_whole (h : History) {t0 t1 i : Nat} (hlen : i < h.L t0) (hlater : t0 ≤ t1) :
    h.W t1 i = true := by
  -- Written by `t0`, since it was in the prefix then, and still written.
  exact h.written_stays t0 t1 i hlater (h.prefix_written t0 i hlen)

/-- **`PublishedSeen`.** A reader that sampled the horizon at `t0` and read
the length at a later moment `t1` read a length at least the horizon it
sampled: it reads every tombstone its snapshot includes. -/
theorem published_seen (h : History) {t0 t1 : Nat} (hlater : t0 ≤ t1) :
    h.H t0 ≤ h.L t1 := by
  -- The horizon was within the length at `t0`, and the length only rose.
  exact Nat.le_trans (h.horizon_le t0) (h.len_rises t0 t1 hlater)

/-! ## The RED cases, as counterexamples -/

/-- **LenFirst.** Publishing the length before writing the slot reaches a
state with length 1 and slot 0 unwritten: a reader reading slot 0 then sees
an append before its contents. -/
theorem len_first_breaks :
    let w : Writer := { start with len := 1 }
    0 < w.len ∧ w.written 0 = false := by
  -- Evaluate.
  decide

/-- **HorizonFirst.** Publishing the horizon before the length reaches a
state with horizon 1 and length 0: a reader that samples horizon 1 and then
reads the length reads 0, missing the tombstone its snapshot includes. -/
theorem horizon_first_breaks :
    let w : Writer := { start with written := fun i => i = 0, horizon := 1 }
    w.len < w.horizon := by
  -- Evaluate.
  decide

end Regolith.TombstoneLog
