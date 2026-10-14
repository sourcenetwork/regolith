import Regolith.LsmOrder

/-!
# Publication: the visible sequence never passes a pending slot (E8)

This file backs the TLA+ model `proofs/tla/IngestPublication.tla`,
invariant `RepeatableSnapshot` (configurations
`MC_IngestPublication_Green`, `MC_IngestPublication_Red_IngestPublishesEarly`
and `MC_IngestPublication_Red_CommitPassesSlot`).

Commits and an ingest draw their sequences from one shared counter. A
reader takes a snapshot at the published horizon, the visible sequence. If
the horizon ever moves past a sequence whose data is not installed yet (the
ingest's table, still being written), a snapshot taken then reads a key as
absent, and the same snapshot reads it as present once the table lands.

What is proved, in plain words:

1. `step_inv` and `reachable_inv`: the fixed protocol keeps every pending
   slot above the horizon. That is its invariant.
2. `repeatable_snapshot`: under the fixed protocol, a snapshot taken at any
   moment reads every key the same at every later moment, whatever commits,
   ingests and publications happen in between.
3. `early_publication_breaks_snapshots`: when the horizon may pass a
   pending slot, a snapshot reads a key absent and later present. This is
   the RED configuration as a concrete counterexample, and the fixed
   protocol refuses the publication that causes it
   (`fixed_protocol_refuses_early_publication`).

Reads use `newestIn` from `LsmOrder.lean`. Over an ordered LSM tree a read
returns the newest visible version across all sources (`read_newest`), so a
single list of installed versions stands for all of them here.
-/

namespace Regolith.Publication

open Regolith.LsmOrder

/-- The state the publication protocol works on. -/
structure Pub where
  /-- The next sequence the shared counter hands out. -/
  next : Nat
  /-- The pending slots: sequences a commit or an ingest has drawn whose
  data is not installed yet. -/
  pending : List Nat
  /-- Every installed version `(key, sequence)`: what the memtables, the
  levels and the ingested tables hold. -/
  installed : Source
  /-- The published read horizon: a snapshot taken now reads at this
  sequence (`ReadHorizon::visible` in the engine). -/
  visible : Nat

/-- The protocol's invariant. -/
structure Inv (p : Pub) : Prop where
  /-- Every pending slot is above the horizon: the horizon never passed a
  sequence whose data is missing. -/
  pending_above : ∀ s ∈ p.pending, p.visible < s
  /-- The horizon is below the next sequence to be handed out, so a slot
  drawn next is above it. -/
  visible_below_next : p.visible < p.next

/-- The start: nothing drawn, nothing installed, horizon 0, and the first
sequence to hand out is 1. -/
def init : Pub := ⟨1, [], [], 0⟩

/-- The fixed protocol's steps. -/
inductive Step : Pub → Pub → Prop
  /-- A commit or an ingest draws the next sequence from the shared
  counter. It is a pending slot until its data is installed. -/
  | draw (p : Pub) :
      Step p { p with next := p.next + 1, pending := p.next :: p.pending }
  /-- The writer holding pending slot `s` installs its versions, every one
  at sequence `s`: a commit's memtable inserts, or an ingest's table. The
  slot stops being pending. -/
  | install (p : Pub) (s : Nat) (keys : List Nat)
      -- `s` is a pending slot.
      (hs : s ∈ p.pending) :
      Step p { p with pending := p.pending.erase s,
                      installed := keys.map (fun k => (k, s)) ++ p.installed }
  /-- The horizon is raised to `s`, never lowered (a `fetch_max`). The fix:
  only when no pending slot is at or below `s`. -/
  | publish (p : Pub) (s : Nat)
      -- `s` was handed out.
      (hs : s < p.next)
      -- No pending slot is at or below `s`.
      (hgap : ∀ t ∈ p.pending, s < t) :
      Step p { p with visible := max p.visible s }

/-- Any number of steps, one after another. -/
inductive Steps : Pub → Pub → Prop
  /-- No step at all. -/
  | refl (p : Pub) : Steps p p
  /-- Some steps, then one more. -/
  | tail {p q r : Pub} : Steps p q → Step q r → Steps p r

/-- The start satisfies the invariant. -/
theorem init_inv : Inv init :=
  -- No pending slot; and `0 < 1`.
  ⟨fun _ h => absurd h List.not_mem_nil, by decide⟩

/-- **Every step keeps the invariant.** -/
theorem step_inv {p q : Pub}
    -- The invariant holds before the step.
    (hinv : Inv p)
    -- One step of the fixed protocol.
    (hstep : Step p q) :
    Inv q := by
  obtain ⟨habove, hnext⟩ := hinv
  cases hstep with
  | draw =>
    -- The new slot is `next`, above the horizon; the old ones still are.
    refine ⟨?_, by simp only; omega⟩
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hm
    · exact hnext
    · exact habove s hm
  | install s keys hs =>
    -- The pending slots only shrink.
    exact ⟨fun t ht => habove t (List.mem_of_mem_erase ht), hnext⟩
  | publish s hs hgap =>
    -- The new horizon `max visible s` is below every pending slot, since
    -- both `visible` and `s` are, and below `next`, since both are.
    refine ⟨?_, by simp only; omega⟩
    intro t ht
    have h1 := habove t ht
    have h2 := hgap t ht
    simp only
    omega

/-- The horizon never moves backwards. -/
theorem step_visible_mono {p q : Pub} (hstep : Step p q) : p.visible ≤ q.visible := by
  -- A draw and an install leave it; a publication takes a `max` with it.
  cases hstep <;> simp only <;> omega

/-- **A step changes no read at or below the horizon.** For every
sequence `snap` at or below the horizon before the step, every key reads
the same at `snap` before and after the step. -/
theorem step_reads {p q : Pub}
    -- The invariant holds before the step.
    (hinv : Inv p)
    -- One step of the fixed protocol.
    (hstep : Step p q)
    {snap : Nat}
    -- The snapshot is at or below the horizon.
    (hsnap : snap ≤ p.visible) (k : Nat) :
    newestIn q.installed k snap = newestIn p.installed k snap := by
  cases hstep with
  -- A draw and a publication install nothing: the reads are unchanged.
  | draw => rfl
  | publish => rfl
  | install s keys hs =>
    -- The installed versions are all at `s`, a pending slot, which is
    -- above the horizon and so above the snapshot: invisible to it.
    simp only
    apply newestIn_append_invisible
    intro e he
    obtain ⟨k', -, rfl⟩ := List.mem_map.mp he
    have := hinv.pending_above s hs
    simp only
    omega

/-- Several steps keep the invariant, never lower the horizon, and change
no read at or below the horizon at the start. -/
theorem steps_reads {p q : Pub}
    -- The invariant holds at the start.
    (hinv : Inv p)
    -- Any number of steps of the fixed protocol.
    (hsteps : Steps p q) :
    Inv q ∧ p.visible ≤ q.visible ∧
      ∀ snap ≤ p.visible, ∀ k, newestIn q.installed k snap = newestIn p.installed k snap := by
  induction hsteps with
  -- No step: nothing changed.
  | refl => exact ⟨hinv, Nat.le_refl _, fun _ _ _ => rfl⟩
  | tail _ hstep ih =>
    -- The steps so far, then one more.
    obtain ⟨hinvq, hvis, hreads⟩ := ih
    refine ⟨step_inv hinvq hstep, Nat.le_trans hvis (step_visible_mono hstep), ?_⟩
    intro snap hsnap k
    -- The snapshot is also at or below the later horizon, so the last step
    -- changes nothing it reads either.
    rw [step_reads hinvq hstep (Nat.le_trans hsnap hvis) k]
    exact hreads snap hsnap k

/-- Every state the fixed protocol reaches satisfies the invariant. -/
theorem reachable_inv {q : Pub} (hreach : Steps init q) : Inv q :=
  (steps_reads init_inv hreach).1

/-- **E8, repeatable snapshots.** Take a snapshot at the horizon of any
reachable state `p`. After any further steps of the fixed protocol, every
key reads at that snapshot exactly what it read when the snapshot was
taken. -/
theorem repeatable_snapshot {p q : Pub}
    -- `p` is reachable from the start.
    (hreach : Steps init p)
    -- `q` follows `p` by any number of steps.
    (hlater : Steps p q) (k : Nat) :
    newestIn q.installed k p.visible = newestIn p.installed k p.visible :=
  (steps_reads (reachable_inv hreach) hlater).2.2 p.visible (Nat.le_refl _) k

/-! ## The RED case: the horizon passes a pending slot -/

/-- The defective protocol: the same steps, except that publication may
raise the horizon past a pending slot. That is what happens when the
ingest publishes its sequence before its table is installed, and also when
a commit that drew a later sequence publishes it with `fetch_max` while the
ingest's slot is still pending. -/
inductive StepEarly : Pub → Pub → Prop
  /-- As `Step.draw`. -/
  | draw (p : Pub) :
      StepEarly p { p with next := p.next + 1, pending := p.next :: p.pending }
  /-- As `Step.install`. -/
  | install (p : Pub) (s : Nat) (keys : List Nat) (hs : s ∈ p.pending) :
      StepEarly p { p with pending := p.pending.erase s,
                           installed := keys.map (fun k => (k, s)) ++ p.installed }
  /-- The defect: no check against the pending slots. -/
  | publish (p : Pub) (s : Nat) (hs : s < p.next) :
      StepEarly p { p with visible := max p.visible s }

/-- The ingest has drawn sequence 1; nothing is installed. -/
def drawn : Pub := ⟨2, [1], [], 0⟩

/-- The horizon was raised to 1 while slot 1 is pending. A snapshot taken
here reads at 1. -/
def publishedEarly : Pub := ⟨2, [1], [], 1⟩

/-- The ingest's table lands: key 7 at sequence 1. -/
def landed : Pub := ⟨2, [], [(7, 1)], 1⟩

/-- **`early_publication_breaks_snapshots`.** The defective protocol
reaches `publishedEarly` from the start, where a snapshot at 1 reads key 7
as absent. One more step installs the ingest's table, and the same
snapshot reads key 7 at sequence 1. -/
theorem early_publication_breaks_snapshots :
    StepEarly init drawn ∧ StepEarly drawn publishedEarly ∧ StepEarly publishedEarly landed ∧
    newestIn publishedEarly.installed 7 publishedEarly.visible = none ∧
    newestIn landed.installed 7 publishedEarly.visible = some 1 := by
  refine ⟨StepEarly.draw init, StepEarly.publish drawn 1 (by decide),
    StepEarly.install publishedEarly 1 [7] (by decide), by decide, by decide⟩

/-- The fixed protocol refuses that publication: from `drawn` no step
leads to `publishedEarly`, because slot 1 is pending. -/
theorem fixed_protocol_refuses_early_publication : ¬ Step drawn publishedEarly := by
  intro h
  -- Name the target state, so each kind of step can be compared with it.
  generalize hq : publishedEarly = q at h
  cases h with
  | draw =>
    -- A draw moves `next` from 2 to 3; the target keeps 2.
    simp [publishedEarly, drawn] at hq
  | install s keys hs =>
    -- An install leaves the horizon at 0; the target's is 1.
    simp [publishedEarly, drawn] at hq
  | publish s hs hgap =>
    -- The guard requires `s < 1` for the pending slot 1, so `s = 0`, and
    -- the horizon would stay at `max 0 0 = 0`, not 1.
    have h1 := hgap 1 List.mem_cons_self
    simp [publishedEarly, drawn] at hq h1
    omega

end Regolith.Publication
