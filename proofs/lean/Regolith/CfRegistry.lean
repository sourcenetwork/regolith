/-!
# CfRegistry: a column family's writes land only while it lives

This file backs the TLA+ model `proofs/tla/CfRegistry.tla`. TLC checks the
protocol there for two writers and one family. Here the same rules are
proved for every number of families, writers and steps.

## The story, for a reader who has never seen the code

A column family is a named keyspace inside one database; its keys carry the
family's id in front. Every write takes a sequence number, one after the
other, in the commit pipeline's "ordered step". Dropping a family writes one
range tombstone at some sequence `t`: it deletes every key of the family
written at a sequence below `t`.

Tiny example of the bug this rules out. Writer W checks that family 5 is
live, then goes to commit. A drop of family 5 commits first, its tombstone
at sequence 7. If W's write then takes sequence 8, it lands above the
tombstone: visible in a family nobody can name any more, and never removed.

The code (`src/engine/commit/families.rs`) checks the family again inside
the ordered step, right before the write takes its sequence, and the drop
retires the family inside the ordered step too, right after its tombstone.
In this file each of those is one atomic step, because the ordered step is
one thread at a time.

## What is proved, in plain words

1. `no_write_after_drop`: every write that landed in a dropped family has a
   sequence below the tombstone, so the tombstone deletes it (TLA+
   `NoWriteAfterDrop`).
2. `no_write_before_birth`: every write that landed is above its family's
   creation (TLA+ `NoWriteBeforeBirth`).
3. `life_in_order`: a family's stage only moves forward, unborn, live,
   dead, so whatever a reader sees, it sees in that order (TLA+
   `LifeInOrder`).
4. The RED cases, as counterexamples: a fence outside the ordered step lets
   a write land after the tombstone (`fence_outside_lands_after_drop`); a
   retire after the ordered step does too (`late_retire_lands_after_drop`);
   reusing a dropped id brings a family back to life
   (`reused_id_goes_back`).
5. Group commit: a whole group, its members checked when the group runs,
   is a run of the steps above (`runGroup_steps`), so the rules hold after
   any group however its members were admitted
   (`group_no_write_after_drop`, `group_no_write_before_birth`). The ticket
   the hand-off holds across a drop is refused when its group runs
   (`fenced_when_run_refuses_after_drop`); checked at the hand-off instead,
   or a transaction left unchecked, it lands over the tombstone
   (`fenced_at_hand_off_lands_after_drop`, TLA+ REDs `FenceAtHandOff` and
   `TxnUnfenced`).

## How to read the Lean

`def` defines a thing, `theorem` states a fact and its proof follows
`:= by`. Lines starting with `--` are comments, in plain words. A proof is a
list of *tactics*; each one changes the goal still to be shown, and the
comment above it says how. `simp` rewrites with known facts; `omega` solves
arithmetic over natural numbers; `cases` splits on the ways a fact could be
true; `induction` proves a fact for every number of steps by proving it for
none and then for one more.
-/

-- Everything below is named Regolith.CfRegistry.<name>.
namespace Regolith.CfRegistry

/-! ## Part 1. The state and the steps -/

/-- A family id's stage, as the registry knows it (`CfRegistry::by_id`). -/
inductive Life where
  /-- Never created: the id has not been handed out. -/
  | unborn
  /-- Created and not dropped: `by_id` holds the id. -/
  | live
  /-- Dropped: `by_id` no longer holds it, and it is never handed out again. -/
  | dead
  -- Two stages can be compared for equality.
  deriving DecidableEq

/-- Where a stage sits in the only order the code moves a family. -/
def Life.rank : Life → Nat
  -- Unborn comes first.
  | .unborn => 0
  -- Then live.
  | .live => 1
  -- Then dead, for good.
  | .dead => 2

/-- Everything about the families at one moment. A family is named by a
natural number, its id. -/
structure State where
  /-- Each id's stage. -/
  life : Nat → Life
  /-- The last sequence number handed out (`latest_seq`). -/
  seq : Nat
  /-- Each id's creation sequence; `0` when not created. -/
  born : Nat → Nat
  /-- Each id's tombstone sequence; `0` when not dropped. -/
  tomb : Nat → Nat
  /-- Every committed write, as (family id, sequence). -/
  landed : List (Nat × Nat)

/-- The start: every id unborn, nothing written. -/
def init : State :=
  -- No family, sequence 0, no birth, no tombstone, no write.
  ⟨fun _ => .unborn, 0, fun _ => 0, fun _ => 0, []⟩

/-- `f` with its value at `k` replaced by `v`. -/
def set {α : Type} (f : Nat → α) (k : Nat) (v : α) : Nat → α :=
  -- At `k` the new value, everywhere else the old one.
  fun x => if x = k then v else f x

/-- Reading `set` at the key it changed gives the new value. -/
@[simp] theorem set_same {α : Type} (f : Nat → α) (k : Nat) (v : α) :
    -- The claim itself; its proof follows.
    set f k v k = v := by
  -- Unfold `set`; the condition `k = k` is true.
  simp [set]

/-- Reading `set` anywhere else gives the old value. -/
theorem set_other {α : Type} (f : Nat → α) (k x : Nat) (v : α) (h : x ≠ k) :
    -- The claim itself; its proof follows.
    set f k v x = f x := by
  -- Unfold `set`; the condition `x = k` is false by `h`.
  simp [set, h]

/-- The steps, one atomic step each, as the ordered step takes them. -/
inductive Step : State → State → Prop
  /-- Create family `f`: its meta write takes the next sequence, and the
  registry publishes the id (`create_family`). -/
  | create (s : State) (f : Nat)
      -- The id was never handed out.
      (h : s.life f = .unborn) :
      -- One more sequence; `f` is born at it and is live.
      Step s { s with seq := s.seq + 1, born := set s.born f (s.seq + 1),
                      life := set s.life f .live }
  /-- Drop family `f`: its tombstone takes the next sequence, and in the same
  ordered step the registry retires the id (`drop_family`). -/
  | drop (s : State) (f : Nat)
      -- Only a live family is dropped.
      (h : s.life f = .live) :
      -- One more sequence; the tombstone sits at it and `f` is dead.
      Step s { s with seq := s.seq + 1, tomb := set s.tomb f (s.seq + 1),
                      life := set s.life f .dead }
  /-- A write to family `f` is admitted: the fence finds it live, and the
  write takes the next sequence (`cf_fence`, then `run_group`). -/
  | land (s : State) (f : Nat)
      -- The fence: `f` is live right now, in the ordered step.
      (h : s.life f = .live) :
      -- One more sequence; the write lands at it.
      Step s { s with seq := s.seq + 1, landed := (f, s.seq + 1) :: s.landed }
  /-- A write to a family that is not live is refused: nothing changes. -/
  | refuse (s : State) (f : Nat)
      -- The fence finds `f` unborn or dead.
      (h : s.life f ≠ .live) :
      -- Nothing at all changes.
      Step s s

/-- The states the steps can reach from the start. -/
inductive Reach : State → Prop
  /-- The start is reachable. -/
  | init : Reach init
  /-- One step from a reachable state reaches another. -/
  | step {s t : State} : Reach s → Step s t → Reach t

/-! ## Part 2. What every reachable state keeps -/

/-- The facts every reachable state has. The three rules follow from them. -/
structure Inv (s : State) : Prop where
  /-- Every write's sequence has been handed out. -/
  landed_le : ∀ p ∈ s.landed, p.2 ≤ s.seq
  /-- An unborn id has no birth, no tombstone, and no write. -/
  unborn_clean : ∀ f, s.life f = .unborn →
    s.born f = 0 ∧ s.tomb f = 0 ∧ ∀ p ∈ s.landed, p.1 ≠ f
  /-- A live family was born and has no tombstone. -/
  live_born : ∀ f, s.life f = .live → s.tomb f = 0 ∧ 0 < s.born f ∧ s.born f ≤ s.seq
  /-- Every write landed above its family's birth. -/
  after_birth : ∀ p ∈ s.landed, 0 < s.born p.1 ∧ s.born p.1 < p.2
  /-- Every write landed below its family's tombstone, if it has one. -/
  before_tomb : ∀ p ∈ s.landed, s.tomb p.1 = 0 ∨ p.2 < s.tomb p.1

/-- The start keeps every fact: there is nothing in it. -/
theorem inv_init : Inv init := by
  -- Each field, about an empty start, holds at once.
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- No write has landed.
  · intro p hp; simp [init] at hp
  -- Every id is unborn, with no birth, no tombstone, no write.
  · intro f _; simp [init]
  -- No id is live at the start.
  · intro f hf; simp [init] at hf
  -- No write has landed.
  · intro p hp; simp [init] at hp
  -- No write has landed.
  · intro p hp; simp [init] at hp

/-- Every step keeps every fact. -/
theorem inv_step {s t : State} (hs : Inv s) (hst : Step s t) : Inv t := by
  -- One case per kind of step.
  cases hst with
  | create f h =>
    -- What the facts say about `f` before its creation.
    obtain ⟨hb0, ht0, hnone⟩ := hs.unborn_clean f h
    -- Prove the parts one at a time; each `?_` becomes a goal of its own.
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    -- Old writes keep their sequences, and the counter only grew.
    · intro p hp; have := hs.landed_le p hp; simp only at hp ⊢; omega
    -- Unborn ids other than `f` are untouched; `f` is no longer unborn.
    · intro g hg
      -- Split: is `g` the family just created?
      by_cases hgf : g = f
      · -- It is: but `f` is live now, not unborn.
        subst hgf; simp at hg
      · -- It is not: its stage, birth and tombstone are unchanged.
        simp only [set_other _ _ _ _ hgf] at hg ⊢
        -- The state's `unborn_clean` fact from before the step gives exactly this.
        exact hs.unborn_clean g hg
    -- Live ids: `f` was just born; the others are as before.
    · intro g hg
      -- Split on whether `g = f` holds.
      by_cases hgf : g = f
      · -- `f`: no tombstone (it was unborn), born at the new sequence.
        subst hgf; simp only [set_same]; exact ⟨ht0, by omega, by omega⟩
      · -- Another live id: unchanged, and the counter grew.
        simp only [set_other _ _ _ _ hgf] at hg ⊢
        -- Keep this fact for the next step, then put the pieces together.
        have := hs.live_born g hg; exact ⟨this.1, this.2.1, by omega⟩
    -- Old writes: none was to `f`, so their family's birth is unchanged.
    · intro p hp
      -- First show `p.1 ≠ f`, named `hpf`.
      have hpf : p.1 ≠ f := hnone p hp
      -- Read through `set` at a key it did not change: the old value.
      simp only [set_other _ _ _ _ hpf]
      -- The state's `after_birth` fact from before the step gives exactly this.
      exact hs.after_birth p hp
    -- Tombstones are unchanged.
    · intro p hp; exact hs.before_tomb p hp
  | drop f h =>
    -- What the facts say about `f` while live.
    obtain ⟨ht0, hb, hbs⟩ := hs.live_born f h
    -- Prove the parts one at a time; each `?_` becomes a goal of its own.
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    -- Old writes keep their sequences, and the counter only grew.
    · intro p hp; have := hs.landed_le p hp; simp only at hp ⊢; omega
    -- Unborn ids: `f` is dead, the others are untouched.
    · intro g hg
      -- Split on whether `g = f` holds.
      by_cases hgf : g = f
      · -- `f` is dead now, not unborn.
        subst hgf; simp at hg
      -- Read through `set` at a key it did not change: the old value.
      · simp only [set_other _ _ _ _ hgf] at hg ⊢
        -- The state's `unborn_clean` fact from before the step gives exactly this.
        exact hs.unborn_clean g hg
    -- Live ids: `f` is dead; the others are as before.
    · intro g hg
      -- Split on whether `g = f` holds.
      by_cases hgf : g = f
      · -- `f` is dead now, not live.
        subst hgf; simp at hg
      -- Read through `set` at a key it did not change: the old value.
      · simp only [set_other _ _ _ _ hgf] at hg ⊢
        -- Keep this fact for the next step, then put the pieces together.
        have := hs.live_born g hg; exact ⟨this.1, this.2.1, by omega⟩
    -- Births are unchanged.
    · intro p hp; exact hs.after_birth p hp
    -- The new tombstone is above every write so far; others unchanged.
    · intro p hp
      -- Split on whether `p.1 = f` holds.
      by_cases hpf : p.1 = f
      · -- A write to `f`: it is at most the old counter, below the tombstone.
        right; rw [hpf]; simp only [set_same]
        -- Keep this fact for the next step, then the arithmetic over natural numbers that is left holds.
        have := hs.landed_le p hp; omega
      · -- A write to another family: its tombstone is unchanged.
        simp only [set_other _ _ _ _ hpf]
        -- The state's `before_tomb` fact from before the step gives exactly this.
        exact hs.before_tomb p hp
  | land f h =>
    -- What the facts say about `f` while live.
    obtain ⟨ht0, hb, hbs⟩ := hs.live_born f h
    -- Prove the parts one at a time; each `?_` becomes a goal of its own.
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    -- The new write is at the new counter; old ones are below it.
    · intro p hp
      -- A member of `x :: l` is `x` itself or a member of `l`.
      simp only [List.mem_cons] at hp
      -- Split the `or` into its cases.
      rcases hp with rfl | hp
      -- Simplify with the definitions until the goal is closed or plain.
      · simp
      -- Keep this fact for the next step, then read off the fields of the record the step wrote, then the arithmetic over natural numbers that is left holds.
      · have := hs.landed_le p hp; simp only; omega
    -- Unborn ids: none is `f` (it is live), and they gained no write.
    · intro g hg
      -- Unpack the facts on the right and name them.
      obtain ⟨h1, h2, h3⟩ := hs.unborn_clean g hg
      -- Prove the parts one at a time; each `?_` becomes a goal of its own.
      refine ⟨h1, h2, ?_⟩
      -- Name the things the goal is about: `p`, `hp`.
      intro p hp
      -- A member of `x :: l` is `x` itself or a member of `l`.
      simp only [List.mem_cons] at hp
      -- Split the `or` into its cases.
      rcases hp with rfl | hp
      · -- The new write is to `f`, which is live, so not `g`.
        intro hfg; simp only at hfg; subst hfg; rw [h] at hg; cases hg
      -- This is exactly what the goal asks.
      · exact h3 p hp
    -- Live ids keep their facts; the counter grew.
    · intro g hg
      -- Keep this fact for the next step, then put the pieces together.
      have := hs.live_born g hg; exact ⟨this.1, this.2.1, by simp only; omega⟩
    -- The new write is above `f`'s birth; old ones as before.
    · intro p hp
      -- A member of `x :: l` is `x` itself or a member of `l`.
      simp only [List.mem_cons] at hp
      -- Split the `or` into its cases.
      rcases hp with rfl | hp
      -- Read off the fields of the record the step wrote, then put the pieces together.
      · simp only; exact ⟨hb, by omega⟩
      -- The state's `after_birth` fact from before the step gives exactly this.
      · exact hs.after_birth p hp
    -- `f` has no tombstone; old writes as before.
    · intro p hp
      -- A member of `x :: l` is `x` itself or a member of `l`.
      simp only [List.mem_cons] at hp
      -- Split the `or` into its cases.
      rcases hp with rfl | hp
      -- Prove the left side of the `or`, then this is exactly what the goal asks.
      · left; exact ht0
      -- The state's `before_tomb` fact from before the step gives exactly this.
      · exact hs.before_tomb p hp
  | refuse f h =>
    -- Nothing changed.
    exact hs

/-- Every reachable state keeps every fact. -/
theorem inv_reach {s : State} (h : Reach s) : Inv s := by
  -- By how `s` was reached: the start, or one step from a reachable state.
  induction h with
  | init => exact inv_init
  | step _ hst ih => exact inv_step ih hst

/-! ## Part 3. The three rules -/

/-- **`no_write_after_drop`.** Every write that landed in a family with a
tombstone is below it, so the tombstone deletes it. Rules out the story's
write at sequence 8 over a tombstone at 7. -/
theorem no_write_after_drop {s : State} (h : Reach s) :
    -- The claim itself; its proof follows.
    ∀ p ∈ s.landed, s.tomb p.1 = 0 ∨ p.2 < s.tomb p.1 :=
  -- One of the facts every reachable state keeps.
  (inv_reach h).before_tomb

/-- **`no_write_before_birth`.** Every write that landed is above its
family's creation. -/
theorem no_write_before_birth {s : State} (h : Reach s) :
    -- The claim itself; its proof follows.
    ∀ p ∈ s.landed, 0 < s.born p.1 ∧ s.born p.1 < p.2 :=
  -- One of the facts every reachable state keeps.
  (inv_reach h).after_birth

/-- One step never moves a family's stage backward. -/
theorem step_rank_le {s t : State} (hst : Step s t) (g : Nat) :
    -- The claim itself; its proof follows.
    (s.life g).rank ≤ (t.life g).rank := by
  -- One case per kind of step.
  cases hst with
  | create f h =>
    -- Only `f` changes, from unborn (0) to live (1).
    by_cases hgf : g = f
    -- Replace one side of `hgf` by the other everywhere, then simplify with the definitions until the goal is closed or plain.
    · subst hgf; simp [h, set_same, Life.rank]
    -- Read through `set` at a key it did not change: the old value.
    · simp [set_other _ _ _ _ hgf]
  | drop f h =>
    -- Only `f` changes, from live (1) to dead (2).
    by_cases hgf : g = f
    -- Replace one side of `hgf` by the other everywhere, then simplify with the definitions until the goal is closed or plain.
    · subst hgf; simp [h, set_same, Life.rank]
    -- Read through `set` at a key it did not change: the old value.
    · simp [set_other _ _ _ _ hgf]
  | land f h =>
    -- No stage changes.
    simp
  | refuse f h =>
    -- Nothing changes.
    simp

/-- Any number of steps, one after another (the reflexive, transitive
closure of `Step`). -/
inductive Steps : State → State → Prop
  /-- No step at all. -/
  | refl (s : State) : Steps s s
  /-- One step, then more. -/
  | cons {s t u : State} : Step s t → Steps t u → Steps s u

/-- **`life_in_order`.** However many steps pass between two looks, the
later look sees a stage at or after the earlier one: unborn, live, dead,
never back. Rules out a reader that saw a family dropped and later saw it
live again. -/
theorem life_in_order {s u : State} (h : Steps s u) (g : Nat) :
    -- The claim itself; its proof follows.
    (s.life g).rank ≤ (u.life g).rank := by
  -- By the number of steps.
  induction h with
  | refl => exact Nat.le_refl _
  | cons hst _ ih => exact Nat.le_trans (step_rank_le hst g) ih

/-! ## Part 4. The RED cases -/

/-- The steps with the fence moved out of the ordered step: a write is
admitted on the strength of a check made earlier, whatever the family is
now (bug `FenceOutside`). -/
inductive BlindStep : State → State → Prop
  /-- The same steps as the real code ... -/
  | real {s t : State} : Step s t → BlindStep s t
  /-- ... plus a write admitted with no check in the ordered step. -/
  | blind (s : State) (f : Nat) :
      -- The state after this step: only the fields named here change.
      BlindStep s { s with seq := s.seq + 1, landed := (f, s.seq + 1) :: s.landed }

/-- The story, step by step: family 1 is created (sequence 1), dropped
(tombstone at 2), and then the write that checked "live" before the drop
lands at 3. -/
def created : State := { init with seq := 1, born := set init.born 1 1, life := set init.life 1 .live }
/-- After the drop: tombstone at 2, family 1 dead. -/
def dropped : State := { created with seq := 2, tomb := set created.tomb 1 2, life := set created.life 1 .dead }
/-- After the blind landing: the write lands at 3. -/
def landedLate : State := { dropped with seq := 3, landed := (1, 3) :: dropped.landed }

/-- **`fence_outside_lands_after_drop`.** With the fence outside the ordered
step, the story's write lands above the tombstone: create, drop, then the
blind landing, and the write at 3 sits over the tombstone at 2. -/
theorem fence_outside_lands_after_drop :
    -- The state after this step: only the fields named here change.
    BlindStep init created ∧ BlindStep created dropped ∧ BlindStep dropped landedLate ∧
    ¬ (∀ p ∈ landedLate.landed, landedLate.tomb p.1 = 0 ∨ p.2 < landedLate.tomb p.1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  -- The create is a real step: id 1 was unborn.
  · exact .real (Step.create init 1 rfl)
  -- The drop is a real step: id 1 was live.
  · exact .real (Step.drop created 1 (by simp [created, set]))
  -- The landing is the blind one.
  · exact .blind dropped 1
  -- The write (1, 3) is over the tombstone 2: the rule fails.
  · intro hall
    -- Keep this fact for the next step.
    have := hall (1, 3) (by simp [landedLate])
    -- Simplify the named facts with the definitions; a false one closes the goal.
    simp [landedLate, dropped, created, set, init] at this

/-- The steps with the retire left until after the ordered step (bug
`RetireLate`): the tombstone commits, but the family stays live meanwhile. -/
inductive LateStep : State → State → Prop
  /-- The same steps as the real code ... -/
  | real {s t : State} : Step s t → LateStep s t
  /-- ... plus a drop that commits its tombstone and leaves `f` live. -/
  | dropNoRetire (s : State) (f : Nat) (h : s.life f = .live) :
      -- The state after this step: only the fields named here change.
      LateStep s { s with seq := s.seq + 1, tomb := set s.tomb f (s.seq + 1) }

/-- After the late drop: tombstone at 2, family 1 still live. -/
def droppedLive : State := { created with seq := 2, tomb := set created.tomb 1 2 }
/-- After a write the fence admits, because the family still looks live. -/
def landedLate2 : State := { droppedLive with seq := 3, landed := (1, 3) :: droppedLive.landed }

/-- **`late_retire_lands_after_drop`.** With the retire after the ordered
step, a write admitted in between passes the fence and lands at 3, over the
tombstone at 2. -/
theorem late_retire_lands_after_drop :
    -- The state after this step: only the fields named here change.
    LateStep init created ∧ LateStep created droppedLive ∧ LateStep droppedLive landedLate2 ∧
    ¬ (∀ p ∈ landedLate2.landed, landedLate2.tomb p.1 = 0 ∨ p.2 < landedLate2.tomb p.1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  -- The create is a real step.
  · exact .real (Step.create init 1 rfl)
  -- The late drop: id 1 was live, and stays live.
  · exact .dropNoRetire created 1 (by simp [created, set])
  -- The landing is a real step: the fence sees id 1 live.
  · exact .real (Step.land droppedLive 1 (by simp [droppedLive, created, set]))
  -- The write (1, 3) is over the tombstone 2: the rule fails.
  · intro hall
    -- Keep this fact for the next step.
    have := hall (1, 3) (by simp [landedLate2])
    -- Simplify the named facts with the definitions; a false one closes the goal.
    simp [landedLate2, droppedLive, created, set, init] at this

/-- **`reused_id_goes_back`.** If a create could take a dead id again (bug
`ReuseId`), a family would go from dead (rank 2) to live (rank 1): a reader
that saw it dropped would then see it live, with a new family's data. -/
theorem reused_id_goes_back :
    -- Name a value the claim below uses.
    let reborn : State := { dropped with seq := 3, life := set dropped.life 1 .live }
    -- The claim itself; its proof follows.
    (dropped.life 1).rank > (reborn.life 1).rank := by
  -- Dead is rank 2, live is rank 1.
  simp [dropped, created, set, Life.rank]

/-! ## Part 5. Group commit: every member is fenced when its group runs

The commit pipeline runs writes in groups (`src/engine/commit/mod.rs`). A
member reaches a group by one of several paths: the leader's own request,
a ticket another writer queued on the ring, the ticket the bounded leader's
hand-off held across the end of one turn and the start of the next, an
optimistic transaction's commit. Whatever the path, the group's first act,
before any sequence, is to check every member against the registry as it
stands then (`fence_group`). Here a whole group is one function of the
state, and it is shown to be a run of the single `land` and `refuse` steps
above, so every rule proved for them holds after any group. -/

/-- One group run in the ordered step (`run_and_complete`): the members'
families, in group order, each checked against the registry as it stands
when the group runs. A member whose family is live takes the next sequence
and lands; one whose family is not is refused and takes none. -/
def runGroup : State → List Nat → State
  -- No member left: the state as it is.
  | s, [] => s
  -- The next member, of family `f`, then the rest of the group.
  | s, f :: rest =>
    -- The rest runs on the state this member leaves behind ...
    runGroup
      -- ... which, when `f` is live, holds one more landed write at the
      -- next sequence, ...
      (if s.life f = .live then
        { s with seq := s.seq + 1, landed := (f, s.seq + 1) :: s.landed }
      -- ... and otherwise is unchanged: the member was refused.
      else s) rest

/-- A group run is a run of single steps: one `land` or one `refuse` per
member, in group order. -/
theorem runGroup_steps (s : State) (ms : List Nat) : Steps s (runGroup s ms) := by
  -- By the number of members, for every starting state.
  induction ms generalizing s with
  | nil =>
    -- No member: zero steps.
    exact Steps.refl s
  | cons f rest ih =>
    -- Split on whether the member's family is live when the group runs.
    by_cases h : s.life f = .live
    · -- Live: unfold one member of the group; the `if` takes its first branch.
      simp only [runGroup, h, ↓reduceIte]
      -- The member is one `land` step, and the rest are more steps.
      exact Steps.cons (Step.land s f h) (ih _)
    · -- Not live: unfold one member; the `if` takes its second branch.
      simp only [runGroup, h, ↓reduceIte]
      -- The member is one `refuse` step, and the rest are more steps.
      exact Steps.cons (Step.refuse s f h) (ih _)

/-- Any number of steps from a reachable state reach a reachable state. -/
theorem reach_steps {s t : State} (hs : Reach s) (h : Steps s t) : Reach t := by
  -- By the number of steps.
  induction h with
  | refl =>
    -- No step: the state is the reachable one we started from.
    exact hs
  | cons hst _ ih =>
    -- One step reaches a reachable state, and the rest follow from it.
    exact ih (Reach.step hs hst)

/-- **`group_no_write_after_drop`.** After any group run from a reachable
state, every write that landed in a dropped family is below its tombstone:
however its members were admitted, the check when the group runs is what
keeps the rule (TLA+ `NoWriteAfterDrop` on `MC_CfRegistry_Green`). -/
theorem group_no_write_after_drop {s : State} (h : Reach s) (ms : List Nat) :
    -- The claim itself; its proof follows.
    ∀ p ∈ (runGroup s ms).landed,
      (runGroup s ms).tomb p.1 = 0 ∨ p.2 < (runGroup s ms).tomb p.1 :=
  -- The group is a run of steps, so its end is reachable, and every
  -- reachable state keeps the rule.
  no_write_after_drop (reach_steps h (runGroup_steps s ms))

/-- **`group_no_write_before_birth`.** After any group run from a reachable
state, every write that landed is above its family's creation. -/
theorem group_no_write_before_birth {s : State} (h : Reach s) (ms : List Nat) :
    -- The claim itself; its proof follows.
    ∀ p ∈ (runGroup s ms).landed,
      0 < (runGroup s ms).born p.1 ∧ (runGroup s ms).born p.1 < p.2 :=
  -- As above: the group's end is reachable.
  no_write_before_birth (reach_steps h (runGroup_steps s ms))

/-- In the story, the real code refuses the held ticket: its group runs
after the drop, finds family 1 dead, and lands nothing. -/
theorem fenced_when_run_refuses_after_drop : runGroup dropped [1] = dropped := by
  -- Family 1 is dead in `dropped`, so the one member is refused.
  simp [runGroup, dropped, created, set, init]

/-- **`fenced_at_hand_off_lands_after_drop`.** The ticket the hand-off holds,
checked when the hand-off took it rather than when its group runs (bug
`FenceAtHandOff`): the check passes in `created`, where family 1 is live;
the drop's group then runs (tombstone at 2, family 1 dead); the held
ticket's group runs on that earlier pass, which is a landing with no check,
and the write at 3 sits over the tombstone at 2. A transaction member that
skips the check (bug `TxnUnfenced`) lands the same way. -/
theorem fenced_at_hand_off_lands_after_drop :
    -- The check at hand-off passes, then the drop, then the unchecked
    -- landing, and the rule fails.
    created.life 1 = .live ∧ BlindStep created dropped ∧ BlindStep dropped landedLate ∧
    ¬ (∀ p ∈ landedLate.landed, landedLate.tomb p.1 = 0 ∨ p.2 < landedLate.tomb p.1) := by
  -- The drop, the unchecked landing and the broken rule are the story of
  -- `fence_outside_lands_after_drop`.
  obtain ⟨_, hdrop, hland, hbad⟩ := fence_outside_lands_after_drop
  -- Family 1 is live in `created`; the rest is that story.
  exact ⟨by simp [created, set], hdrop, hland, hbad⟩

-- The end of this file's names.
end Regolith.CfRegistry
