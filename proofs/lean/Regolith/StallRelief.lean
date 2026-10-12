/-!
# StallRelief: no stopped writer waits on a relief nobody runs

This file backs the TLA+ model `proofs/tla/StallRelief.tla`. TLC checks
three writers there; here the rule is proved for any number of writers.

## The story, for a reader who has never seen the code

A write "stop" refuses writes until the background makes room. With no
background worker, a stopped writer makes room itself, with flush and
compaction steps, and for each step it needs the "gate". If another thread
holds the gate, the writer does not wait for the gate: it waits on the
stall's unit, trusting the gate's holder.

Three kinds of thread hold the gate: a stopped writer relieving the stop;
a writer whose write left one step owing, which it runs once and returns;
and a foreground job (an ingest, a checkpoint), which holds it for its
whole run.

Tiny example: writer 1 holds the gate for one step, writer 2 finds it held
and waits, writer 1's step leaves the stop on and writer 1 returns. If the
unit landed only when the stop cleared, writer 2 would wait for ever. So
every piece of progress lands the unit, stop or no stop ("relief handed
back"), and each waiter looks again. A writer that found the gate held but
registers only after such a landing would miss it, so it reads a progress
count before its step and again once registered, and lands its own unit if
the count moved. A job that held the gate relieves the stop once it
releases the gate.

## What is proved, in plain words

1. `no_stranded_wait`: in every state the real code reaches, once every
   writer has finished or waits, and the job is not running or still to
   relieve, nobody waits (TLA+ `NoStrandedWait`).
2. The RED cases, each a run of the buggy steps that ends with a writer
   waiting and nobody left to land its unit:
   `no_relief_strands_a_waiter` (the job ends with no relief),
   `no_hand_back_strands_a_waiter` (progress lands the unit only when the
   stop cleared), `no_recheck_strands_a_waiter` (a contended writer
   registers without reading the count again).

## How the writers are counted

Writers are counted by what they are doing, not named. A contended writer
is "fresh" while no progress was counted since it read the count, and
"stale" once some was: that is all the count's value is used for.

## How to read the Lean

`def` defines a thing, `theorem` states a fact and its proof follows
`:= by`. Lines starting with `--` are comments, in plain words. A proof is a
list of *tactics*; each one changes the goal still to be shown, and the
comment above it says how. `simp` rewrites with known facts; `omega` solves
arithmetic over natural numbers; `cases` splits on the ways a fact could be
true; `induction` proves a fact for every number of steps.
-/

-- Everything below is named Regolith.StallRelief.<name>.
namespace Regolith.StallRelief

/-- Which code the steps follow. -/
inductive Mode where
  /-- The real code. -/
  | green
  /-- Bug: the job ends with no relief. -/
  | noRelief
  /-- Bug: progress lands the unit only when the stop cleared. -/
  | noHandBack
  /-- Bug: a contended writer registers without reading the count again. -/
  | noRecheck
  -- Two modes can be compared for equality.
  deriving DecidableEq

/-- Who holds the gate. -/
inductive Gate where
  /-- Nobody. -/
  | free
  /-- The foreground job. -/
  | job
  /-- A writer's step: relieving, or the one it owed. -/
  | writer
  -- Two holders can be compared for equality.
  deriving DecidableEq

/-- The foreground job's progress. -/
inductive Job where
  /-- Not started. -/
  | idle
  /-- Holding the gate, doing its work. -/
  | holding
  /-- Released the gate, about to relieve the stop. -/
  | relieving
  /-- Finished. -/
  | done
  -- Two stages can be compared for equality.
  deriving DecidableEq

/-- Everything at one moment. Writers are counted by what they are doing;
finished writers are not counted. -/
structure State where
  /-- Whether a write would be stopped now. -/
  stopped : Bool
  /-- Who holds the gate. -/
  gate : Gate
  /-- The job's progress. -/
  job : Job
  /-- Writers about to write. -/
  writing : Nat
  /-- Writers whose write went in and left one step owing. -/
  owing : Nat
  /-- Writers whose step holds the gate (at most one). -/
  holding : Nat
  /-- Writers that released the gate and have yet to count their progress. -/
  refreshing : Nat
  /-- Contended writers that have missed no progress. -/
  fresh : Nat
  /-- Contended writers that have missed some progress. -/
  stale : Nat
  /-- Writers waiting on the stall's unit. -/
  waiting : Nat
  -- Two states can be compared for equality.
  deriving DecidableEq

/-- The start with `n` writers, stopped or not: the gate free, the job not
started, every writer about to write. -/
def start (n : Nat) (b : Bool) : State :=
  -- Only `writing` counts anyone.
  ⟨b, .free, .idle, n, 0, 0, 0, 0, 0, 0⟩

/-- The unit lands: every waiter is about to write again. -/
def land (s : State) : State :=
  -- The waiters join the writers.
  { s with writing := s.writing + s.waiting, waiting := 0 }

/-- A piece of progress is counted: every contended writer has now missed
one. -/
def count (s : State) : State :=
  -- The fresh ones become stale.
  { s with stale := s.stale + s.fresh, fresh := 0 }

/-- Whether a piece of progress lands the unit, in mode `m`, with the stop
now `b`. -/
def lands : Mode → Bool → Bool
  -- The bug: only once the stop cleared.
  | .noHandBack, b => !b
  -- The real code: always.
  | _, _ => true

/-- A piece of progress in mode `m`: counted, and the unit landed as `lands`
says. -/
def progress (m : Mode) (s : State) : State :=
  -- Count first; land when `lands` says so.
  if lands m s.stopped then land (count s) else count s

/-- The steps, in mode `m`. -/
inductive Step (m : Mode) : State → State → Prop
  /-- The job takes the free gate. -/
  | jobStart (s : State) (h1 : s.job = .idle) (h2 : s.gate = .free) :
      -- It holds the gate.
      Step m s { s with gate := .job, job := .holding }
  /-- The job ends its work and releases the gate; it relieves next, or,
  in bug `noRelief`, is finished. -/
  | jobEnd (s : State) (h : s.job = .holding) :
      -- The gate is free.
      Step m s { s with gate := .free, job := if m = .noRelief then .done else .relieving }
  /-- The job's relief with the gate free: its steps leave the stop as `b`,
  and its progress is counted and lands the unit. -/
  | jobRelieveFree (s : State) (b : Bool) (h1 : s.job = .relieving) (h2 : s.gate = .free) :
      -- Finished, after its progress.
      Step m s (land (count { s with stopped := b, job := .done }))
  /-- The job's relief with a writer's step holding the gate: left to that
  writer. -/
  | jobRelieveHeld (s : State) (h1 : s.job = .relieving) (h2 : s.gate = .writer) :
      -- Only the job's progress changes.
      Step m s { s with job := .done }
  /-- A writer's write goes in: no stop. It may bring on the stop (`b`),
  and leaves one step owing. -/
  | write (s : State) (b : Bool) (h1 : 0 < s.writing) (h2 : s.stopped = false) :
      -- One writer moves from writing to owing.
      Step m s { s with stopped := b, writing := s.writing - 1, owing := s.owing + 1 }
  /-- A stopped writer finds the gate free: its step takes it. -/
  | relieve (s : State) (h1 : 0 < s.writing) (h2 : s.stopped = true) (h3 : s.gate = .free) :
      -- It holds the gate.
      Step m s { s with gate := .writer, writing := s.writing - 1, holding := s.holding + 1 }
  /-- A stopped writer reads the count, and its step finds the gate held. -/
  | contend (s : State) (h1 : 0 < s.writing) (h2 : s.stopped = true) (h3 : s.gate ≠ .free) :
      -- One more fresh contended writer.
      Step m s { s with writing := s.writing - 1, fresh := s.fresh + 1 }
  /-- An owing writer's step finds the gate free and takes it. -/
  | owedTake (s : State) (h1 : 0 < s.owing) (h2 : s.gate = .free) :
      -- It holds the gate.
      Step m s { s with gate := .writer, owing := s.owing - 1, holding := s.holding + 1 }
  /-- An owing writer's step finds the gate held: the writer returns. -/
  | owedContended (s : State) (h1 : 0 < s.owing) (h2 : s.gate ≠ .free) :
      -- It is finished.
      Step m s { s with owing := s.owing - 1 }
  /-- A writer's step ends, leaving the stop as `b`, and releases the gate. -/
  | stepEnd (s : State) (b : Bool) (h : 0 < s.holding) :
      -- The gate is free; the writer counts its progress next.
      Step m s { s with stopped := b, gate := .free, holding := s.holding - 1,
                        refreshing := s.refreshing + 1 }
  /-- A writer counts its step's progress; then it writes again
  (`back = 1`) or is finished (`back = 0`: it gave up, or its step was the
  owed one). -/
  | refresh (s : State) (back : Nat) (hb : back ≤ 1) (h : 0 < s.refreshing) :
      -- Its progress, then the writer's next place.
      Step m s (progress m { s with refreshing := s.refreshing - 1,
                                    writing := s.writing + back })
  /-- A fresh contended writer registers and finds the stop cleared: it
  counts that progress, which lands the unit, and writes again. -/
  | clearedFresh (s : State) (h1 : 0 < s.fresh) (h2 : s.stopped = false) :
      -- Counted and landed.
      Step m s (land (count { s with fresh := s.fresh - 1, writing := s.writing + 1 }))
  /-- A stale contended writer registers and finds the stop cleared: the
  same. -/
  | clearedStale (s : State) (h1 : 0 < s.stale) (h2 : s.stopped = false) :
      -- Counted and landed.
      Step m s (land (count { s with stale := s.stale - 1, writing := s.writing + 1 }))
  /-- A stale contended writer registers with the stop on: the count moved,
  so it lands the unit and writes again; in bug `noRecheck` it waits. -/
  | registerStale (s : State) (h1 : 0 < s.stale) (h2 : s.stopped = true) :
      -- Landed, or, for the bug, one more waiter.
      Step m s (if m = .noRecheck then { s with stale := s.stale - 1, waiting := s.waiting + 1 }
                else land { s with stale := s.stale - 1, writing := s.writing + 1 })
  /-- A fresh contended writer registers with the stop on: it waits. -/
  | registerFresh (s : State) (h1 : 0 < s.fresh) (h2 : s.stopped = true) :
      -- One more waiter.
      Step m s { s with fresh := s.fresh - 1, waiting := s.waiting + 1 }

/-- The states the steps of mode `m` reach from a start. -/
inductive Reach (m : Mode) : State → Prop
  /-- A start is reachable. -/
  | start (n : Nat) (b : Bool) : Reach m (start n b)
  /-- One step from a reachable state reaches another. -/
  | step {s t : State} : Reach m s → Step m s t → Reach m t

/-- Someone is on the way to count a piece of progress: the job at work or
about to relieve, a writer holding the gate, or one about to count. -/
def Pending (s : State) : Prop :=
  -- Any of the four.
  s.job = .holding ∨ s.job = .relieving ∨ s.holding = 1 ∨ 0 < s.refreshing

/-- The facts every state the real code reaches has. -/
structure Inv (s : State) : Prop where
  /-- A writer holds the gate exactly when one writer's step does. -/
  writer_gate : (s.gate = .writer ↔ s.holding = 1) ∧ s.holding ≤ 1
  /-- The job holds the gate exactly while it does its work. -/
  job_gate : s.gate = .job ↔ s.job = .holding
  /-- A waiter waits on someone on the way. -/
  waiter_pending : 0 < s.waiting → Pending s
  /-- So does a contended writer that has missed no progress. -/
  fresh_pending : 0 < s.fresh → Pending s

/-- Every start has the facts. -/
theorem inv_start (n : Nat) (b : Bool) : Inv (start n b) := by
  -- Nobody holds the gate, nobody waits, nobody is contended.
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> simp [start]

/-- A free gate means no writer's step holds it. -/
theorem holding_zero {s : State} (hw1 : s.gate = .writer ↔ s.holding = 1)
    (hw2 : s.holding ≤ 1) (h : s.gate = .free) : s.holding = 0 := by
  -- One holding would mean a writer's gate, not a free one.
  have : s.holding ≠ 1 := fun h' => by rw [hw1.mpr h'] at h; cases h
  -- So none.
  omega

/-- Every step of the real code keeps the facts. -/
theorem inv_step {s t : State} (hs : Inv s) (hst : Step .green s t) : Inv t := by
  -- What the facts say before the step.
  obtain ⟨⟨hw1, hw2⟩, hj, hwait, hfresh⟩ := hs
  -- One case per kind of step.
  cases hst with
  | jobStart h1 h2 =>
    -- The gate was free, so no writer's step held it.
    have h0 := holding_zero hw1 hw2 h2
    -- Each fact, with the job holding the gate.
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    -- Not a writer's gate, and no writer holds it.
    · simp [h0]
    -- At most one.
    · simp only; omega
    -- The job's gate, and the job at work.
    · simp
    -- A waiter waits on the job at work.
    · intro _; exact Or.inl rfl
    -- So does a fresh contended writer.
    · intro _; exact Or.inl rfl
  | jobEnd h =>
    -- The job held the gate, so no writer's step did.
    have hg : s.gate = .job := hj.mpr h
    -- So no writer holds it.
    have h0 : s.holding ≠ 1 := fun h' => by rw [hw1.mpr h'] at hg; cases hg
    -- Each fact, with the gate free and the job about to relieve.
    refine ⟨⟨?_, hw2⟩, ?_, ?_, ?_⟩
    -- Not a writer's gate, and no writer holds it.
    · simp; omega
    -- Not the job's gate, and the job not at work.
    · simp
    -- A waiter waits on the job's relief.
    · intro _; exact Or.inr (Or.inl rfl)
    -- So does a fresh contended writer.
    · intro _; exact Or.inr (Or.inl rfl)
  | jobRelieveFree b h1 h2 =>
    -- The gate is free, so no writer holds it.
    have h0 := holding_zero hw1 hw2 h2
    -- Each fact: the gate still free, nobody waits, nobody fresh.
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    -- Not a writer's gate, and no writer holds it.
    · simp [land, count, h2, h0]
    -- At most one.
    · simp only [land, count]; omega
    -- Not the job's gate, and the job finished.
    · simp [land, count, h2]
    -- Nobody waits.
    · intro h; simp [land, count] at h
    -- Nobody is fresh.
    · intro h; simp [land, count] at h
  | jobRelieveHeld h1 h2 =>
    -- A writer's step holds the gate.
    have hrel : s.holding = 1 := hw1.mp h2
    -- Each fact: only the job changed.
    refine ⟨⟨hw1, hw2⟩, ?_, ?_, ?_⟩
    -- A writer's gate is not the job's, and the job is finished.
    · simp [h2]
    -- A waiter waits on the writer holding the gate.
    · intro _; exact Or.inr (Or.inr (Or.inl hrel))
    -- So does a fresh contended writer.
    · intro _; exact Or.inr (Or.inr (Or.inl hrel))
  | write b h1 h2 =>
    -- Only the stop and two writer counts change: the facts stay.
    exact ⟨⟨hw1, hw2⟩, hj, hwait, hfresh⟩
  | relieve h1 h2 h3 =>
    -- The gate was free, so no writer's step held it.
    have h0 := holding_zero hw1 hw2 h3
    -- And the job was not at work.
    have hnj : s.job ≠ .holding := fun h => by rw [hj.mpr h] at h3; cases h3
    -- Each fact, with the writer's step holding the gate.
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    -- A writer's gate, and one writer holds it.
    · simp; omega
    -- At most one.
    · simp only; omega
    -- Not the job's gate, and the job not at work.
    · simp [hnj]
    -- A waiter waits on the writer holding the gate.
    · intro _; exact Or.inr (Or.inr (Or.inl (by simp only; omega)))
    -- So does a fresh contended writer.
    · intro _; exact Or.inr (Or.inr (Or.inl (by simp only; omega)))
  | contend h1 h2 h3 =>
    -- The gate is held: by the job at work, or by a writer's step.
    have hp : Pending s := by
      -- Split on who holds it.
      cases hg : s.gate with
      -- Free: ruled out by the step's condition.
      | free => exact absurd hg h3
      -- The job: it is at work.
      | job => exact Or.inl (hj.mp hg)
      -- A writer: its step holds it.
      | writer => exact Or.inr (Or.inr (Or.inl (hw1.mp hg)))
    -- Each fact: one more fresh writer, everything else as it was.
    refine ⟨⟨hw1, hw2⟩, hj, ?_, ?_⟩
    -- A waiter waits on whoever holds the gate.
    · intro _; exact hp
    -- So does the new fresh writer.
    · intro _; exact hp
  | owedTake h1 h2 =>
    -- The gate was free, so no writer's step held it.
    have h0 := holding_zero hw1 hw2 h2
    -- And the job was not at work.
    have hnj : s.job ≠ .holding := fun h => by rw [hj.mpr h] at h2; cases h2
    -- Each fact, with the owed step holding the gate.
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    -- A writer's gate, and one writer holds it.
    · simp; omega
    -- At most one.
    · simp only; omega
    -- Not the job's gate, and the job not at work.
    · simp [hnj]
    -- A waiter waits on the owed step.
    · intro _; exact Or.inr (Or.inr (Or.inl (by simp only; omega)))
    -- So does a fresh contended writer.
    · intro _; exact Or.inr (Or.inr (Or.inl (by simp only; omega)))
  | owedContended h1 h2 =>
    -- Only the owing count changes: the facts stay.
    exact ⟨⟨hw1, hw2⟩, hj, hwait, hfresh⟩
  | stepEnd b h =>
    -- A writer's step held the gate, so the job was not at work.
    have hg : s.gate = .writer := hw1.mpr (by omega)
    -- So the job was not at work.
    have hnj : s.job ≠ .holding := fun h' => by rw [hj.mpr h'] at hg; cases hg
    -- Each fact, with the gate free and one writer about to count.
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    -- Not a writer's gate, and no writer holds it.
    · simp; omega
    -- At most one.
    · simp only; omega
    -- Not the job's gate, and the job not at work.
    · simp [hnj]
    -- A waiter waits on the writer about to count.
    · intro _; exact Or.inr (Or.inr (Or.inr (by simp only; omega)))
    -- So does a fresh contended writer.
    · intro _; exact Or.inr (Or.inr (Or.inr (by simp only; omega)))
  | refresh back hb h =>
    -- Each fact: the gate as it was, nobody waits, nobody fresh.
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    -- The gate and the holders are as they were.
    · simp [progress, lands, land, count, hw1]
    -- At most one.
    · simp only [progress, lands, land, count, ↓reduceIte]; omega
    -- The gate and the job are as they were.
    · simp [progress, lands, land, count, hj]
    -- Nobody waits: the progress landed the unit.
    · intro h'; simp [progress, lands, land, count] at h'
    -- Nobody is fresh: the progress was counted.
    · intro h'; simp [progress, lands, land, count] at h'
  | clearedFresh h1 h2 =>
    -- Each fact: the gate as it was, nobody waits, nobody fresh.
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    -- The gate and the holders are as they were.
    · simp [land, count, hw1]
    -- At most one.
    · simp only [land, count]; omega
    -- The gate and the job are as they were.
    · simp [land, count, hj]
    -- Nobody waits.
    · intro h'; simp [land, count] at h'
    -- Nobody is fresh.
    · intro h'; simp [land, count] at h'
  | clearedStale h1 h2 =>
    -- Each fact: the gate as it was, nobody waits, nobody fresh.
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    -- The gate and the holders are as they were.
    · simp [land, count, hw1]
    -- At most one.
    · simp only [land, count]; omega
    -- The gate and the job are as they were.
    · simp [land, count, hj]
    -- Nobody waits.
    · intro h'; simp [land, count] at h'
    -- Nobody is fresh.
    · intro h'; simp [land, count] at h'
  | registerStale h1 h2 =>
    -- Each fact: the real code lands the unit; the fresh are as they were.
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    -- The gate and the holders are as they were.
    · simp [land, hw1]
    -- At most one.
    · simp only [land, reduceCtorEq, ↓reduceIte]; omega
    -- The gate and the job are as they were.
    · simp [land, hj]
    -- Nobody waits.
    · intro h'; simp [land] at h'
    -- A fresh writer still waits on whoever it did.
    · intro h'; simp only [land, reduceCtorEq, ↓reduceIte] at h' ⊢; exact hfresh h'
  | registerFresh h1 h2 =>
    -- It missed no progress, so someone is on the way.
    have hp : Pending s := hfresh h1
    -- Each fact: one more waiter, everything else as it was.
    refine ⟨⟨hw1, hw2⟩, hj, ?_, ?_⟩
    -- The waiters wait on that someone.
    · intro _; exact hp
    -- So do the remaining fresh writers.
    · intro _; exact hp

/-- Every state the real code reaches has the facts. -/
theorem inv_reach {s : State} (h : Reach .green s) : Inv s := by
  -- By how `s` was reached.
  induction h with
  -- A start has them.
  | start n b => exact inv_start n b
  -- A step keeps them.
  | step _ hst ih => exact inv_step ih hst

/-- Nobody is left but waiters: no writer about to write, owing, holding
the gate, about to count, or contended, and the job not running or still
to relieve. -/
def OnlyWaiters (s : State) : Prop :=
  -- Every count but `waiting` is zero, and the job is idle or finished.
  s.writing = 0 ∧ s.owing = 0 ∧ s.holding = 0 ∧ s.refreshing = 0 ∧ s.fresh = 0 ∧
    s.stale = 0 ∧ s.job ≠ .holding ∧ s.job ≠ .relieving

/-- **`no_stranded_wait`.** In every state the real code reaches, once
nobody is left but waiters, nobody waits: someone was always on the way to
land the unit. Rules out the story's writer 2 waiting for ever. -/
theorem no_stranded_wait {s : State} (h : Reach .green s) (ho : OnlyWaiters s) :
    s.waiting = 0 := by
  -- The facts of the reachable state.
  have hi := inv_reach h
  -- What nobody-but-waiters says.
  obtain ⟨_, _, hh, hr, _, _, hjh, hjr⟩ := ho
  -- Either nobody waits, or somebody does.
  rcases Nat.eq_zero_or_pos s.waiting with h0 | hpos
  -- Nobody waits: that is the claim.
  · exact h0
  -- Somebody waits: then someone is on the way, and each kind is ruled out.
  · rcases hi.waiter_pending hpos with h' | h' | h' | h'
    -- Not the job at work.
    · exact absurd h' hjh
    -- Not the job about to relieve.
    · exact absurd h' hjr
    -- No writer holds the gate.
    · omega
    -- No writer is about to count.
    · omega

/-- **`no_relief_strands_a_waiter`.** Bug `noRelief`: the stop is on; the
job takes the gate; the one writer finds it held and waits; the job ends
with no relief. Nobody is left but the waiter. -/
theorem no_relief_strands_a_waiter :
    -- Some state the buggy steps reach has only waiters, and one.
    ∃ s, Reach .noRelief s ∧ OnlyWaiters s ∧ s.waiting = 1 := by
  -- The run, step by step from one writer and the stop on.
  have h0 := Reach.start (m := .noRelief) 1 true
  -- The job takes the gate.
  have h1 := Reach.step h0 (Step.jobStart _ rfl rfl)
  -- The writer is stopped and contended.
  have h2 := Reach.step h1 (Step.contend _ (by decide) rfl (by decide))
  -- It registers and waits.
  have h3 := Reach.step h2 (Step.registerFresh _ (by decide) rfl)
  -- The job ends, with no relief.
  have h4 := Reach.step h3 (Step.jobEnd _ rfl)
  -- That last state has only a waiter.
  exact ⟨_, h4, by unfold OnlyWaiters; decide, rfl⟩

/-- **`no_hand_back_strands_a_waiter`.** Bug `noHandBack`: the stop is on;
writer 1's relieving step takes the gate; writer 2 finds it held and waits;
writer 1's step leaves the stop on, its progress lands nothing, and writer
1 gives up. Nobody is left but the waiter. -/
theorem no_hand_back_strands_a_waiter :
    -- Some state the buggy steps reach has only waiters, and one.
    ∃ s, Reach .noHandBack s ∧ OnlyWaiters s ∧ s.waiting = 1 := by
  -- The run, step by step from two writers and the stop on.
  have h0 := Reach.start (m := .noHandBack) 2 true
  -- Writer 1's step takes the gate.
  have h1 := Reach.step h0 (Step.relieve _ (by decide) rfl rfl)
  -- Writer 2 is stopped and contended.
  have h2 := Reach.step h1 (Step.contend _ (by decide) rfl (by decide))
  -- It registers and waits.
  have h3 := Reach.step h2 (Step.registerFresh _ (by decide) rfl)
  -- Writer 1's step ends with the stop still on.
  have h4 := Reach.step h3 (Step.stepEnd _ true (by decide))
  -- Writer 1 counts its progress, which lands nothing, and gives up.
  have h5 := Reach.step h4 (Step.refresh _ 0 (by decide) (by decide))
  -- That last state has only a waiter.
  exact ⟨_, h5, by unfold OnlyWaiters; decide, rfl⟩

/-- **`no_recheck_strands_a_waiter`.** Bug `noRecheck`: the stop is on;
writer 1's relieving step holds the gate; writer 2 reads the count and
finds the gate held; writer 1's step ends, its progress lands the unit with
nobody on it, and writer 1 gives up; writer 2 registers and waits. Nobody is
left but the waiter. -/
theorem no_recheck_strands_a_waiter :
    -- Some state the buggy steps reach has only waiters, and one.
    ∃ s, Reach .noRecheck s ∧ OnlyWaiters s ∧ s.waiting = 1 := by
  -- The run, step by step from two writers and the stop on.
  have h0 := Reach.start (m := .noRecheck) 2 true
  -- Writer 1's step takes the gate.
  have h1 := Reach.step h0 (Step.relieve _ (by decide) rfl rfl)
  -- Writer 2 is stopped and contended.
  have h2 := Reach.step h1 (Step.contend _ (by decide) rfl (by decide))
  -- Writer 1's step ends with the stop still on.
  have h3 := Reach.step h2 (Step.stepEnd _ true (by decide))
  -- Writer 1 counts its progress, landing nobody, and gives up.
  have h4 := Reach.step h3 (Step.refresh _ 0 (by decide) (by decide))
  -- Writer 2, stale now, registers without looking at the count, and waits.
  have h5 := Reach.step h4 (Step.registerStale _ (by decide) rfl)
  -- That last state has only a waiter.
  exact ⟨_, h5, by unfold OnlyWaiters; decide, rfl⟩

-- The end of this file's names.
end Regolith.StallRelief
