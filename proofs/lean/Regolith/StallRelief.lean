/-!
# StallRelief: a job that held the compaction gate strands no stopped writer

This file backs the TLA+ model `proofs/tla/StallRelief.tla`. TLC checks
two writers there; here the rule is proved for any number of writers.

## The story, for a reader who has never seen the code

A write "stop" refuses writes until compaction makes room. With no
background worker, a stopped writer compacts itself, and for that it needs
the compaction gate. If another thread holds the gate, the writer does not
wait for the gate: it waits on the stall's unit, trusting the gate's holder
to clear the stop and land the unit.

A foreground job (an ingest, a checkpoint) holds the gate for its whole run
and compacts nothing. Tiny example: an ingest takes the gate, two stopped
writers find it held and wait; the ingest ends. Without the fix nobody
compacts and nobody lands the unit, and the writers wait for ever. With the
fix (`relieve_after_foreground`, `src/engine/foreground.rs`) the job, once it
releases the gate, relieves the stop itself and lands the unit, or leaves it
to a writer already relieving.

## What is proved, in plain words

1. `job_end_strands_no_waiter`: in every reachable state, once the job is
   finished and no writer is relieving, no writer is waiting (TLA+
   `NoStrandedWait`).
2. `no_relief_strands_waiters`: with the job ending without the relief (bug
   `NoRelief`), a short run finishes the job with a writer still waiting
   and nobody relieving.

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

/-- Who holds the compaction gate. -/
inductive Gate where
  /-- Nobody. -/
  | free
  /-- The foreground job. -/
  | job
  /-- A stopped writer whose relief step is compacting. -/
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

/-- Everything at one moment. Writers are counted by what they are doing. -/
structure State where
  /-- Whether a write would be stopped now. -/
  stopped : Bool
  /-- Who holds the gate. -/
  gate : Gate
  /-- The job's progress. -/
  job : Job
  /-- Writers about to write. -/
  writing : Nat
  /-- Writers relieving the stop (at most one: the gate is exclusive). -/
  relieving : Nat
  /-- Writers waiting on the stall's unit. -/
  waiting : Nat

/-- The start with `n` writers: stopped, the gate free, the job not started,
every writer about to write. -/
def start (n : Nat) : State :=
  -- Stopped, gate free, job idle, `n` writers writing, none relieving or
  -- waiting.
  ⟨true, .free, .idle, n, 0, 0⟩

/-- The steps of the real code. -/
inductive Step : State → State → Prop
  /-- The job takes the free gate. -/
  | jobStart (s : State) (h1 : s.job = .idle) (h2 : s.gate = .free) :
      -- It holds the gate.
      Step s { s with gate := .job, job := .holding }
  /-- The job ends its work and releases the gate; it relieves next. -/
  | jobEnd (s : State) (h : s.job = .holding) :
      -- The gate is free, the relief is next.
      Step s { s with gate := .free, job := .relieving }
  /-- The job's relief with the gate free: the stop clears and the unit
  lands, waking every waiter. -/
  | jobRelieveFree (s : State) (h1 : s.job = .relieving) (h2 : s.gate = .free) :
      -- Not stopped, waiters back to writing, the job finished.
      Step s { s with stopped := false, job := .done, writing := s.writing + s.waiting,
                      waiting := 0 }
  /-- The job's relief with a writer's step holding the gate: that writer
  lands the unit, and the job is finished. -/
  | jobRelieveHeld (s : State) (h1 : s.job = .relieving) (h2 : s.gate = .writer) :
      -- Only the job's progress changes.
      Step s { s with job := .done }
  /-- A writer's write goes in: no stop. -/
  | write (s : State) (h1 : 0 < s.writing) (h2 : s.stopped = false) :
      -- One writer fewer about to write.
      Step s { s with writing := s.writing - 1 }
  /-- A stopped writer finds the gate free and relieves. -/
  | relieve (s : State) (h1 : 0 < s.writing) (h2 : s.stopped = true) (h3 : s.gate = .free) :
      -- It holds the gate and is relieving.
      Step s { s with gate := .writer, writing := s.writing - 1, relieving := s.relieving + 1 }
  /-- A stopped writer finds the gate held and waits on the unit. -/
  | wait (s : State) (h1 : 0 < s.writing) (h2 : s.stopped = true) (h3 : s.gate ≠ .free) :
      -- One more waiter.
      Step s { s with writing := s.writing - 1, waiting := s.waiting + 1 }
  /-- The relieving writer's step clears the stop, frees the gate and lands
  the unit; it and every waiter go back to writing. -/
  | step (s : State) (h : 0 < s.relieving) :
      -- Not stopped, gate free, everyone writing again.
      Step s { s with stopped := false, gate := .free, relieving := s.relieving - 1,
                      writing := s.writing + 1 + s.waiting, waiting := 0 }

/-- The states the steps reach from a start. -/
inductive Reach : State → Prop
  /-- A start is reachable. -/
  | start (n : Nat) : Reach (start n)
  /-- One step from a reachable state reaches another. -/
  | step {s t : State} : Reach s → Step s t → Reach t

/-- The facts every reachable state has. -/
structure Inv (s : State) : Prop where
  /-- A writer relieves exactly when a writer holds the gate. -/
  writer_gate : (s.gate = .writer ↔ s.relieving = 1) ∧ s.relieving ≤ 1
  /-- The job holds the gate exactly while it does its work. -/
  job_gate : s.gate = .job ↔ s.job = .holding
  /-- A waiter is waiting on someone: the job at work or about to relieve,
  or a relieving writer. -/
  waiter_has_relief : 0 < s.waiting →
    s.job = .holding ∨ s.job = .relieving ∨ s.relieving = 1

/-- Every start has the facts. -/
theorem inv_start (n : Nat) : Inv (start n) := by
  -- Nobody holds the gate and nobody waits.
  refine ⟨?_, ?_, ?_⟩ <;> simp [start]

/-- Every step keeps the facts. -/
theorem inv_step {s t : State} (hs : Inv s) (hst : Step s t) : Inv t := by
  -- What the facts say before the step.
  obtain ⟨⟨hw1, hw2⟩, hj, hr⟩ := hs
  -- One case per kind of step.
  cases hst with
  | jobStart h1 h2 =>
    -- The gate was free, so no writer relieved; now the job holds it.
    have : s.relieving ≠ 1 := fun h => by rw [hw1.mpr h] at h2; cases h2
    -- Each fact, with the new gate and job.
    refine ⟨⟨?_, hw2⟩, ?_, ?_⟩
    -- The job holds the gate, not a writer.
    · simp; omega
    -- The job holds the gate and is at work.
    · simp
    -- A waiter waits on the job at work.
    · intro _; left; rfl
  | jobEnd h =>
    -- The job held the gate, so no writer relieved.
    have hg : s.gate = .job := hj.mpr h
    -- So no writer was relieving.
    have : s.relieving ≠ 1 := fun h' => by rw [hw1.mpr h'] at hg; cases hg
    -- Each fact, with the gate free and the job about to relieve.
    refine ⟨⟨?_, hw2⟩, ?_, ?_⟩
    -- Nobody holds the gate, and nobody relieves.
    · simp; omega
    -- The job no longer holds it.
    · simp
    -- A waiter waits on the job's relief.
    · intro _; right; left; rfl
  | jobRelieveFree h1 h2 =>
    -- Each fact: the gate is free, nobody waits.
    refine ⟨⟨?_, hw2⟩, ?_, ?_⟩
    -- The gate is as it was: free, so no writer relieves.
    · simp only; constructor
      -- A free gate is not a writer's.
      · intro h; rw [h2] at h; cases h
      -- No writer relieves with the gate free.
      · intro h; have := hw1.mpr h; rw [h2] at this; cases this
    -- The gate is free and the job finished.
    · simp [h2]
    -- Nobody waits.
    · intro h; simp at h
  | jobRelieveHeld h1 h2 =>
    -- A writer holds the gate, so a writer is relieving.
    have hrel : s.relieving = 1 := hw1.mp h2
    -- Each fact: only the job changed.
    refine ⟨⟨hw1, hw2⟩, ?_, ?_⟩
    -- The gate is a writer's, and the job is finished.
    · simp [h2]
    -- A waiter waits on the relieving writer.
    · intro _; right; right; exact hrel
  | write h1 h2 =>
    -- Only the writing count changes.
    exact ⟨⟨hw1, hw2⟩, hj, hr⟩
  | relieve h1 h2 h3 =>
    -- The gate was free, so the job was not at work and nobody relieved.
    have hnj : s.job ≠ .holding := fun h => by rw [hj.mpr h] at h3; cases h3
    -- No writer was relieving.
    have h0 : s.relieving ≠ 1 := fun h => by rw [hw1.mpr h] at h3; cases h3
    -- Each fact: the writer holds the gate and relieves.
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    -- A writer's gate and one relieving writer.
    · simp; omega
    -- At most one.
    · simp only; omega
    -- The gate is not the job's, and the job is not at work.
    · simp [hnj]
    -- A waiter waits on the relieving writer.
    · intro _; right; right; simp only; omega
  | wait h1 h2 h3 =>
    -- Each fact: one more waiter, everything else as it was.
    refine ⟨⟨hw1, hw2⟩, hj, ?_⟩
    -- The gate is held: by the job at work, or by a relieving writer.
    intro _
    -- Split on who holds the gate.
    cases hg : s.gate with
    -- Free: ruled out by the step's condition.
    | free => exact absurd hg h3
    -- The job: it is at work.
    | job => left; exact hj.mp hg
    -- A writer: it is relieving.
    | writer => right; right; exact hw1.mp hg
  | step h =>
    -- The relieving writer held the gate, so the job did not.
    have hrel : s.relieving = 1 := by omega
    -- Each fact: the gate is free and nobody waits.
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    -- Nobody holds the gate, nobody relieves.
    · simp; omega
    -- At most one.
    · simp only; omega
    -- The gate is free, and the job was not at work (a writer held it).
    · simp only; constructor
      -- A free gate is not the job's.
      · intro h'; cases h'
      -- The job was not at work: the gate was the writer's, not the job's.
      · intro h'; have := hj.mpr h'; rw [hw1.mpr hrel] at this; cases this
    -- Nobody waits.
    · intro h'; simp at h'

/-- Every reachable state has the facts. -/
theorem inv_reach {s : State} (h : Reach s) : Inv s := by
  -- By how `s` was reached.
  induction h with
  | start n => exact inv_start n
  | step _ hst ih => exact inv_step ih hst

/-- **`job_end_strands_no_waiter`.** Once the job is finished and no writer
is relieving, nobody waits on the stall: someone always lands its unit.
Rules out the story's two writers waiting for ever after the ingest. -/
theorem job_end_strands_no_waiter {s : State} (h : Reach s) (hd : s.job = .done)
    (hr : s.relieving = 0) : s.waiting = 0 := by
  -- The facts of the reachable state.
  have hi := inv_reach h
  -- Either nobody waits, or somebody does.
  rcases Nat.eq_zero_or_pos s.waiting with h0 | hpos
  -- Nobody waits: that is the claim.
  · exact h0
  -- Somebody waits: then the job is at work or relieving, or a writer
  -- relieves, and each of those contradicts what we know.
  · rcases hi.waiter_has_relief hpos with h' | h' | h'
    -- Not at work: it is finished.
    · rw [hd] at h'; cases h'
    -- Not relieving: it is finished.
    · rw [hd] at h'; cases h'
    -- No writer relieves.
    · omega

/-- **`no_relief_strands_waiters`.** With the job ending without relief (bug
`NoRelief`): one writer, the job takes the gate, the writer waits, the job
releases the gate and finishes. The job is done, nobody relieves, and the
writer still waits. -/
theorem no_relief_strands_waiters :
    -- After the three steps of the story.
    let held : State := { start 1 with gate := .job, job := .holding }
    let waited : State := { held with writing := 0, waiting := 1 }
    let ended : State := { waited with gate := .free, job := .done }
    -- The job is finished, nobody relieves, and a writer waits.
    ended.job = .done ∧ ended.relieving = 0 ∧ ended.waiting = 1 := by
  -- Each part is read off the states.
  simp [start]

-- The end of this file's names.
end Regolith.StallRelief
