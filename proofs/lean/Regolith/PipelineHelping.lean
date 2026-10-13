/-!
# PipelineHelping: a stopped thread holds nobody up

This file backs the TLA+ model `proofs/tla/CommitPipeline.tla`, the safety
half of its liveness properties `LockFree` and `EveryLiveCommitCompletes`,
its invariant `NoLiveThreadBlocked`, and its RED `StopHoldsClaim`. The
sequence numbering and the publication order of the same pipeline are in
`Regolith/Pipeline.lean`.

## The story

The commit pipeline keeps commits in a ring of slots (`src/engine/commit`).
Think of a bakery with a ticket machine: every commit pulls a numbered
ticket, and whoever stands at the counter does the next step of the next
order, its own or somebody else's. So a customer who wanders off holds
nobody up: the next one finishes their order for them.

A slot goes through stages. Each step that moves it one stage on may be
taken by any thread whose own slot is the same one or a later one. Each
step has an ordering rule, and every rule looks back only: at the slots
before this one, and at whether the round (the one claim on the log's
device step) is free. None looks at a later slot, and none names a thread.

Tiny example: thread A pulled ticket 1 and stopped for good before writing
its order down. Thread B, at ticket 2, finds ticket 1 empty and throws it
away (that settles it), passes it, and then takes its own commit through
every stage. B never waits for A.

## What is proved, for every number of slots and every mix of stages

1. `first_unfinished_can_step`: with every earlier slot finished and the
   round free, whatever step a slot needs next may be taken.
2. `step_advances`, `no_step_goes_back`: a step moves a slot exactly one
   stage on; no step of any thread moves any slot back.
3. `helper_step_makes_progress`: while work is left, the next step of the
   first unfinished slot is enabled, and taking it leaves exactly one step
   fewer to take.
4. `helper_alone_finishes`: one thread running alone finishes every slot
   up to its own, wherever every other thread stopped: the safety half of
   lock-freedom.
5. `helping_is_bounded` (E21): that takes at most eight steps a slot, so no
   thread serves an unbounded queue of others.
6. `held_round_blocks`: the one exception, stated and proved. A thread that
   stops while it holds the round stops the commits that wait for the
   sync, which is why the pipeline treats the holder as doing device I/O.

What stays in TLA+: that the interleavings of several threads keep
finishing slots (the liveness half). TLC checks it for two and three
threads.

How to read the Lean: `def` defines a function or a property, `theorem`
states a fact and its proof follows `:= by`. Lines starting with `--` are
comments. Inside a proof, each step is commented with what it establishes.
-/

-- Everything below is named Regolith.PipelineHelping.<name>.
namespace Regolith.PipelineHelping

/-! ## The stages of a slot, and the steps between them -/

/-- What kind of order a slot holds. -/
inductive Kind where
  /-- Nothing: the ticket was pulled and its owner went no further. -/
  | empty
  /-- A commit that does not wait for the disk. -/
  | eventual
  /-- A commit that waits for its record to be durable. -/
  | immediate
  /-- A slot that will land nothing: it loses a conflict or is refused. -/
  | abort
  /-- An ordered unit: an ingest's install, a rotation, a close. -/
  | unit
  -- Two such values can be compared for equality.
  deriving DecidableEq

/-- How far a slot has come, in the order the stages are passed. -/
inductive Stage where
  /-- The ticket is pulled; no order is in the cell. -/
  | reserved
  /-- The order is in the cell; it has no verdict. -/
  | ready
  /-- The verdict is installed. -/
  | decided
  /-- Its writes are in the memtable. -/
  | applied
  /-- The tip moved to its verdict. -/
  | tipped
  /-- The decided frontier passed it. -/
  | settled
  /-- Its record is in the log. -/
  | written
  /-- Its record is durable. -/
  | durable
  /-- The read horizon reached its sequence. -/
  | shown
  /-- The published frontier passed it: its owner's call returns. -/
  | finished
  -- Two such values can be compared for equality.
  deriving DecidableEq

/-- The stages as numbers, so that "further on" is "greater". -/
def rank : Stage → Nat
  -- A ticket with no order comes first.
  | .reserved => 0
  -- Then the order is in the cell.
  | .ready => 1
  -- Then it has its verdict.
  | .decided => 2
  -- Then its writes are in the memtable.
  | .applied => 3
  -- Then the tip is at its verdict.
  | .tipped => 4
  -- Then the decided frontier is past it.
  | .settled => 5
  -- Then its record is in the log.
  | .written => 6
  -- Then the record is durable.
  | .durable => 7
  -- Then readers see it.
  | .shown => 8
  -- Then the published frontier is past it.
  | .finished => 9

/-- The steps of the pipeline: what a thread does to a slot. -/
inductive Step where
  /-- Throw away a ticket nobody filled. -/
  | void
  /-- Work out the verdict and install it. -/
  | decide
  /-- Put the writes into the memtable. -/
  | apply
  /-- Move the tip to the verdict. -/
  | moveTip
  /-- Pass the decided frontier over the slot. -/
  | pass
  /-- Write the record at its place in the log. -/
  | write
  /-- Claim the round and sync the written prefix. -/
  | sync
  /-- Raise the read horizon to the slot's sequence. -/
  | raiseHorizon
  /-- Pass the published frontier over the slot. -/
  | passFrontier
  /-- Claim and run an ordered unit. -/
  | runUnit
  -- Two such values can be compared for equality.
  deriving DecidableEq

/-- One slot: what it holds and how far it has come. -/
structure Cell where
  /-- What kind of order it holds. -/
  kind : Kind
  /-- How far it has come. -/
  stage : Stage
  -- Two such values can be compared for equality.
  deriving DecidableEq

/-- The next step of a slot and the stage it leads to, or `none` when the
slot is finished (or its stage is one its kind never passes through). -/
def next (c : Cell) : Option (Step × Stage) :=
  -- By what the slot holds and how far it has come.
  match c.kind, c.stage with
  -- An empty ticket is thrown away, which settles it...
  | .empty, .reserved => some (.void, .settled)
  -- ...and then the published frontier passes it.
  | .empty, .settled => some (.passFrontier, .finished)
  -- A commit that does not wait for the disk gets its verdict...
  | .eventual, .ready => some (.decide, .decided)
  -- ...its writes go into the memtable...
  | .eventual, .decided => some (.apply, .applied)
  -- ...the tip moves to it...
  | .eventual, .applied => some (.moveTip, .tipped)
  -- ...the decided frontier passes it...
  | .eventual, .tipped => some (.pass, .settled)
  -- ...its record is written...
  | .eventual, .settled => some (.write, .written)
  -- ...readers are shown it...
  | .eventual, .written => some (.raiseHorizon, .shown)
  -- ...and the published frontier passes it.
  | .eventual, .shown => some (.passFrontier, .finished)
  -- A commit that waits for the disk gets its verdict...
  | .immediate, .ready => some (.decide, .decided)
  -- ...its writes go into the memtable...
  | .immediate, .decided => some (.apply, .applied)
  -- ...the tip moves to it...
  | .immediate, .applied => some (.moveTip, .tipped)
  -- ...the decided frontier passes it...
  | .immediate, .tipped => some (.pass, .settled)
  -- ...its record is written...
  | .immediate, .settled => some (.write, .written)
  -- ...and synced, which is the step that needs the round...
  | .immediate, .written => some (.sync, .durable)
  -- ...readers are shown it...
  | .immediate, .durable => some (.raiseHorizon, .shown)
  -- ...and the published frontier passes it.
  | .immediate, .shown => some (.passFrontier, .finished)
  -- An abort gets its verdict...
  | .abort, .ready => some (.decide, .decided)
  -- ...the tip moves to it, with nothing to apply...
  | .abort, .decided => some (.moveTip, .tipped)
  -- ...the decided frontier passes it...
  | .abort, .tipped => some (.pass, .settled)
  -- ...and the published frontier passes it, with nothing to write.
  | .abort, .settled => some (.passFrontier, .finished)
  -- An ordered unit is run, which decides and settles it...
  | .unit, .ready => some (.runUnit, .settled)
  -- ...readers are shown what it installed...
  | .unit, .settled => some (.raiseHorizon, .shown)
  -- ...and the published frontier passes it.
  | .unit, .shown => some (.passFrontier, .finished)
  -- Anything else: finished, or not a stage of that kind.
  | _, _ => none

/-- How many steps a slot still needs. -/
def todo (c : Cell) : Nat :=
  -- By what the slot holds and how far it has come.
  match c.kind, c.stage with
  -- An empty ticket: void, then pass.
  | .empty, .reserved => 2
  -- Voided: pass.
  | .empty, .settled => 1
  -- A commit that does not wait for the disk needs seven steps in all.
  | .eventual, .ready => 7
  -- Decided: six left.
  | .eventual, .decided => 6
  -- Applied: five left.
  | .eventual, .applied => 5
  -- The tip moved: four left.
  | .eventual, .tipped => 4
  -- Settled: write, show, pass.
  | .eventual, .settled => 3
  -- Written: show, pass.
  | .eventual, .written => 2
  -- Shown: pass.
  | .eventual, .shown => 1
  -- A commit that waits for the disk needs eight.
  | .immediate, .ready => 8
  -- Decided: seven left.
  | .immediate, .decided => 7
  -- Applied: six left.
  | .immediate, .applied => 6
  -- The tip moved: five left.
  | .immediate, .tipped => 5
  -- Settled: write, sync, show, pass.
  | .immediate, .settled => 4
  -- Written: sync, show, pass.
  | .immediate, .written => 3
  -- Durable: show, pass.
  | .immediate, .durable => 2
  -- Shown: pass.
  | .immediate, .shown => 1
  -- An abort needs four.
  | .abort, .ready => 4
  -- Decided: tip, frontier, pass.
  | .abort, .decided => 3
  -- The tip moved: frontier, pass.
  | .abort, .tipped => 2
  -- Settled: pass.
  | .abort, .settled => 1
  -- An ordered unit needs three.
  | .unit, .ready => 3
  -- Run: show, pass.
  | .unit, .settled => 2
  -- Shown: pass.
  | .unit, .shown => 1
  -- Anything else has nothing left.
  | _, _ => 0

/-- A slot whose stage is one its kind passes through. -/
def WellFormed (c : Cell) : Prop := c.stage = .finished ∨ (next c).isSome = true

/-- Whether a step waits for every earlier slot to be settled (the decided
frontier stands just before this slot). -/
def needsDecided : Step → Bool
  -- Voiding, deciding, applying, the tip and the frontier are all done to
  -- the next slot in line.
  | .void | .decide | .apply | .moveTip | .pass => true
  -- A record is written at its own place, whatever its neighbours do, and
  -- a sync asks nothing of the other slots.
  | .write | .sync => false
  -- Publishing and a unit ask more: see `needsPublished`.
  | .raiseHorizon | .passFrontier | .runUnit => false

/-- Whether a step waits for every earlier slot to be finished (the
published frontier stands just before this slot). -/
def needsPublished : Step → Bool
  -- Publishing goes in ring order, and a unit runs with the pipeline
  -- drained.
  | .raiseHorizon | .passFrontier | .runUnit => true
  -- No other step waits for publication.
  | .void | .decide | .apply | .moveTip | .pass | .write | .sync => false

/-- Whether a step needs the round: the one claim on the log's device
step. -/
def needsRound : Step → Bool
  -- A sync is the device step, and a unit holds the round for the length
  -- of its body.
  | .sync | .runUnit => true
  -- No other step touches the device step.
  | .void | .decide | .apply | .moveTip | .pass | .write | .raiseHorizon | .passFrontier => false

/-- When a step may be taken on a slot, given the slots before it in the
ring and whether the round is free. Nothing here mentions a later slot, and
nothing names a thread: any thread whose own slot is this one or a later
one may take the step. -/
def Enabled (roundFree : Bool) (before : List Cell) (step : Step) : Prop :=
  -- Every earlier slot is settled, if the step waits for that.
  (needsDecided step = true → ∀ b ∈ before, rank .settled ≤ rank b.stage) ∧
  -- Every earlier slot is finished, if the step waits for that.
  (needsPublished step = true → ∀ b ∈ before, b.stage = .finished) ∧
  -- The round is free, if the step needs it.
  (needsRound step = true → roundFree = true)

/-- **The first unfinished slot always has a step.** With every earlier
slot finished and the round free, whatever step the slot needs next may be
taken: every ordering rule is met, because every rule looks back only. -/
theorem first_unfinished_can_step (before : List Cell) (step : Step)
    -- Every slot before this one is finished.
    (hbefore : ∀ b ∈ before, b.stage = .finished) :
    -- The claim itself; its proof follows.
    Enabled true before step := by
  -- The three rules, one by one.
  refine ⟨?_, ?_, ?_⟩
  -- Settled: a finished slot is past settled.
  · intro _ b hb
    -- It is finished...
    rw [hbefore b hb]
    -- ...and finished ranks above settled.
    decide
  -- Finished: take any earlier slot.
  · intro _ b hb
    -- That it is finished is the hypothesis itself.
    exact hbefore b hb
  -- The round: whatever the step needs...
  · intro _
    -- ...the round is free.
    rfl

/-- A slot that is well formed and not finished has a next step. -/
theorem unfinished_has_next (c : Cell)
    -- Its stage is one its kind passes through.
    (hwf : WellFormed c)
    -- It is not finished.
    (hun : c.stage ≠ .finished) : ∃ step st, next c = some (step, st) := by
  -- Well formed means finished, or with a next step.
  cases hwf with
  -- Case: the left alternative holds.
  | inl hfin =>
    -- Finished is ruled out.
    exact absurd hfin hun
  -- Case: the right alternative holds.
  | inr hsome =>
    -- A next step exists: look at what `next` gives.
    match hn : next c with
    -- A step and a stage: those are the ones asked for.
    | some (step, st) => exact ⟨step, st, rfl⟩
    -- Case: there is none.
    | none =>
      -- No next step contradicts the hypothesis.
      simp [hn] at hsome

/-- **A step moves a slot one stage on, and never back.** The stage a step
leads to is further on, the slot then needs exactly one step fewer, and it
is still well formed. -/
theorem step_advances (c : Cell) (step : Step) (st : Stage)
    -- `step` is the slot's next step, and leads to stage `st`.
    (hn : next c = some (step, st)) :
    -- The claim itself; its proof follows.
    rank c.stage < rank st ∧ todo ⟨c.kind, st⟩ + 1 = todo c ∧ WellFormed ⟨c.kind, st⟩ := by
  -- Name the slot's kind and stage.
  obtain ⟨k, s0⟩ := c
  -- Go through every kind and stage: each case is read off the tables.
  cases k <;> cases s0 <;> simp [next] at hn <;> obtain ⟨rfl, rfl⟩ := hn <;>
    -- (Each case then holds by reading the tables.)
    simp [rank, todo, WellFormed, next]

/-- **No step goes back.** Whatever thread takes whatever step on whatever
slot, the slot's stage only moves forward: nobody undoes another thread's
work, so progress made is progress kept. -/
theorem no_step_goes_back (c : Cell) (step : Step) (st : Stage)
    -- `step` is the slot's next step, and leads to stage `st`.
    (hn : next c = some (step, st)) : rank c.stage < rank st :=
  -- The first part of `step_advances`.
  (step_advances c step st hn).1

/-- A finished slot needs nothing more. -/
theorem todo_finished (k : Kind) : todo ⟨k, .finished⟩ = 0 := by
  -- Read off the table, kind by kind.
  cases k <;> rfl

/-- A well-formed slot that needs nothing more is finished. -/
theorem finished_of_todo_zero (c : Cell)
    -- Its stage is one its kind passes through.
    (hwf : WellFormed c)
    -- It needs no step.
    (hz : todo c = 0) : c.stage = .finished := by
  -- Well formed means finished, or with a next step.
  cases hwf with
  -- Case: the left alternative holds.
  | inl hfin =>
    -- Finished: nothing to show.
    exact hfin
  -- Case: the right alternative holds.
  | inr hsome =>
    -- With a next step the slot needs at least one step: name the step.
    match hn : next c with
    -- Case: there is one.
    | some (step, st) =>
      -- Then `todo c` is one more than something...
      have := (step_advances c step st hn).2.1
      -- ...so it is not zero.
      omega
    -- Case: there is none.
    | none =>
      -- No next step contradicts the hypothesis.
      simp [hn] at hsome

/-- The steps the slots of a list still need, in all. -/
def total : List Cell → Nat
  -- No slot, no step.
  | [] => 0
  -- A slot's own steps, and the rest's.
  | c :: rest => todo c + total rest

/-- What one step of a helper does: it takes the next step of the first
slot that is not finished, and leaves every other slot as it is. -/
def helperStep : List Cell → List Cell
  -- No slot, nothing to do.
  | [] => []
  -- Look at the first slot.
  | c :: rest =>
    -- A finished slot is passed over: the step is taken further on.
    if c.stage = .finished then c :: helperStep rest
    -- The first unfinished one moves on, by its next step.
    else match next c with
      -- Its next step leads to stage `st`.
      | some (_, st) => ⟨c.kind, st⟩ :: rest
      -- (A slot with no next step is left as it is.)
      | none => c :: rest

/-- **A helper's step is always there to take, and always counts.** In a
list of well-formed slots with work left, the helper's step is the next
step of the first unfinished slot; that step is enabled when the round is
free (every slot before it is finished); and after it the slots need
exactly one step fewer and are still well formed. -/
theorem helper_step_makes_progress (l : List Cell)
    -- Every slot's stage is one its kind passes through.
    (hwf : ∀ c ∈ l, WellFormed c)
    -- Some step is still needed.
    (hpos : 0 < total l) :
    -- The claim itself; its proof follows.
    total (helperStep l) + 1 = total l ∧ (∀ c ∈ helperStep l, WellFormed c) ∧
      ∃ before c after step st, l = before ++ c :: after ∧
        (∀ b ∈ before, b.stage = .finished) ∧ next c = some (step, st) ∧
        Enabled true before step := by
  -- By induction on the slots.
  induction l with
  -- Case: the empty list.
  | nil =>
    -- No slot needs no step: the hypothesis is false.
    simp [total] at hpos
  -- Case: a first element and then the rest, the claim known for the rest (ih).
  | cons c rest ih =>
    -- The first slot is well formed...
    have hc : WellFormed c := hwf c (List.mem_cons_self)
    -- ...and so are the rest.
    have hrest : ∀ x ∈ rest, WellFormed x := fun x hx => hwf x (List.mem_cons_of_mem _ hx)
    -- Is the first slot finished?
    by_cases hfin : c.stage = .finished
    -- It is, so it needs nothing: the work left is in the rest.
    · have hz : todo c = 0 := by
        -- Name its kind; its stage is `finished`.
        obtain ⟨k, s0⟩ := c
        -- Read the hypothesis as a fact about that stage...
        simp only at hfin
        -- ...put `finished` in its place...
        subst hfin
        -- ...and read the table.
        exact todo_finished k
      -- So the rest has work left.
      have hpos' : 0 < total rest := by
        -- The total is the first slot's none plus the rest's.
        simpa [total, hz] using hpos
      -- The induction step gives the answer for the rest.
      obtain ⟨ht, hw, before, c', after, step, st, hl, hb, hn, he⟩ := ih hrest hpos'
      -- Put the finished slot back in front of each part.
      refine ⟨?_, ?_, c :: before, c', after, step, st, ?_, ?_, hn, ?_⟩
      -- The count: the first slot adds nothing on either side.
      · simp [helperStep, hfin, total, hz, ht]
      -- Well formed: the first slot is unchanged, the rest by induction.
      · intro x hx
        -- `x` is the first slot or one of the stepped rest.
        simp [helperStep, hfin] at hx
        -- Either way it is well formed.
        cases hx with
        -- The first slot: by hypothesis.
        | inl h => exact h ▸ hc
        -- One of the rest: by induction.
        | inr h => exact hw x h
      -- The list splits at the same slot, one place later.
      · simp [hl]
      -- Every slot before it is finished: the first one, and the others.
      · intro b hb'
        -- `b` is the first slot or one of `before`.
        simp at hb'
        -- Look at which.
        cases hb' with
        -- The first slot is finished: that is this case.
        | inl h => exact h ▸ hfin
        -- One of `before` is finished by induction.
        | inr h => exact hb b h
      -- The step is enabled: every slot before it is finished.
      · exact first_unfinished_can_step (c :: before) step (by
          -- Take any slot before it.
          intro b hb'
          -- It is the first slot or one of `before`.
          simp at hb'
          -- Look at which.
          cases hb' with
          -- The first slot is finished: that is this case.
          | inl h => exact h ▸ hfin
          -- One of `before` is finished by induction.
          | inr h => exact hb b h)
    -- It is not: it is the first unfinished slot, and has a next step.
    · obtain ⟨step, st, hn⟩ := unfinished_has_next c hc hfin
      -- That step moves it one stage on.
      obtain ⟨_, htodo, hwf'⟩ := step_advances c step st hn
      -- Nothing stands before it.
      refine ⟨?_, ?_, [], c, rest, step, st, rfl, ?_, hn, ?_⟩
      -- The count: unfold the helper's step and the totals.
      · simp [helperStep, hfin, hn, total]
        -- This slot needs one step fewer, the rest the same.
        omega
      -- Well formed: take any slot after the step.
      · intro x hx
        -- `x` is the stepped slot or one of the rest.
        simp [helperStep, hfin, hn] at hx
        -- Look at which.
        cases hx with
        -- The stepped slot: by `step_advances`.
        | inl h => exact h ▸ hwf'
        -- One of the rest: as before.
        | inr h => exact hrest x h
      -- No slot is before it: suppose there were one.
      · intro b hb
        -- The empty list has no member.
        simp at hb
      -- The step is enabled: there is nothing before it to wait for.
      · exact first_unfinished_can_step [] step (by
          -- Suppose there were a slot before it.
          intro b hb
          -- The empty list has no member.
          simp at hb)

/-- `run n l`: the slots after `n` steps of one helper. -/
def run : Nat → List Cell → List Cell
  -- No step: the slots as they are.
  | 0, l => l
  -- One step, then the rest.
  | n + 1, l => run n (helperStep l)

/-- When no step is needed, every slot is finished. -/
theorem all_finished_of_total_zero (l : List Cell)
    -- Every slot's stage is one its kind passes through.
    (hwf : ∀ c ∈ l, WellFormed c)
    -- No step is needed.
    (hz : total l = 0) : ∀ c ∈ l, c.stage = .finished := by
  -- By induction on the slots.
  induction l with
  -- Case: the empty list.
  | nil =>
    -- No slot: suppose there were one.
    intro c hc
    -- The empty list has no member.
    simp at hc
  -- Case: a first element and then the rest, the claim known for the rest (ih).
  | cons c rest ih =>
    -- The first slot needs nothing...
    have h1 : todo c = 0 := by
      -- The total is its steps plus the rest's...
      simp [total] at hz
      -- ...and a sum that is zero has zero parts.
      omega
    -- ...and neither does the rest.
    have h2 : total rest = 0 := by
      -- The same sum...
      simp [total] at hz
      -- ...and the same arithmetic.
      omega
    -- Take any slot of the list.
    intro x hx
    -- It is the first slot or one of the rest.
    simp at hx
    -- Look at which.
    cases hx with
    -- Case: the left alternative holds.
    | inl h =>
      -- The first: well formed and needing nothing, so finished.
      exact h ▸ finished_of_todo_zero c (hwf c (List.mem_cons_self)) h1
    -- Case: the right alternative holds.
    | inr h =>
      -- One of the rest: by induction.
      exact ih (fun y hy => hwf y (List.mem_cons_of_mem _ hy)) h2 x h

/-- **One live thread alone finishes every slot up to its own** (the
safety half of lock-freedom). Take the slots of the ring up to a thread's
own, each at any stage at all: the others may have stopped anywhere. With
the round free, that thread's own steps, `total l` of them and each one
enabled when it is taken, leave every slot finished: its own commit
returns. No other thread has to take a step. -/
theorem helper_alone_finishes (l : List Cell)
    -- Every slot's stage is one its kind passes through.
    (hwf : ∀ c ∈ l, WellFormed c) : ∀ c ∈ run (total l) l, c.stage = .finished := by
  -- By induction on the number of steps needed, for every list of slots.
  generalize hn : total l = n
  -- Induct on that number, for every list of slots.
  induction n generalizing l with
  -- Case: zero.
  | zero =>
    -- No step needed: every slot is finished already.
    exact all_finished_of_total_zero l hwf hn
  -- Case: one more, the claim known for the number before (ih).
  | succ n ih =>
    -- Work is left...
    have hpos : 0 < total l := by omega
    -- ...so the helper's step counts, and leaves the slots well formed.
    obtain ⟨ht, hw, _⟩ := helper_step_makes_progress l hwf hpos
    -- After it, `n` steps are needed, and the induction step applies.
    exact ih (helperStep l) hw (by omega)

/-- A slot never needs more than eight steps. -/
theorem todo_le (c : Cell) : todo c ≤ 8 := by
  -- Name its kind and stage.
  obtain ⟨k, s0⟩ := c
  -- Read the table case by case.
  cases k <;> cases s0 <;> simp [todo]

/-- **Helping is bounded** (E21). The steps one thread takes for the slots
up to its own, other threads' slots included, are at most eight a slot:
no thread serves an unbounded queue of others. -/
theorem helping_is_bounded (l : List Cell) : total l ≤ 8 * l.length := by
  -- By induction on the slots.
  induction l with
  -- Case: the empty list.
  | nil =>
    -- No slot, no step.
    simp [total]
  -- Case: a first element and then the rest, the claim known for the rest (ih).
  | cons c rest ih =>
    -- The first slot needs at most eight.
    have := todo_le c
    -- The total is its steps plus the rest's, and the list is one longer.
    simp [total]
    -- The rest is bounded by induction; add the two bounds.
    omega

/-- **The stated limit: a held round blocks the sync.** With the round not
free, the sync an Immediate commit waits for cannot be taken, however far
every other slot has come. A thread that stops while it holds the round
therefore stops the commits that need it, which is why the pipeline treats
the holder as doing device I/O (TLA+ RED `StopHoldsClaim`). -/
theorem held_round_blocks (before : List Cell) : ¬ Enabled false before .sync := by
  -- Suppose the sync were enabled.
  intro h
  -- Its third rule says the round is free; it is not.
  have := h.2.2 rfl
  -- `false = true` is absurd.
  exact Bool.noConfusion this

-- The end of this file's names.
end Regolith.PipelineHelping
