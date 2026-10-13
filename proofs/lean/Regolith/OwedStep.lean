/-!
# OwedStep: with no worker, each write runs one owed step and L0 stays bounded (E16)

This file backs the TLA+ model `proofs/tla/OwedStep.tla`, invariants
`OneStepPerWrite`, `ExactlyTheOwedStep`, `L0Bounded` and `FrozenBounded`
(configurations `MC_OwedStep_*`). The model checks two small sizes; this
file proves the laws for every memtable size, every trigger and every run.

## The story, with a tiny example

regolith keeps new writes in memory, in a "memtable". When the memtable is
full it is "sealed" and must be written out to a file: a "flush". Flushed
files land in "L0", the top level of the tree, and when L0 holds too many
files they are merged into the next level: a "compaction". Reads look at
every L0 file, so a growing L0 makes every read slower.

Usually a background thread (the "worker") flushes and compacts. A database
opened with no worker (for example on a wasm target that has no threads)
has nobody to do that. So the writes do it: a write that seals a memtable
leaves one step of background work "owed", and the next write to finish
its commit runs exactly one step, then returns
(`RegolithEngine::run_owed_step`, `src/engine/background_step.rs`). One step
is one flush of the oldest sealed memtable, or, when nothing is sealed, one
compaction pass. A step that did work owes the next one.

Example, with a memtable of two writes and a trigger of two L0 files:
write 2 seals and flushes (L0 = 1); write 3 runs a pass that finds nothing
to do; write 4 seals and flushes (L0 = 2, the trigger); write 5 runs a
pass, which compacts L0 (L0 = 0). L0 never passes 2, and no write runs more
than one step.

What could go wrong (E16): before the fix a flush owed nothing, so after
the flush that brought L0 to its trigger nobody compacted, and L0 grew
until writes were stopped. And a write that kept running steps until
nothing was owed would pay for a flush and a compaction and more, all in
one call.

## What is proved, in plain words

1. `write_one_step`: a write runs one step when one is owed as it leaves
   the commit pipeline, and none otherwise. Never more than one.
2. `write_inv`, `run_inv`, `l0_bounded`: when a memtable holds at least
   two writes, after any number of writes L0 holds at most `T` files (the
   compaction trigger) and no sealed memtable is left waiting.
3. `stopped_write_inv`, `l0_bounded_by_stop`: for any memtable size, even
   one write per memtable, L0 never passes the stop trigger `P`: a write
   that finds L0 there first runs the step that compacts it.
4. `flush_owes_nothing_overfills` and `step_until_idle_runs_three`: the two
   RED cases, as counterexamples.

## What the proof leaves out

Several threads writing at once. A step can then find another thread
doing the work and do nothing, and writes can outrun the one thread that
works; the bound on L0 is then the stop trigger's, and the stop's relief
is `StallRelief.lean`. Here one write runs at a time, which is the case of
a database with no worker used from one thread.

How to read the Lean: `def` defines a function or a property, `theorem`
states a fact and its proof follows `:= by`. Lines starting with `--` are
comments. `{ s with a := x }` is the state `s` with its field `a` set to `x`.
-/

-- Everything below is named Regolith.OwedStep.<name>.
namespace Regolith.OwedStep

/-! ## The state and the steps -/

/-- What the argument is about. -/
structure St where
  /-- How many writes the active memtable holds. -/
  filled : Nat
  /-- How many sealed memtables wait for their flush (`ReadView::frozen`). -/
  frozen : Nat
  /-- How many files L0 holds. -/
  l0 : Nat
  /-- Whether one step of background work is owed (`OWED_STEP` in
  `RegolithEngine::owed`). -/
  owed : Bool
  -- Lean may decide whether two states are equal, so the examples at the end can be computed.
  deriving DecidableEq

/-- The start: an empty memtable, nothing sealed, an empty L0, nothing owed. -/
def init : St := ⟨0, 0, 0, false⟩

/-- A write goes through the commit pipeline. A memtable holds `S` writes:
the write that fills it seals it, which owes one step
(`RegolithEngine::flush_sealed_later`). -/
def commit (S : Nat) (s : St) : St :=
  -- The write that fills the memtable: a fresh memtable, one more sealed, a step owed.
  if s.filled + 1 = S then { s with filled := 0, frozen := s.frozen + 1, owed := true }
  -- Any other write: one more write in the memtable.
  else { s with filled := s.filled + 1 }

/-- One bounded step of background work
(`RegolithEngine::run_one_background_step`), run as the owed step. `T` is
the compaction trigger. `deeper` says whether a pass that leaves L0 alone
found work in a deeper level; such a pass did work, so it owes the next
step. -/
def bgStep (T : Nat) (deeper : Bool) (s : St) : St :=
  -- A sealed memtable waits: flush the oldest. One file more in L0, and the flush owes a step.
  if 0 < s.frozen then { s with frozen := s.frozen - 1, l0 := s.l0 + 1, owed := true }
  -- Nothing sealed and L0 at its trigger: the pass merges all of L0 away, and owes a step.
  else if T ≤ s.l0 then { s with l0 := 0, owed := true }
  -- Nothing sealed and L0 below its trigger: L0 is left alone.
  else { s with owed := deeper }

/-- What a write does once its commit returned (`run_owed`): if a step is
owed, it takes the debt and runs exactly one step. The second component is
how many steps ran. -/
def runOwed (T : Nat) (deeper : Bool) (s : St) : St × Nat :=
  -- A step is owed: clear the debt, run one step, count one. Otherwise run nothing.
  if s.owed then (bgStep T deeper { s with owed := false }, 1) else (s, 0)

/-- One whole write: the commit, then the owed step if any. -/
def write (S T : Nat) (deeper : Bool) (s : St) : St × Nat :=
  -- First the commit, then what it left owing.
  runOwed T deeper (commit S s)

/-! ## One step per write -/

/-- **`write_one_step`.** A write runs one step when one is owed as its
commit returns, and none otherwise: never more than one. TLA+:
`OneStepPerWrite`, `ExactlyTheOwedStep`. Example ruled out: a write that
seals, flushes, compacts and compacts again before it returns. -/
theorem write_one_step (S T : Nat) (deeper : Bool) (s : St) :
    -- The statement: the steps run are 1 if a step is owed after the commit, else 0.
    (write S T deeper s).2 = (if (commit S s).owed then 1 else 0) := by
  -- Unfold the write: it is `runOwed` on the state after the commit.
  unfold write runOwed
  -- Split on whether a step is owed; each side counts what the claim says.
  split <;> simp_all

/-! ## L0 stays at its trigger -/

/-- What holds after every write, when a memtable holds at least two writes. -/
structure Inv (S T : Nat) (s : St) : Prop where
  /-- No sealed memtable is left waiting. -/
  none_frozen : s.frozen = 0
  /-- The active memtable is not full. -/
  room : s.filled < S
  /-- L0 holds at most `T` files. -/
  l0_le : s.l0 ≤ T
  /-- When L0 is at its trigger, a step is owed and the memtable is fresh:
  the next write does not seal, and its step compacts L0. -/
  full_owes : s.l0 = T → s.owed = true ∧ s.filled = 0

/-- The start satisfies the invariant. -/
theorem inv_init {S T : Nat}
    -- A memtable holds at least two writes.
    (hS : 2 ≤ S)
    -- The trigger is at least one file.
    (hT : 1 ≤ T) :
    -- The statement: the invariant holds at the start.
    Inv S T init := by
  -- Nothing is sealed and L0 is empty; two facts are left.
  refine ⟨rfl, ?_, Nat.zero_le _, ?_⟩
  -- The empty memtable has room.
  · show 0 < S
    -- Arithmetic: S is at least 2.
    omega
  -- L0 is not at its trigger: suppose it were.
  · intro h
    -- Then the trigger would be 0.
    have : (0 : Nat) = T := h
    -- But it is at least 1.
    omega

/-- **Every write keeps the invariant.** -/
theorem write_inv {S T : Nat}
    -- A memtable holds at least two writes.
    (hS : 2 ≤ S)
    -- The trigger is at least one file.
    (hT : 1 ≤ T)
    -- Whatever a pass finds in the deeper levels.
    (deeper : Bool) {s : St}
    -- The invariant holds before the write.
    (hs : Inv S T s) :
    -- The statement: it holds after the write.
    Inv S T (write S T deeper s).1 := by
  -- Take the invariant apart into its four facts.
  obtain ⟨hfz, hfl, hl0, hfull⟩ := hs
  -- Does this write fill the memtable?
  by_cases hseal : s.filled + 1 = S
  -- It does: the write seals.
  · have hlt : s.l0 < T := by
      -- L0 is below its trigger or at it.
      rcases Nat.lt_or_ge s.l0 T with h | h
      -- Below: that is the claim.
      · exact h
      -- At it: then the memtable would be fresh,
      · have := (hfull (Nat.le_antisymm hl0 h)).2
        -- but a fresh memtable of two or more writes is not filled by one write.
        omega
    -- What the write leaves: a fresh memtable, the sealed one flushed, one file more, a step owed.
    have hw : (write S T deeper s).1 =
        { s with filled := 0, frozen := 0, l0 := s.l0 + 1, owed := true } := by
      -- Compute: the commit seals, a step is owed, and the step flushes.
      simp [write, commit, runOwed, bgStep, hseal, hfz]
    -- State the goal for that state.
    rw [hw]
    -- Nothing sealed; room in the fresh memtable; L0 at most the trigger; a step owed.
    exact ⟨rfl, by show 0 < S; omega, by show s.l0 + 1 ≤ T; omega, fun _ => ⟨rfl, rfl⟩⟩
  -- It does not: the write only adds to the memtable, which still has room.
  · have hroom : s.filled + 1 < S := by omega
    -- Is a step owed?
    by_cases hown : s.owed = true
    -- A step is owed, and nothing is sealed: it is a compaction pass. Is L0 at its trigger?
    · by_cases hfull' : T ≤ s.l0
      -- At its trigger: the pass merges L0 away.
      · have hw : (write S T deeper s).1 =
            { s with filled := s.filled + 1, l0 := 0, owed := true } := by
          -- Compute: no seal, a step owed, nothing sealed, L0 at its trigger.
          simp [write, commit, runOwed, bgStep, hseal, hfz, hown, hfull']
        -- State the goal for that state.
        rw [hw]
        -- Nothing sealed; room; an empty L0, which is not at a trigger of one or more.
        exact ⟨hfz, hroom, Nat.zero_le _, fun h => by have : (0 : Nat) = T := h; omega⟩
      -- Below its trigger: the pass leaves L0 alone.
      · have hw : (write S T deeper s).1 =
            { s with filled := s.filled + 1, owed := deeper } := by
          -- Compute: no seal, a step owed, nothing sealed, L0 below its trigger.
          simp [write, commit, runOwed, bgStep, hseal, hfz, hown, hfull']
        -- State the goal for that state.
        rw [hw]
        -- Nothing sealed; room; L0 as before, still below its trigger.
        exact ⟨hfz, hroom, hl0, fun h => by have : s.l0 = T := h; omega⟩
    -- No step is owed: spell that out as "owed = false".
    · have hno : s.owed = false := by
        -- Look at the flag.
        cases h : s.owed with
        -- False: that is the claim.
        | false => rfl
        -- True: but it is not.
        | true => exact absurd h hown
      -- Then L0 is not at its trigger, where a step would be owed.
      have hne : s.l0 ≠ T := fun h => by
        -- At the trigger a step is owed,
        have := (hfull h).1
        -- and none is.
        rw [hno] at this
        -- "false = true" is impossible.
        cases this
      -- What the write leaves: one more write in the memtable, nothing else.
      have hw : (write S T deeper s).1 = { s with filled := s.filled + 1 } := by
        -- Compute: no seal, and nothing owed, so no step.
        simp [write, commit, runOwed, hseal, hno]
      -- State the goal for that state.
      rw [hw]
      -- Nothing sealed; room; L0 as before, and not at its trigger.
      exact ⟨hfz, hroom, hl0, fun h => absurd h hne⟩

/-- Any number of writes, one after another. Each entry of the list says
what that write's pass found in the deeper levels. -/
def run (S T : Nat) : List Bool → St → St
  -- No write: the state as it is.
  | [], s => s
  -- One write, then the rest.
  | d :: ds, s => run S T ds (write S T d s).1

/-- Any number of writes keep the invariant. -/
theorem run_inv {S T : Nat}
    -- A memtable holds at least two writes.
    (hS : 2 ≤ S)
    -- The trigger is at least one file.
    (hT : 1 ≤ T)
    -- The writes.
    (ds : List Bool) {s : St}
    -- The invariant holds before them.
    (hs : Inv S T s) :
    -- The statement: it holds after them.
    Inv S T (run S T ds s) := by
  -- Go through the writes one at a time, from any starting state.
  induction ds generalizing s with
  -- No write: nothing changed.
  | nil => exact hs
  -- One write keeps the invariant, and the rest follow from the state it leaves.
  | cons d ds ih => exact ih (write_inv hS hT d hs)

/-- **`l0_bounded`.** With no worker, a memtable of at least two writes and
any trigger, after any number of writes L0 holds at most `T` files and no
sealed memtable is left waiting. TLA+: `L0Bounded`, `FrozenBounded`. Example
ruled out: a trigger of 2 and an L0 of 3, 4, 5 files, growing with every
flush until the database stops writes. -/
theorem l0_bounded {S T : Nat}
    -- A memtable holds at least two writes.
    (hS : 2 ≤ S)
    -- The trigger is at least one file.
    (hT : 1 ≤ T)
    -- The writes.
    (ds : List Bool) :
    -- The statement: L0 is at most the trigger, and nothing sealed waits.
    (run S T ds init).l0 ≤ T ∧ (run S T ds init).frozen = 0 :=
  -- The invariant holds after the writes.
  let h := run_inv hS hT ds (inv_init hS hT)
  -- Read off two of its facts.
  ⟨h.l0_le, h.none_frozen⟩

/-! ## Any memtable size: the stop trigger is the bound -/

/-- The step a stopped write runs to relieve the stop
(`RegolithEngine::relieve_inline`): the same background step, not run as
the owed step. A flush still owes a step; a compaction pass leaves the debt
as it is. -/
def relieveStep (T : Nat) (s : St) : St :=
  -- A sealed memtable waits: flush the oldest.
  if 0 < s.frozen then { s with frozen := s.frozen - 1, l0 := s.l0 + 1, owed := true }
  -- Nothing sealed and L0 at its trigger: the pass merges all of L0 away.
  else if T ≤ s.l0 then { s with l0 := 0 }
  -- Nothing to do.
  else s

/-- A write on a database whose stop trigger is `P`: a write that finds L0
at `P` is stopped and first relieves the stop; then it writes. -/
def writeStopped (S T P : Nat) (deeper : Bool) (s : St) : St :=
  -- Stopped: one relieving step first. Then the write and its owed step.
  (write S T deeper (if P ≤ s.l0 then relieveStep T s else s)).1

/-- What holds after every write, for any memtable size. -/
structure InvStop (S P : Nat) (s : St) : Prop where
  /-- No sealed memtable is left waiting. -/
  none_frozen : s.frozen = 0
  /-- The active memtable is not full. -/
  room : s.filled < S
  /-- L0 holds at most `P` files. -/
  l0_le : s.l0 ≤ P

/-- **Every write keeps L0 within the stop trigger**, whatever the memtable
size. -/
theorem stopped_write_inv {S T P : Nat}
    -- The compaction trigger is at least one file,
    (hT : 1 ≤ T)
    -- and the stop trigger is not below it.
    (hTP : T ≤ P)
    -- Whatever a pass finds in the deeper levels.
    (deeper : Bool) {s : St}
    -- The invariant holds before the write.
    (hs : InvStop S P s) :
    -- The statement: it holds after the write.
    InvStop S P (writeStopped S T P deeper s) := by
  -- Take the invariant apart into its three facts.
  obtain ⟨hfz, hfl, hl0⟩ := hs
  -- The state the write starts from, after the relief if it was stopped: call it u.
  -- It has nothing sealed, room in its memtable, and an L0 strictly below the stop trigger.
  have hu : ∃ u : St, (if P ≤ s.l0 then relieveStep T s else s) = u ∧
      u.frozen = 0 ∧ u.filled = s.filled ∧ u.l0 < P := by
    -- Was the write stopped?
    by_cases hstop : P ≤ s.l0
    -- Stopped: nothing is sealed and L0 is at its trigger, so the relief empties L0.
    · refine ⟨{ s with l0 := 0 }, ?_, hfz, rfl, ?_⟩
      -- Compute the relieving step.
      · simp [relieveStep, hstop, hfz, Nat.le_trans hTP hstop]
      -- An empty L0 is below a stop trigger of one or more.
      · show 0 < P
        -- Arithmetic.
        omega
    -- Not stopped: the state as it is, with L0 below the stop trigger.
    · exact ⟨s, by simp [hstop], hfz, rfl, by omega⟩
  -- Name that state and its facts.
  obtain ⟨u, hueq, hufz, hufl, hul0⟩ := hu
  -- The write runs from u.
  have hgoal : writeStopped S T P deeper s = (write S T deeper u).1 := by
    -- Unfold, and put u for the state after the relief.
    simp only [writeStopped, hueq]
  -- State the goal for the write from u.
  rw [hgoal]
  -- Does the write fill the memtable?
  by_cases hseal : u.filled + 1 = S
  -- It seals: its owed step flushes, one file more in L0.
  · have hw : (write S T deeper u).1 =
        { u with filled := 0, frozen := 0, l0 := u.l0 + 1, owed := true } := by
      -- Compute: the commit seals, a step is owed, and the step flushes.
      simp [write, commit, runOwed, bgStep, hseal, hufz]
    -- State the goal for that state.
    rw [hw]
    -- Nothing sealed; room in the fresh memtable; L0 at most the stop trigger.
    exact ⟨rfl, by show 0 < S; omega, by show u.l0 + 1 ≤ P; omega⟩
  -- It does not seal: the memtable still has room.
  · have hroom : u.filled + 1 < S := by omega
    -- Is a step owed?
    by_cases hown : u.owed = true
    -- A step is owed, and nothing is sealed: a pass. Is L0 at its trigger?
    · by_cases hfull' : T ≤ u.l0
      -- At its trigger: the pass merges L0 away.
      · have hw : (write S T deeper u).1 =
            { u with filled := u.filled + 1, l0 := 0, owed := true } := by
          -- Compute: no seal, a step owed, nothing sealed, L0 at its trigger.
          simp [write, commit, runOwed, bgStep, hseal, hufz, hown, hfull']
        -- State the goal for that state.
        rw [hw]
        -- Nothing sealed; room; an empty L0.
        exact ⟨hufz, hroom, Nat.zero_le _⟩
      -- Below its trigger: the pass leaves L0 alone.
      · have hw : (write S T deeper u).1 =
            { u with filled := u.filled + 1, owed := deeper } := by
          -- Compute: no seal, a step owed, nothing sealed, L0 below its trigger.
          simp [write, commit, runOwed, bgStep, hseal, hufz, hown, hfull']
        -- State the goal for that state.
        rw [hw]
        -- Nothing sealed; room; L0 as it was, below the stop trigger.
        exact ⟨hufz, hroom, Nat.le_of_lt hul0⟩
    -- No step is owed: spell that out as "owed = false".
    · have hno : u.owed = false := by
        -- Look at the flag.
        cases h : u.owed with
        -- False: that is the claim.
        | false => rfl
        -- True: but it is not.
        | true => exact absurd h hown
      -- What the write leaves: one more write in the memtable, nothing else.
      have hw : (write S T deeper u).1 = { u with filled := u.filled + 1 } := by
        -- Compute: no seal, and nothing owed, so no step.
        simp [write, commit, runOwed, hseal, hno]
      -- State the goal for that state.
      rw [hw]
      -- Nothing sealed; room; L0 as it was, below the stop trigger.
      exact ⟨hufz, hroom, Nat.le_of_lt hul0⟩

/-- Any number of writes on a database with stop trigger `P`. -/
def runStopped (S T P : Nat) : List Bool → St → St
  -- No write: the state as it is.
  | [], s => s
  -- One write, then the rest.
  | d :: ds, s => runStopped S T P ds (writeStopped S T P d s)

/-- **`l0_bounded_by_stop`.** With no worker and any memtable size, even one
write per memtable, after any number of writes L0 holds at most `P` files,
the stop trigger, and no sealed memtable is left waiting. Example ruled
out: an L0 that grows for ever because every write seals and every step
flushes. -/
theorem l0_bounded_by_stop {S T P : Nat}
    -- A memtable holds at least one write.
    (hS : 1 ≤ S)
    -- The compaction trigger is at least one file,
    (hT : 1 ≤ T)
    -- and the stop trigger is not below it.
    (hTP : T ≤ P)
    -- The writes.
    (ds : List Bool) :
    -- The statement: L0 is at most the stop trigger, and nothing sealed waits.
    (runStopped S T P ds init).l0 ≤ P ∧ (runStopped S T P ds init).frozen = 0 := by
  -- The invariant holds after any writes from any state that satisfies it.
  have hrun : ∀ (ds : List Bool) (s : St), InvStop S P s → InvStop S P (runStopped S T P ds s) := by
    -- Take the writes.
    intro ds
    -- Go through them one at a time, from any starting state.
    induction ds with
    -- No write: nothing changed.
    | nil => exact fun s hs => hs
    -- One write keeps the invariant, and the rest follow from the state it leaves.
    | cons d ds ih => exact fun s hs => ih _ (stopped_write_inv hT hTP d hs)
  -- The start satisfies it: nothing sealed, room in the empty memtable, an empty L0.
  have h0 : InvStop S P init := ⟨rfl, by show 0 < S; omega, Nat.zero_le _⟩
  -- So it holds after the writes.
  have h := hrun ds init h0
  -- Read off two of its facts.
  exact ⟨h.l0_le, h.none_frozen⟩

/-! ## The RED cases, as counterexamples -/

/-- The step before E16: a flush owes nothing. -/
def bgStepForget (T : Nat) (deeper : Bool) (s : St) : St :=
  -- The defect: the flush leaves no step owed.
  if 0 < s.frozen then { s with frozen := s.frozen - 1, l0 := s.l0 + 1, owed := false }
  -- A pass with L0 at its trigger, as in the design.
  else if T ≤ s.l0 then { s with l0 := 0, owed := true }
  -- A pass with L0 below its trigger, as in the design.
  else { s with owed := deeper }

/-- One write under that defect. -/
def writeForget (S T : Nat) (deeper : Bool) (s : St) : St :=
  -- The commit, then one step if one is owed.
  if (commit S s).owed then bgStepForget T deeper { commit S s with owed := false } else commit S s

/-- Any number of writes under that defect. -/
def runForget (S T : Nat) : List Bool → St → St
  -- No write: the state as it is.
  | [], s => s
  -- One write, then the rest.
  | d :: ds, s => runForget S T ds (writeForget S T d s)

/-- **`flush_owes_nothing_overfills`.** With a memtable of two writes and a
trigger of two files, six writes under the defect leave three files in L0:
each second write seals and flushes, and no write ever runs a compaction
pass, because nothing is owed after a flush. TLA+:
`MC_OwedStep_Red_FlushOwesNothing` breaks `L0Bounded`. -/
theorem flush_owes_nothing_overfills :
    -- The statement: L0 holds three files, one more than the trigger.
    (runForget 2 2 [false, false, false, false, false, false] init).l0 = 3 := by
  -- Settled by computing the six writes.
  decide

/-- The defect "step until idle": a write keeps running steps while one is
owed. `fuel` bounds the loop so Lean accepts the definition; the second
component counts the steps. -/
def runOwedLoop (T : Nat) : Nat → St → St × Nat
  -- Out of fuel: stop.
  | 0, s => (s, 0)
  -- Fuel left:
  | fuel + 1, s =>
    -- is a step owed?
    if s.owed then
      -- Yes: run one step, then go round again ...
      let r := runOwedLoop T fuel (bgStep T false { s with owed := false })
      -- ... and count this step.
      (r.1, r.2 + 1)
    -- No: stop.
    else (s, 0)

/-- **`step_until_idle_runs_three`.** With a trigger of two files and one
file in L0, the write that seals a memtable runs three steps under the
defect: the flush (L0 reaches its trigger), the compaction it now owes, and
a pass that finds nothing more. The design runs one (`write_one_step`).
TLA+: `MC_OwedStep_Red_StepUntilIdle` breaks `OneStepPerWrite`. -/
theorem step_until_idle_runs_three :
    -- The statement: from a memtable one write short of full and one file in L0, the loop runs
    -- three steps.
    (runOwedLoop 2 8 (commit 2 ⟨1, 0, 1, false⟩)).2 = 3 := by
  -- Settled by computing the loop.
  decide

-- End of the namespace opened at the top.
end Regolith.OwedStep
