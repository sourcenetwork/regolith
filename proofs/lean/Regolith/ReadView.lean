/-!
# ReadView: a wait-free read view that is never freed under a reader

This file backs the TLA+ model `proofs/tla/ReadView.tla`, invariants
`NoFreedRead`, `FreshLoad` and `ChainOfPublications` (configurations
`MC_ReadView_*`).

## The story

Every read in regolith asks one cell "which memtables and table files make
up the database now?" (`ReadViewCell`, `src/engine/read_view.rs`). A
reader pins itself, loads the cell's pointer, uses the view, and unpins. A
writer builds a new view from the current one and swaps it in with one
compare-and-swap; the view it replaced is retired, and the reclaimer frees
a retired view only once every reader that was pinned when it was retired
has unpinned.

Tiny example: reader 0 pins and loads view 1. A writer swaps in view 2 and
retires view 1, noting that reader 0 is pinned. The reclaimer may not free
view 1 until reader 0 unpins. Reader 0 reads view 1 safely the whole time.

## What is proved, for any number of readers and publications

1. `reachable_safe`: in every state the system can reach, a reader that
   holds a view holds one that is not freed (`NoFreedRead`), and that view
   is at least as new as what was published when its load began
   (`FreshLoad`).
2. `cas_chain`: applying any list of publication attempts by
   compare-and-swap, every attempt that goes in was built from exactly the
   view it replaced (`ChainOfPublications`).
3. The RED cases as concrete counterexamples: freeing at retirement frees a
   view a reader holds (`free_early_breaks`), a store without the CAS loses
   a publication (`plain_store_breaks`), and a reader that reuses its last
   view reads one older than what was published (`stale_load_breaks`).
-/

namespace Regolith.ReadView

/-- `upd f a b` is the function `f` with its value at `a` replaced by `b`:
the model's way of changing one reader's or one view's entry. -/
def upd {α : Type} (f : Nat → α) (a : Nat) (b : α) : Nat → α :=
  -- At `a` the new value; everywhere else, what `f` said.
  fun x => if x = a then b else f x

/-- Reading `upd f a b` at `a` gives `b`. -/
@[simp] theorem upd_same {α : Type} (f : Nat → α) (a : Nat) (b : α) : upd f a b a = b := by
  -- Unfold `upd`; the `if` takes its true branch.
  simp [upd]

/-- Reading `upd f a b` anywhere else gives what `f` said. -/
@[simp] theorem upd_other {α : Type} (f : Nat → α) {a x : Nat} (b : α) (h : x ≠ a) :
    upd f a b x = f x := by
  -- Unfold `upd`; the `if` takes its false branch because `x ≠ a`.
  simp [upd, h]

/-- A reader's progress, as in `ReadView.tla`: idle, pinned (its
`ViewGuard` is being made), or holding a view. -/
inductive RState where
  /-- Not reading. -/
  | idle
  /-- Pinned: kovan counts it, it has not loaded yet. -/
  | pinned
  /-- Holding a loaded view: a `ViewGuard` is alive. -/
  | holding
  deriving DecidableEq

/-- Everything the model tracks. Readers and views are numbered. -/
structure State where
  /-- The view the cell holds now (`ReadViewCell::current`). -/
  published : Nat
  /-- How many views have been built: views are numbered 1, 2, ... in the
  order they are built. -/
  made : Nat
  /-- `retired v`: view `v` was replaced and handed to the reclaimer. -/
  retired : Nat → Bool
  /-- `freed v`: view `v`'s memory was given back. -/
  freed : Nat → Bool
  /-- `waitFor v r`: the reclaimer still waits for reader `r` before it
  may free view `v`. -/
  waitFor : Nat → Nat → Bool
  /-- Each reader's progress. -/
  rstate : Nat → RState
  /-- The view each reader holds (0 when it holds none). -/
  rview : Nat → Nat
  /-- What was published when each reader pinned: the view its load must
  not be older than. -/
  rfloor : Nat → Nat

/-- The start: view 1 published, nothing retired, nobody reading. -/
def init : State where
  -- The engine opened with view 1 in the cell ...
  published := 1
  -- ... the only view built so far.
  made := 1
  -- Nothing has been replaced ...
  retired := fun _ => false
  -- ... or freed ...
  freed := fun _ => false
  -- ... and nobody is waited for.
  waitFor := fun _ _ => false
  -- Every reader is idle ...
  rstate := fun _ => .idle
  -- ... holding nothing.
  rview := fun _ => 0
  rfloor := fun _ => 0

/-- The steps of the real protocol. -/
inductive Step : State → State → Prop where
  /-- Reader `r` pins: it starts a read, noting what is published. -/
  | pin (s : State) (r : Nat) (h : s.rstate r = .idle) :
      Step s { s with rstate := upd s.rstate r .pinned,
                      rfloor := upd s.rfloor r s.published }
  /-- Reader `r`, pinned, loads the cell: it holds the published view. -/
  | load (s : State) (r : Nat) (h : s.rstate r = .pinned) :
      Step s { s with rstate := upd s.rstate r .holding,
                      rview := upd s.rview r s.published }
  /-- Reader `r` drops its view: the reclaimer stops waiting for it. -/
  | unpin (s : State) (r : Nat) (h : s.rstate r = .holding) :
      Step s { s with rstate := upd s.rstate r .idle,
                      rview := upd s.rview r 0,
                      waitFor := fun v q => s.waitFor v q && q != r }
  /-- A publication built from `base` goes in, because `base` is still the
  published view (the compare-and-swap succeeds). The replaced view is
  retired and waits for every reader that is pinned or holding now. -/
  | swap (s : State) (base : Nat) (h : base = s.published) :
      Step s { s with published := s.made + 1,
                      made := s.made + 1,
                      retired := upd s.retired s.published true,
                      waitFor := upd s.waitFor s.published (fun q => s.rstate q != .idle) }
  /-- The reclaimer frees a retired view nobody is waited for on. -/
  | free (s : State) (v : Nat) (hr : s.retired v = true)
      (hw : ∀ q, s.waitFor v q = false) :
      Step s { s with freed := upd s.freed v true }

/-- The states the protocol can reach from `init`. -/
inductive Reachable : State → Prop where
  /-- The start is reachable. -/
  | init : Reachable init
  /-- One step from a reachable state reaches another. -/
  | step {s t : State} : Reachable s → Step s t → Reachable t

/-- What holds in every reachable state. The last two fields are the
promises; the others are what makes them hold step after step. -/
structure Inv (s : State) : Prop where
  /-- The published view is the newest one built. -/
  pub_made : s.published = s.made
  /-- Only views older than the published one are ever retired. -/
  retired_old : ∀ v, s.retired v = true → v < s.published
  /-- Only retired views are freed. -/
  freed_retired : ∀ v, s.freed v = true → s.retired v = true
  /-- A pinned reader's floor is at most what is published. -/
  pinned_floor : ∀ r, s.rstate r = .pinned → s.rfloor r ≤ s.published
  /-- A holding reader's floor is at most its view. -/
  holding_fresh : ∀ r, s.rstate r = .holding → s.rfloor r ≤ s.rview r
  /-- A holding reader's view, once retired, still waits for it. -/
  holding_waited : ∀ r, s.rstate r = .holding →
      s.retired (s.rview r) = true → s.waitFor (s.rview r) r = true
  /-- **`NoFreedRead`.** A holding reader's view is not freed. -/
  holding_live : ∀ r, s.rstate r = .holding → s.freed (s.rview r) = false

/-- The invariant holds at the start. -/
theorem inv_init : Inv init := by
  -- Every field is about an empty start: `simp` closes each one.
  constructor <;> intros <;> simp_all [init]

/-- Every step keeps the invariant. -/
theorem inv_step {s t : State} (hs : Inv s) (hst : Step s t) : Inv t := by
  -- One case per kind of step.
  cases hst with
  | pin r h =>
    -- A pin changes only reader `r`'s state (idle to pinned) and floor.
    -- Split the invariant into its seven fields and prove each.
    constructor
    -- The cell and the views are untouched: the old facts still hold.
    · exact hs.pub_made
    · exact hs.retired_old
    · exact hs.freed_retired
    -- Pinned floors: take a pinned reader `q`.
    · intro q hq
      -- Either it is `r` or another reader.
      by_cases hqr : q = r
      · -- It is `r`: its floor is the published view; `simp` reads that off.
        subst hqr; simp
      · -- Another reader: its entries did not change; reuse the old fact.
        simp [hqr] at hq ⊢; exact hs.pinned_floor q hq
    -- Holding readers: take one, `q`.
    · intro q hq
      -- Either it is `r` or another reader.
      by_cases hqr : q = r
      · -- `r` is pinned now, not holding: `simp` finds the contradiction.
        subst hqr; simp at hq
      · -- Another reader: unchanged; reuse the old fact.
        simp [hqr] at hq ⊢; exact hs.holding_fresh q hq
    -- Wait bits of holders: the same two cases.
    · intro q hq
      by_cases hqr : q = r
      · -- `r` is not holding.
        subst hqr; simp at hq
      · -- Another holder: unchanged.
        simp [hqr] at hq ⊢; exact hs.holding_waited q hq
    -- Holders' views not freed: the same two cases.
    · intro q hq
      by_cases hqr : q = r
      · -- `r` is not holding.
        subst hqr; simp at hq
      · -- Another holder: unchanged.
        simp [hqr] at hq ⊢; exact hs.holding_live q hq
  | load r h =>
    -- A load makes `r` hold the published view. Prove each field.
    constructor
    -- The cell and the views are untouched.
    · exact hs.pub_made
    · exact hs.retired_old
    · exact hs.freed_retired
    -- Pinned floors: `r` is no longer pinned; other pinned readers are
    -- unchanged.
    · intro q hq
      by_cases hqr : q = r
      · -- `r` holds now, so it is not pinned: contradiction.
        subst hqr; simp at hq
      · -- Another reader: reuse the old fact.
        simp [hqr] at hq; exact hs.pinned_floor q hq
    -- Holders' floors: `r` holds the published view, at least its floor
    -- because it was pinned; others are unchanged.
    · intro q hq
      by_cases hqr : q = r
      · -- `r`: the goal is `floor ≤ published`, the pinned fact.
        subst hqr; simp; exact hs.pinned_floor q h
      · -- Another holder: unchanged.
        simp [hqr] at hq ⊢; exact hs.holding_fresh q hq
    -- Wait bits: the published view is not retired, so `r` needs none.
    · intro q hq
      by_cases hqr : q = r
      · -- `r` holds the published view.
        subst hqr
        -- Suppose it were retired ...
        intro hret
        -- ... read the retired bit of the published view ...
        simp at hret
        -- ... a retired view is older than the published one ...
        have := hs.retired_old _ hret
        -- ... and no view is older than itself.
        omega
      · -- Another holder: unchanged.
        simp [hqr] at hq ⊢; exact hs.holding_waited q hq
    -- Not freed: the published view is not retired, hence not freed.
    · intro q hq
      by_cases hqr : q = r
      · -- `r` holds the published view.
        subst hqr
        -- The goal is the published view's freed bit.
        simp
        -- Look at that bit.
        cases hf : s.freed s.published with
        | false =>
          -- Not freed: done.
          rfl
        | true =>
          -- Freed would mean retired, hence older than itself: impossible.
          have := hs.retired_old _ (hs.freed_retired _ hf)
          omega
      · -- Another holder: unchanged.
        simp [hqr] at hq ⊢; exact hs.holding_live q hq
  | unpin r h =>
    -- An unpin makes `r` idle; every other reader keeps its view and bits.
    constructor
    -- The cell and the views are untouched.
    · exact hs.pub_made
    · exact hs.retired_old
    · exact hs.freed_retired
    -- Pinned floors: `r` is idle; others are unchanged.
    · intro q hq
      by_cases hqr : q = r
      · -- `r` is idle, not pinned: contradiction.
        subst hqr; simp at hq
      · -- Another reader: reuse the old fact.
        simp [hqr] at hq; exact hs.pinned_floor q hq
    -- Holders' floors: `r` is not a holder any more; others unchanged.
    · intro q hq
      by_cases hqr : q = r
      · -- `r` is idle: contradiction.
        subst hqr; simp at hq
      · -- Another holder: unchanged.
        simp [hqr] at hq ⊢; exact hs.holding_fresh q hq
    -- Wait bits: for another holder `q` its bit is untouched (`q != r`).
    · intro q hq
      by_cases hqr : q = r
      · -- `r` is idle: contradiction.
        subst hqr; simp at hq
      · -- Read `q`'s bit through the new wait table: unchanged for `q`.
        simp [hqr] at hq ⊢
        -- Given the view is retired, the old fact gives the bit.
        intro hret
        exact hs.holding_waited q hq hret
    -- Not freed: nothing is freed, and holders other than `r` keep views.
    · intro q hq
      by_cases hqr : q = r
      · -- `r` is idle: contradiction.
        subst hqr; simp at hq
      · -- Another holder: unchanged.
        simp [hqr] at hq ⊢; exact hs.holding_live q hq
  | swap base h =>
    -- A swap publishes view `made + 1` and retires the old published one.
    have hpm := hs.pub_made
    constructor
    -- The new view is the newest built.
    · rfl
    -- Every retired view is now below `made + 1`.
    · intro v hv
      -- Read the new state's fields as the old state's.
      dsimp only at hv ⊢
      by_cases hvp : v = s.published
      · -- The view just retired is the old published one, below the new.
        omega
      · -- An older retired view was below the old published one already.
        simp [hvp] at hv
        have := hs.retired_old v hv
        omega
    -- Freed views were retired before, and stay retired.
    · intro v hv
      -- Read the new state's fields as the old state's.
      dsimp only at hv ⊢
      have hr := hs.freed_retired v hv
      by_cases hvp : v = s.published
      · -- It is the view just retired: retired now.
        subst hvp; simp
      · -- Any other view keeps its retired bit.
        simp [hvp]; exact hr
    -- Pinned floors were at most the old published view, below the new one.
    · intro q hq
      -- Read the new state's fields as the old state's.
      dsimp only at hq ⊢
      have := hs.pinned_floor q hq
      omega
    -- Holding readers keep their views and floors.
    · exact hs.holding_fresh
    -- A holder of the view just retired is waited for: it is not idle. A
    -- holder of an older view keeps its wait bit.
    · intro q hq hret
      -- Read the new state's fields as the old state's.
      dsimp only at hq hret ⊢
      by_cases hvp : s.rview q = s.published
      · -- It holds the view just retired: its bit is "not idle", true.
        rw [hvp]; simp [hq]
      · -- It holds an older view: that view's wait bits are unchanged.
        simp [hvp] at hret ⊢
        exact hs.holding_waited q hq hret
    -- Nothing is freed by a swap.
    · exact hs.holding_live
  | free v hr hw =>
    -- Freeing `v`: only allowed with nobody waited for on it.
    constructor
    · exact hs.pub_made
    · exact hs.retired_old
    -- `v` was retired, every other freed view too.
    · intro w hwf
      by_cases hwv : w = v
      · subst hwv; exact hr
      · simp [hwv] at hwf; exact hs.freed_retired w hwf
    · exact hs.pinned_floor
    · exact hs.holding_fresh
    · exact hs.holding_waited
    -- A holder of `v` would be waited for on it, which `free` rules out.
    · intro q hq
      by_cases hqv : s.rview q = v
      · exfalso
        have hwait := hs.holding_waited q hq (by rw [hqv]; exact hr)
        rw [hqv, hw q] at hwait
        exact Bool.false_ne_true hwait
      · simp [hqv]; exact hs.holding_live q hq

/-- Every reachable state satisfies the invariant. -/
theorem inv_reachable {s : State} (h : Reachable s) : Inv s := by
  -- Induction on how `s` was reached: the start, then one step at a time.
  induction h with
  | init =>
    -- The start satisfies it.
    exact inv_init
  | step _ hst ih =>
    -- One more step keeps it.
    exact inv_step ih hst

/-- **`NoFreedRead` and `FreshLoad`, for every reachable state.** A reader
holding a view holds one that is not freed and is at least as new as what
was published when its load began. -/
theorem reachable_safe {s : State} (h : Reachable s) (r : Nat)
    (hr : s.rstate r = .holding) :
    s.freed (s.rview r) = false ∧ s.rfloor r ≤ s.rview r := by
  -- The invariant holds in `s` ...
  have hi := inv_reachable h
  -- ... and both promises are fields of it.
  exact ⟨hi.holding_live r hr, hi.holding_fresh r hr⟩

/-! ## The compare-and-swap chain -/

/-- Apply publication attempts in order. Each attempt is `(base, new)`: a
view built from `base`. With `cas` it goes in only if `base` is still
published; without it (the PlainStore bug) it always goes in. Returns the
attempts that went in, as `(base, replaced)` pairs. -/
def run (cas : Bool) : Nat → List (Nat × Nat) → List (Nat × Nat)
  -- No attempts left: nothing more goes in.
  | _, [] => []
  -- The next attempt goes in when the CAS allows it, replacing `cur`.
  | cur, (base, new) :: rest =>
    if !cas || base == cur then (base, cur) :: run cas new rest else run cas cur rest

/-- Every pair that went in was built from the view it replaced. -/
def Chained : List (Nat × Nat) → Prop
  -- An empty history is a chain.
  | [] => True
  -- Each entry's base is what it replaced, and the rest is a chain.
  | (base, replaced) :: rest => base = replaced ∧ Chained rest

/-- **`ChainOfPublications`.** With the compare-and-swap, every publication
that goes in, from any start and for any list of attempts, was built from
the very view it replaced: no publication overwrites another's change. -/
theorem cas_chain (cur : Nat) (attempts : List (Nat × Nat)) :
    Chained (run true cur attempts) := by
  -- Induction on the attempts, for every current view.
  induction attempts generalizing cur with
  | nil =>
    -- No attempts: the empty history is a chain.
    trivial
  | cons a rest ih =>
    -- Split the attempt into its base and its new view.
    obtain ⟨base, new⟩ := a
    -- Unfold one step of the run.
    simp only [run]
    -- Either the CAS let it in (and `base = cur`) or it did not.
    by_cases hb : base = cur
    · -- It went in: its pair is `(cur, cur)`, chained, and the rest is a
      -- chain from the new view by the hypothesis.
      simp [hb, Chained, ih]
    · -- It did not: the history is the rest's, a chain by the hypothesis.
      simp [hb, ih]

/-! ## The RED cases, as counterexamples -/

/-- **PlainStore.** Two publishers both build from view 1; without the CAS
the second goes in on top of the first and replaces view 2, which it was
not built from. -/
theorem plain_store_breaks : ¬ Chained (run false 1 [(1, 2), (1, 3)]) := by
  -- Evaluate the run and the chain: the second pair is `(1, 2)`, and 1 is
  -- not 2.
  simp [run, Chained]

/-- A state where reader 0 has loaded view 1. -/
def holdingOne : State :=
  { init with rstate := upd init.rstate 0 .holding, rview := upd init.rview 0 1 }

/-- **FreeEarly.** A swap that frees the view it retires at once, instead
of retiring it to wait for readers, leaves reader 0 holding a freed view. -/
theorem free_early_breaks :
    let s' := { holdingOne with published := 2, made := 2,
                                retired := upd holdingOne.retired 1 true,
                                freed := upd holdingOne.freed 1 true }
    s'.rstate 0 = .holding ∧ s'.freed (s'.rview 0) = true := by
  -- Evaluate the two reads of the state.
  decide

/-- **StaleLoad.** Reader 0 held view 1 before; view 2 is published and the
reader pins (floor 2) but reuses view 1 instead of loading: its view is
older than its floor. -/
theorem stale_load_breaks :
    let s' := { init with published := 2, made := 2,
                          rstate := upd init.rstate 0 .holding,
                          rview := upd init.rview 0 1,
                          rfloor := upd init.rfloor 0 2 }
    s'.rstate 0 = .holding ∧ s'.rview 0 < s'.rfloor 0 := by
  -- Evaluate: view 1 is below floor 2.
  decide

end Regolith.ReadView
