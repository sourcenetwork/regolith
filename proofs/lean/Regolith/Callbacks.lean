/-!
# Callbacks: transaction callbacks run exactly once, in order, per attempt

This file backs the TLA+ model `proofs/tla/TxnCallbacks.tla`, invariants
`AtMostOnce`, `ExactlyOnce`, `CallbacksBeforeHooks`, `NoLostUpdate`,
`AttemptIsolation` and `PanicAborts` (configurations `MC_TxnCallbacks_*`).
TLC checks there how the outcome reaches a transaction concurrently: a
committer, a helping committer, `close`, or the owner. Here the outcome
state machine of one `transact` call (plan 3.16) is a sequential machine:
attempts one after another, each registering callbacks, running its
before_commit pass, validating, and ending with exactly one outcome. The
theorems hold for every number of attempts, callbacks and writes.

What is proved, in plain words:

1. `step_inv` and `reachable_inv`: the machine's invariant holds in every
   reachable state.
2. `exactly_once`: every on_commit callback registered in attempt `a` has
   run exactly once if attempt `a` committed and never otherwise; every
   on_abort callback has run exactly once, with the attempt's abort reason,
   if the attempt ended without committing, and never otherwise. The
   database hooks' on_commit and on_abort follow the same law, once per
   attempt. An attempt that has not ended has run none of them.
   `never_both`: no attempt runs both an on_commit and an on_abort
   callback.
3. `order`: within an attempt, every event of an earlier stage comes before
   every event of a later stage: the before_commit callbacks, then the
   hooks' before_commit, then validation, then the transaction's outcome
   callbacks, then the hooks' outcome. `callbacks_before_hooks`: once an
   on_commit callback ran, the hooks' on_commit ran too, after it.
   `finish_commit_runs` and
   `finish_abort_runs`: the outcome callbacks run in the order they were
   registered, the hooks after them. `commit_was_validated`: a committed
   attempt was validated, before its on_commit callbacks.
4. `before_writes_validated`: the write set an attempt validates holds every
   write its before_commit callbacks (and the hooks' before_commit) made.
5. `attempts_isolated`: an outcome callback that ran was registered in the
   attempt whose outcome it reports, so a re-run never runs a previous
   attempt's callbacks; `surviving_callbacks_break_isolation` is the RED
   case, as a counterexample.
6. `panic_aborts`: a panic in before_commit ends the attempt with the
   reason `panic`, runs every on_abort callback of the attempt, and no
   on_commit callback.
7. `delivered_once`: an outcome that comes back through a `CommitTicket` is
   delivered, and its callbacks run, at most once, and exactly once when
   the ticket is ready, however many paths try (the queue's poll, the
   queue's drop, the commit's own fallback); `no_claim_delivers_twice` is
   the RED case.
8. `delivered_on_queue_thread`: every delivery runs on the thread that
   holds the commit's queue, never on a committer that decided or synced
   it (D53, the committing thread).

How to read the Lean: `def` defines a function or a property, `theorem`
states a fact and its proof follows `:= by`. Lines starting with `--` are
comments. `[x, y].Sublist l` says `x` comes before `y` in the list `l`.
`l.count e` is how many times `e` occurs in `l`.
-/

namespace Regolith.Callbacks

/-! ## The objects -/

/-- How an attempt ended: committed, or one of the abort reasons of 3.16
(conflict, rollback, drop, an error, close, a panic in before_commit). -/
inductive Outcome where
  /-- The attempt committed. -/
  | commit
  /-- Validation found a conflict; `transact` may re-run. -/
  | conflict
  /-- The caller rolled back. -/
  | rollback
  /-- The transaction was dropped. -/
  | drop
  /-- The closure, or a before_commit callback, returned an error. -/
  | error
  /-- The database was closed. -/
  | close
  /-- A before_commit callback panicked (`Error::CallbackPanicked`). -/
  | panic
  deriving DecidableEq

/-- Where the current attempt is. -/
inductive Phase where
  /-- The closure runs: callbacks are registered and writes buffered. -/
  | open_
  /-- `commit` was called: the before_commit callbacks run, and may write
  and register more callbacks. -/
  | preparing
  /-- The hooks' before_commit ran: the write set is complete. -/
  | prepared
  /-- Validation ran, with this verdict (`true`: no conflict). -/
  | validated (ok : Bool)
  /-- The outcome's callbacks ran. -/
  | ended
  deriving DecidableEq

/-- One entry of the trace: a callback, a hook or validation that ran.
The first argument is always the attempt. -/
inductive Ev where
  /-- Before_commit callback `c` of attempt `a` ran. -/
  | before (a c : Nat)
  /-- The database hooks' before_commit ran for attempt `a`. -/
  | hookBefore (a : Nat)
  /-- Attempt `a` was validated with write set `ws`. -/
  | validate (a : Nat) (ws : List Nat)
  /-- On_commit callback `c` of attempt `a` ran. -/
  | onCommit (a c : Nat)
  /-- On_abort callback `c` of attempt `a` ran, with reason `o`. -/
  | onAbort (a c : Nat) (o : Outcome)
  /-- The database hooks' on_commit ran for attempt `a`. -/
  | hookCommit (a : Nat)
  /-- The database hooks' on_abort ran for attempt `a`, with reason `o`. -/
  | hookAbort (a : Nat) (o : Outcome)
  deriving DecidableEq

/-- The attempt an event belongs to. -/
def Ev.att : Ev → Nat
  | .before a _ => a
  | .hookBefore a => a
  | .validate a _ => a
  | .onCommit a _ => a
  | .onAbort a _ _ => a
  | .hookCommit a => a
  | .hookAbort a _ => a

/-- The stage of an event inside its attempt: before_commit callbacks (0),
the hooks' before_commit (1), validation (2), the transaction's outcome
callbacks (3), the hooks' outcome (4). -/
def Ev.rank : Ev → Nat
  | .before .. => 0
  | .hookBefore _ => 1
  | .validate .. => 2
  | .onCommit .. => 3
  | .onAbort .. => 3
  | .hookCommit _ => 4
  | .hookAbort .. => 4

/-- The latest stage a phase has reached. -/
def Phase.rank : Phase → Nat
  | .open_ => 0
  | .preparing => 0
  | .prepared => 1
  | .validated _ => 2
  | .ended => 4

/-- The state of one `transact` call. -/
structure T where
  /-- The current attempt, counted from 0. -/
  att : Nat
  /-- Where the current attempt is. -/
  phase : Phase
  /-- The current attempt's outcome, once it ended. -/
  cur : Option Outcome
  /-- Before_commit callbacks registered and not yet run, in order. -/
  befores : List Nat
  /-- The current attempt's on_commit callbacks, in registration order. -/
  commits : List Nat
  /-- The current attempt's on_abort callbacks, in registration order. -/
  aborts : List Nat
  /-- The keys the current attempt wrote: its closure, its callbacks and
  the hooks. -/
  writes : List Nat
  /-- Ghost: every event, in order. -/
  log : List Ev
  /-- Ghost: every on_commit registration `(attempt, callback)`. -/
  regC : List (Nat × Nat)
  /-- Ghost: every on_abort registration `(attempt, callback)`. -/
  regA : List (Nat × Nat)
  /-- Ghost: every `(attempt, key)` a before_commit callback or the hooks'
  before_commit wrote. -/
  bw : List (Nat × Nat)
  deriving DecidableEq

/-- The start: attempt 0, open, nothing registered or run. -/
def init : T := ⟨0, .open_, none, [], [], [], [], [], [], [], []⟩

/-- Attempt `a`'s outcome: every earlier attempt ended with a conflict
(`transact` re-runs only on a conflict), the current one has `cur`, and a
later one has none yet. -/
def outcomeOf (s : T) (a : Nat) : Option Outcome :=
  if a < s.att then some .conflict else if a = s.att then s.cur else none

/-- The aborts a phase allows. A conflict comes only from validation;
rollback, drop, an error and close may end an attempt any time before it
is validated. (A panic has its own step.) -/
def Allowed (p : Phase) (o : Outcome) : Prop :=
  (p = .validated false ∧ o = .conflict) ∨
  ((p = .open_ ∨ p = .preparing ∨ p = .prepared) ∧
    (o = .rollback ∨ o = .drop ∨ o = .error ∨ o = .close))

/-- The fresh transaction `transact` re-runs a conflicted attempt in: the
next attempt, open, with no outcome, no callback and no write. -/
def retried (s : T) : T :=
  { s with att := s.att + 1, phase := .open_, cur := none, befores := [], commits := [],
           aborts := [], writes := [] }

/-- The events of a commit: the transaction's on_commit callbacks in
registration order, then the hooks' on_commit. -/
def commitChunk (s : T) : List Ev :=
  s.commits.map (Ev.onCommit s.att) ++ [.hookCommit s.att]

/-- The events of an abort with reason `o`: the transaction's on_abort
callbacks in registration order, then the hooks' on_abort. -/
def abortChunk (s : T) (o : Outcome) : List Ev :=
  s.aborts.map (fun c => Ev.onAbort s.att c o) ++ [.hookAbort s.att o]

/-! ## The steps -/

/-- The design's steps. -/
inductive Step : T → T → Prop
  /-- Register on_commit callback `c` (fresh in this attempt), while the
  closure runs or during the before_commit pass. -/
  | regCommit (s : T) (c : Nat)
      -- The closure runs, or the before_commit pass does.
      (hp : s.phase = .open_ ∨ s.phase = .preparing)
      -- `c` is not an on_commit callback of this attempt yet.
      (hc : (s.att, c) ∉ s.regC) :
      Step s { s with commits := s.commits ++ [c], regC := s.regC ++ [(s.att, c)] }
  /-- Register on_abort callback `c` (fresh in this attempt). -/
  | regAbort (s : T) (c : Nat)
      -- The closure runs, or the before_commit pass does.
      (hp : s.phase = .open_ ∨ s.phase = .preparing)
      -- `c` is not an on_abort callback of this attempt yet.
      (hc : (s.att, c) ∉ s.regA) :
      Step s { s with aborts := s.aborts ++ [c], regA := s.regA ++ [(s.att, c)] }
  /-- Register before_commit callback `c`; one registered during the pass
  runs in the same pass. -/
  | regBefore (s : T) (c : Nat)
      -- The closure runs, or the before_commit pass does.
      (hp : s.phase = .open_ ∨ s.phase = .preparing) :
      Step s { s with befores := s.befores ++ [c] }
  /-- The closure writes key `k`. -/
  | write (s : T) (k : Nat)
      -- The closure runs.
      (hp : s.phase = .open_) :
      Step s { s with writes := s.writes ++ [k] }
  /-- The closure returns and `commit` (or `prepare`) is called. -/
  | commit (s : T)
      -- The closure ran.
      (hp : s.phase = .open_) :
      Step s { s with phase := .preparing }
  /-- The oldest pending before_commit callback runs and writes `ws`
  through the transaction. -/
  | runBefore (s : T) (c : Nat) (rest ws : List Nat)
      -- The before_commit pass runs.
      (hp : s.phase = .preparing)
      -- `c` is the oldest pending before_commit callback.
      (hb : s.befores = c :: rest) :
      Step s { s with befores := rest, log := s.log ++ [.before s.att c],
                      writes := s.writes ++ ws, bw := s.bw ++ ws.map (fun k => (s.att, k)) }
  /-- With every before_commit callback run, the hooks' before_commit runs
  and writes `ws`. -/
  | hookBefore (s : T) (ws : List Nat)
      -- The before_commit pass runs.
      (hp : s.phase = .preparing)
      -- Every before_commit callback ran.
      (hb : s.befores = []) :
      Step s { s with phase := .prepared, log := s.log ++ [.hookBefore s.att],
                      writes := s.writes ++ ws, bw := s.bw ++ ws.map (fun k => (s.att, k)) }
  /-- Validation of the whole write set, with verdict `ok`. -/
  | validate (s : T) (ok : Bool)
      -- Every before_commit callback, the hooks' included, ran.
      (hp : s.phase = .prepared) :
      Step s { s with phase := .validated ok, log := s.log ++ [.validate s.att s.writes] }
  /-- A validated attempt commits: its on_commit callbacks run, then the
  hooks'. -/
  | finishCommit (s : T)
      -- Validation found no conflict.
      (hp : s.phase = .validated true) :
      Step s { s with phase := .ended, cur := some .commit, log := s.log ++ commitChunk s }
  /-- The attempt ends without committing, for a reason its phase allows:
  its on_abort callbacks run, then the hooks'. -/
  | finishAbort (s : T) (o : Outcome)
      -- The phase allows ending with `o`.
      (ho : Allowed s.phase o) :
      Step s { s with phase := .ended, cur := some o, log := s.log ++ abortChunk s o }
  /-- The oldest pending before_commit callback panics: the commit fails
  with `CallbackPanicked`, and the on_abort callbacks run. -/
  | panicBefore (s : T) (c : Nat) (rest : List Nat)
      -- The before_commit pass runs.
      (hp : s.phase = .preparing)
      -- `c` is the oldest pending before_commit callback, the one that panics.
      (hb : s.befores = c :: rest) :
      Step s { s with phase := .ended, cur := some .panic, befores := rest,
                      log := s.log ++ (Ev.before s.att c :: abortChunk s .panic) }
  /-- `transact` re-runs a conflicted attempt in a fresh transaction: no
  callback and no write carries over (the state `retried s`). -/
  | retry (s : T)
      -- The attempt ended ...
      (hp : s.phase = .ended)
      -- ... with a conflict, the only outcome `transact` re-runs.
      (hc : s.cur = some .conflict) :
      Step s { s with att := s.att + 1, phase := .open_, cur := none, befores := [],
                      commits := [], aborts := [], writes := [] }

/-- Any number of steps, one after another. -/
inductive Steps : T → T → Prop
  /-- No step at all. -/
  | refl (s : T) : Steps s s
  /-- Some steps, then one more. -/
  | tail {s t u : T} : Steps s t → Step t u → Steps s u

/-! ## The invariant -/

/-- The machine's invariant. -/
structure Inv (s : T) : Prop where
  /-- The current on_commit list is this attempt's registrations, in order. -/
  commits_order : (s.regC.filter (fun p => p.1 == s.att)).map Prod.snd = s.commits
  /-- The current on_abort list is this attempt's registrations, in order. -/
  aborts_order : (s.regA.filter (fun p => p.1 == s.att)).map Prod.snd = s.aborts
  /-- No on_commit callback is registered twice in an attempt. -/
  commits_nodup : s.commits.Nodup
  /-- No on_abort callback is registered twice in an attempt. -/
  aborts_nodup : s.aborts.Nodup
  /-- No registration belongs to a later attempt. -/
  regC_le : ∀ p ∈ s.regC, p.1 ≤ s.att
  /-- No registration belongs to a later attempt. -/
  regA_le : ∀ p ∈ s.regA, p.1 ≤ s.att
  /-- The current attempt has an outcome exactly when it ended. -/
  cur_ended : s.cur = none ↔ s.phase ≠ .ended
  /-- On_commit callback `c` of attempt `a` ran once if registered and the
  attempt committed, else never. -/
  cC : ∀ a c, s.log.count (.onCommit a c) =
    if (a, c) ∈ s.regC ∧ outcomeOf s a = some .commit then 1 else 0
  /-- On_abort callback `c` of attempt `a` ran once with reason `o` if
  registered and the attempt ended aborted with `o`, else never. -/
  cA : ∀ a c o, s.log.count (.onAbort a c o) =
    if (a, c) ∈ s.regA ∧ outcomeOf s a = some o ∧ o ≠ .commit then 1 else 0
  /-- The hooks' on_commit ran once for a committed attempt, else never. -/
  hC : ∀ a, s.log.count (.hookCommit a) = if outcomeOf s a = some .commit then 1 else 0
  /-- The hooks' on_abort ran once with reason `o` for an attempt aborted
  with `o`, else never. -/
  hA : ∀ a o, s.log.count (.hookAbort a o) =
    if outcomeOf s a = some o ∧ o ≠ .commit then 1 else 0
  /-- No event belongs to a later attempt. -/
  att_le : ∀ x ∈ s.log, x.att ≤ s.att
  /-- The current attempt's events are of stages its phase has reached. -/
  rank_le : ∀ x ∈ s.log, x.att = s.att → x.rank ≤ s.phase.rank
  /-- Within an attempt, earlier stages come first. -/
  ordered : ∀ x ∈ s.log, ∀ y ∈ s.log, x.att = y.att → x.rank < y.rank → [x, y].Sublist s.log
  /-- No callback write belongs to a later attempt. -/
  bw_le : ∀ p ∈ s.bw, p.1 ≤ s.att
  /-- The current attempt's callback writes are in its write set. -/
  bw_cur : ∀ k, (s.att, k) ∈ s.bw → k ∈ s.writes
  /-- A validated write set holds every callback write of its attempt. -/
  bw_validated : ∀ a k ws, (a, k) ∈ s.bw → Ev.validate a ws ∈ s.log → k ∈ ws
  /-- A validated current attempt has its validation in the log. -/
  validated_logged : ∀ ok, s.phase = .validated ok → ∃ ws, Ev.validate s.att ws ∈ s.log
  /-- A committed attempt was validated. -/
  commit_validated : ∀ a, outcomeOf s a = some .commit → ∃ ws, Ev.validate a ws ∈ s.log

/-! ## Helpers -/

/-- A one-element list has no repeats. -/
theorem nodup_one {α : Type} (x : α) : [x].Nodup := by simp

/-- Mapping a list without repeats through an injective function keeps it
without repeats. -/
theorem nodup_map {l : List Nat} {f : Nat → Ev}
    -- `f` never maps two numbers to one event.
    (hf : ∀ x y, f x = f y → x = y)
    -- `l` has no repeats.
    (hl : l.Nodup) :
    (l.map f).Nodup := by
  unfold List.Nodup at *
  rw [List.pairwise_map]
  exact hl.imp (fun h e => h (hf _ _ e))

/-- A list sorted by stage has every earlier-stage element before every
later-stage one. -/
theorem ordered_of_sorted {e : List Ev}
    -- `e` never goes back a stage.
    (hs : e.Pairwise (fun x y => x.rank ≤ y.rank)) :
    ∀ x ∈ e, ∀ y ∈ e, x.rank < y.rank → [x, y].Sublist e := by
  induction e with
  | nil => intro x hx; simp at hx
  | cons z e ih =>
    obtain ⟨hz, he⟩ := List.pairwise_cons.1 hs
    intro x hx y hy hxy
    rcases List.mem_cons.1 hx with rfl | hx'
    · rcases List.mem_cons.1 hy with rfl | hy'
      · -- `x = y = z`: no stage is below itself.
        omega
      · -- `z` heads the list and `y` follows it.
        exact List.Sublist.cons_cons _ (List.singleton_sublist.2 hy')
    · rcases List.mem_cons.1 hy with rfl | hy'
      · -- `y = z` heads the list, so `y`'s stage is at most `x`'s.
        have := hz x hx'
        omega
      · -- Both in the tail.
        exact (ih he x hx' y hy' hxy).cons z

/-- Appending a stage-sorted chunk of current-attempt events, none of a
stage below what the attempt reached, keeps every attempt ordered. -/
theorem ordered_append {l e : List Ev} {a r : Nat}
    -- The old log is ordered.
    (hord : ∀ x ∈ l, ∀ y ∈ l, x.att = y.att → x.rank < y.rank → [x, y].Sublist l)
    -- The current attempt's old events are of stage at most `r`.
    (hrank : ∀ x ∈ l, x.att = a → x.rank ≤ r)
    -- The chunk belongs to the current attempt.
    (hatt : ∀ y ∈ e, y.att = a)
    -- The chunk's stages are at least `r`.
    (hge : ∀ y ∈ e, r ≤ y.rank)
    -- The chunk is sorted by stage.
    (hs : e.Pairwise (fun x y => x.rank ≤ y.rank)) :
    ∀ x ∈ l ++ e, ∀ y ∈ l ++ e, x.att = y.att → x.rank < y.rank → [x, y].Sublist (l ++ e) := by
  intro x hx y hy hxy hlt
  rcases List.mem_append.1 hx with hxl | hxe <;> rcases List.mem_append.1 hy with hyl | hye
  · -- Both old.
    exact (hord x hxl y hyl hxy hlt).trans (List.sublist_append_left l e)
  · -- `x` old, `y` new: `x` comes first.
    exact (List.singleton_sublist.2 hxl).append (List.singleton_sublist.2 hye)
  · -- `x` new, `y` old, same attempt: `y`'s stage is at most `r`, `x`'s at
    -- least `r`, against `x` being of an earlier stage.
    have h1 := hrank y hyl (by rw [← hxy]; exact hatt x hxe)
    have h2 := hge x hxe
    omega
  · -- Both new: the chunk is sorted.
    exact (ordered_of_sorted hs x hxe y hye hlt).trans (List.sublist_append_right l e)

/-- An outcome chunk is sorted: its callbacks share stage 3, the hook is 4. -/
theorem chunk_sorted {l : List Nat} {f : Nat → Ev} {h : Ev}
    -- Every mapped event is of stage 3.
    (hf : ∀ c, (f c).rank = 3)
    -- The hook is of stage 4.
    (hh : h.rank = 4) :
    (l.map f ++ [h]).Pairwise (fun x y => x.rank ≤ y.rank) := by
  rw [List.pairwise_append, List.pairwise_map]
  refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
  · -- Equal stages.
    exact List.pairwise_of_forall (fun a b => by rw [hf a, hf b]; exact Nat.le_refl 3)
  · intro x hx y hy
    simp only [List.mem_map, List.mem_singleton] at hx hy
    obtain ⟨c, -, rfl⟩ := hx
    subst hy
    rw [hf c, hh]
    omega

/-- `outcomeOf` for an attempt other than the current one does not depend
on the current outcome. -/
theorem outcomeOf_ne {s : T} {a : Nat} (o : Option Outcome) (h : a ≠ s.att) :
    outcomeOf { s with cur := o } a = outcomeOf s a := by
  simp [outcomeOf, h]

/-- The current attempt's outcome is `cur`. -/
theorem outcomeOf_cur (s : T) : outcomeOf s s.att = s.cur := by
  simp [outcomeOf]

/-- `outcomeOf` reads only the attempt and `cur`: in any state `t` at the
same attempt as `s`, the current attempt's outcome is `t.cur` and every
other attempt's is as in `s`. -/
theorem outcomeOf_eq (s t : T)
    -- `t` is at the same attempt as `s`.
    (h : t.att = s.att) (a : Nat) :
    outcomeOf t a = if a = s.att then t.cur else outcomeOf s a := by
  unfold outcomeOf
  rw [h]
  by_cases h1 : a < s.att
  · -- An earlier attempt: a conflict in both.
    have : a ≠ s.att := by omega
    simp [h1, this]
  · -- The current attempt, or a later one.
    simp [h1]
    by_cases h2 : a = s.att <;> simp [h2]

/-- At the start no attempt has an outcome. -/
theorem outcomeOf_init (a : Nat) : outcomeOf init a = none := by
  -- Attempt 0 is current with no outcome; no attempt is earlier.
  by_cases h : a = 0 <;> simp [outcomeOf, init, h]

/-! ## Every step keeps the invariant -/

/-- The start satisfies the invariant. -/
theorem init_inv : Inv init := by
  -- Nothing has run or been registered; no attempt has an outcome.
  refine ⟨rfl, rfl, List.nodup_nil, List.nodup_nil, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩ <;> (try simp only [outcomeOf_init]) <;> simp [init]

/-- The current on_commit callbacks are exactly this attempt's
registrations. -/
theorem Inv.mem_commits {s : T}
    -- The invariant holds.
    (h : Inv s) (c : Nat) : c ∈ s.commits ↔ (s.att, c) ∈ s.regC := by
  rw [← h.commits_order]
  simp only [List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨a, c'⟩, ⟨hm, ha⟩, rfl⟩
    simp only at ha
    subst ha
    exact hm
  · intro hm
    exact ⟨(s.att, c), ⟨hm, rfl⟩, rfl⟩

/-- The current on_abort callbacks are exactly this attempt's
registrations. -/
theorem Inv.mem_aborts {s : T}
    -- The invariant holds.
    (h : Inv s) (c : Nat) : c ∈ s.aborts ↔ (s.att, c) ∈ s.regA := by
  rw [← h.aborts_order]
  simp only [List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨a, c'⟩, ⟨hm, ha⟩, rfl⟩
    simp only at ha
    subst ha
    exact hm
  · intro hm
    exact ⟨(s.att, c), ⟨hm, rfl⟩, rfl⟩

/-- An attempt that has not ended has no outcome yet. -/
theorem Inv.cur_none {s : T}
    -- The invariant holds.
    (h : Inv s)
    -- The attempt has not ended.
    (hp : s.phase ≠ .ended) : s.cur = none :=
  h.cur_ended.2 hp

/-- Ending the current attempt with outcome `o` by appending the events
`E` (a list without repeats holding exactly that outcome's callbacks and
hook) keeps the four count laws. -/
theorem counts_end {s t : T} {E : List Ev} {o : Outcome}
    -- The invariant held before.
    (hs : Inv s)
    -- The attempt had not ended.
    (hcur : s.cur = none)
    -- The new state: same attempt and registrations, outcome `o`, log
    -- extended by `E`.
    (hatt : t.att = s.att) (hregC : t.regC = s.regC) (hregA : t.regA = s.regA)
    (htcur : t.cur = some o) (hlog : t.log = s.log ++ E)
    -- `E` has no repeats.
    (hE : E.Nodup)
    -- `E` holds the on_commit callbacks exactly when `o` is a commit.
    (memC : ∀ a c, Ev.onCommit a c ∈ E ↔ a = s.att ∧ o = .commit ∧ c ∈ s.commits)
    -- `E` holds the on_abort callbacks, with reason `o`, exactly when `o`
    -- is an abort.
    (memA : ∀ a c o', Ev.onAbort a c o' ∈ E ↔
      a = s.att ∧ o' = o ∧ o ≠ .commit ∧ c ∈ s.aborts)
    -- `E` holds the hooks' on_commit exactly when `o` is a commit.
    (memHC : ∀ a, Ev.hookCommit a ∈ E ↔ a = s.att ∧ o = .commit)
    -- `E` holds the hooks' on_abort, with reason `o`, exactly when `o` is
    -- an abort.
    (memHA : ∀ a o', Ev.hookAbort a o' ∈ E ↔ a = s.att ∧ o' = o ∧ o ≠ .commit) :
    (∀ a c, t.log.count (.onCommit a c) =
      if (a, c) ∈ t.regC ∧ outcomeOf t a = some .commit then 1 else 0) ∧
    (∀ a c o', t.log.count (.onAbort a c o') =
      if (a, c) ∈ t.regA ∧ outcomeOf t a = some o' ∧ o' ≠ .commit then 1 else 0) ∧
    (∀ a, t.log.count (.hookCommit a) = if outcomeOf t a = some .commit then 1 else 0) ∧
    (∀ a o', t.log.count (.hookAbort a o') =
      if outcomeOf t a = some o' ∧ o' ≠ .commit then 1 else 0) := by
  -- Before the step, the current attempt had no outcome, so none of its
  -- outcome events were in the log.
  have hold : outcomeOf s s.att = none := by rw [outcomeOf_cur, hcur]
  refine ⟨fun a c => ?_, fun a c o' => ?_, fun a => ?_, fun a o' => ?_⟩
  · rw [hlog, List.count_append, hs.cC, hE.count]
    simp only [outcomeOf_eq s t hatt, hregC, memC, htcur]
    by_cases ha : a = s.att
    · -- The current attempt: nothing before, the chunk now.
      subst ha
      simp [hold, ← hs.mem_commits, and_comm]
    · simp [ha]
  · rw [hlog, List.count_append, hs.cA, hE.count]
    simp only [outcomeOf_eq s t hatt, hregA, memA, htcur]
    by_cases ha : a = s.att
    · -- The current attempt: nothing before; the chunk holds `c` with
      -- reason `o` exactly when `c` is registered and `o` is an abort.
      subst ha
      have hm := hs.mem_aborts c
      by_cases h1 : o' = o
      · subst h1
        simp [hold, hm, and_comm]
      · simp [hold, h1, Ne.symm h1]
    · simp [ha]
  · rw [hlog, List.count_append, hs.hC, hE.count]
    simp only [outcomeOf_eq s t hatt, memHC, htcur]
    by_cases ha : a = s.att
    · subst ha; simp [hold]
    · simp [ha]
  · rw [hlog, List.count_append, hs.hA, hE.count]
    simp only [outcomeOf_eq s t hatt, memHA, htcur]
    by_cases ha : a = s.att
    · subst ha
      by_cases h1 : o' = o
      · subst h1; simp [hold]
      · simp [hold, h1, Ne.symm h1]
    · simp [ha]

/-- A step that leaves the attempt, the outcome, the registrations and the
outcome events alone, and appends only events of stages 0 to 2, keeps the
four count laws. -/
theorem counts_append_quiet {s : T} {e : List Ev}
    -- The four count laws held before (`Inv.cC`, `cA`, `hC`, `hA`).
    (hcC : ∀ a c, s.log.count (.onCommit a c) =
      if (a, c) ∈ s.regC ∧ outcomeOf s a = some .commit then 1 else 0)
    (hcA : ∀ a c o, s.log.count (.onAbort a c o) =
      if (a, c) ∈ s.regA ∧ outcomeOf s a = some o ∧ o ≠ .commit then 1 else 0)
    (hhC : ∀ a, s.log.count (.hookCommit a) = if outcomeOf s a = some .commit then 1 else 0)
    (hhA : ∀ a o, s.log.count (.hookAbort a o) =
      if outcomeOf s a = some o ∧ o ≠ .commit then 1 else 0)
    -- The appended events are of the early stages.
    (he : ∀ x ∈ e, x.rank ≤ 2) :
    (∀ a c, (s.log ++ e).count (.onCommit a c) =
      if (a, c) ∈ s.regC ∧ outcomeOf s a = some .commit then 1 else 0) ∧
    (∀ a c o, (s.log ++ e).count (.onAbort a c o) =
      if (a, c) ∈ s.regA ∧ outcomeOf s a = some o ∧ o ≠ .commit then 1 else 0) ∧
    (∀ a, (s.log ++ e).count (.hookCommit a) = if outcomeOf s a = some .commit then 1 else 0) ∧
    (∀ a o, (s.log ++ e).count (.hookAbort a o) =
      if outcomeOf s a = some o ∧ o ≠ .commit then 1 else 0) := by
  -- No outcome event is among the appended ones: their stages are 3 and 4.
  have z : ∀ x, 3 ≤ x.rank → e.count x = 0 := by
    intro x hx
    apply List.count_eq_zero.2
    intro hm
    have := he x hm
    omega
  refine ⟨fun a c => ?_, fun a c o => ?_, fun a => ?_, fun a o => ?_⟩
  · rw [List.count_append, z _ (by simp [Ev.rank]), hcC]; rfl
  · rw [List.count_append, z _ (by simp [Ev.rank]), hcA]; rfl
  · rw [List.count_append, z _ (by simp [Ev.rank]), hhC]; rfl
  · rw [List.count_append, z _ (by simp [Ev.rank]), hhA]; rfl

/-- What a commit chunk holds: the current on_commit callbacks, and the
hooks' on_commit. -/
theorem mem_commitChunk (s : T) (e : Ev) :
    e ∈ commitChunk s ↔ (∃ c ∈ s.commits, e = .onCommit s.att c) ∨ e = .hookCommit s.att := by
  simp [commitChunk, eq_comm]

/-- What an abort chunk holds: the current on_abort callbacks with reason
`o`, and the hooks' on_abort with `o`. -/
theorem mem_abortChunk (s : T) (o : Outcome) (e : Ev) :
    e ∈ abortChunk s o ↔ (∃ c ∈ s.aborts, e = .onAbort s.att c o) ∨ e = .hookAbort s.att o := by
  simp [abortChunk, eq_comm]

/-- A commit chunk holds on_commit callback `c` of attempt `a` exactly when
`a` is the current attempt and `c` one of its on_commit callbacks. -/
theorem commitChunk_memC (s : T) (a c : Nat) :
    Ev.onCommit a c ∈ commitChunk s ↔ a = s.att ∧ Outcome.commit = .commit ∧ c ∈ s.commits := by
  rw [mem_commitChunk]
  constructor
  · rintro (⟨c', hc', h⟩ | h)
    · -- One of the callback events.
      simp only [Ev.onCommit.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, hc'⟩
    · -- The hook event is not a callback event.
      simp at h
  · rintro ⟨rfl, -, hc⟩
    exact Or.inl ⟨c, hc, rfl⟩

/-- An abort chunk with reason `o` holds on_abort callback `c` of attempt
`a` with reason `o'` exactly when `a` is the current attempt, `o' = o`, and
`c` is one of its on_abort callbacks. -/
theorem abortChunk_memA (s : T) {o : Outcome}
    -- `o` is an abort reason.
    (hoc : o ≠ .commit) (a c : Nat) (o' : Outcome) :
    Ev.onAbort a c o' ∈ abortChunk s o ↔ a = s.att ∧ o' = o ∧ o ≠ .commit ∧ c ∈ s.aborts := by
  rw [mem_abortChunk]
  constructor
  · rintro (⟨c', hc', h⟩ | h)
    · simp only [Ev.onAbort.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl, hoc, hc'⟩
    · simp at h
  · rintro ⟨rfl, rfl, -, hc⟩
    exact Or.inl ⟨c, hc, rfl⟩

/-- An abort chunk with reason `o` holds the hooks' on_abort of attempt
`a` with reason `o'` exactly when `a` is current and `o' = o`. -/
theorem abortChunk_memHA (s : T) {o : Outcome}
    -- `o` is an abort reason.
    (hoc : o ≠ .commit) (a : Nat) (o' : Outcome) :
    Ev.hookAbort a o' ∈ abortChunk s o ↔ a = s.att ∧ o' = o ∧ o ≠ .commit := by
  rw [mem_abortChunk]
  constructor
  · rintro (⟨c', -, h⟩ | h)
    · simp at h
    · simp only [Ev.hookAbort.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, hoc⟩
  · rintro ⟨rfl, rfl, -⟩
    exact Or.inr rfl

/-- A commit chunk has no repeats. -/
theorem commitChunk_nodup {s : T}
    -- No on_commit callback is registered twice.
    (hn : s.commits.Nodup) : (commitChunk s).Nodup := by
  unfold commitChunk
  rw [List.nodup_append]
  refine ⟨nodup_map (fun x y h => by simpa using h) hn, nodup_one _, ?_⟩
  -- A callback event is not the hook event.
  intro a ha b hb
  simp only [List.mem_map, List.mem_singleton] at ha hb
  obtain ⟨c, -, rfl⟩ := ha
  subst hb
  simp

/-- An abort chunk has no repeats. -/
theorem abortChunk_nodup {s : T} {o : Outcome}
    -- No on_abort callback is registered twice.
    (hn : s.aborts.Nodup) : (abortChunk s o).Nodup := by
  unfold abortChunk
  rw [List.nodup_append]
  refine ⟨nodup_map (fun x y h => by simpa using h) hn, nodup_one _, ?_⟩
  intro a ha b hb
  simp only [List.mem_map, List.mem_singleton] at ha hb
  obtain ⟨c, -, rfl⟩ := ha
  subst hb
  simp

/-- Every event of a commit chunk belongs to the current attempt and is
of stage 3 or 4. -/
theorem commitChunk_att {s : T} : ∀ y ∈ commitChunk s, y.att = s.att ∧ 3 ≤ y.rank := by
  intro y hy
  rcases (mem_commitChunk s y).1 hy with ⟨c, -, rfl⟩ | rfl <;> simp [Ev.att, Ev.rank]

/-- Every event of an abort chunk belongs to the current attempt and is of
stage 3 or 4. -/
theorem abortChunk_att {s : T} {o : Outcome} :
    ∀ y ∈ abortChunk s o, y.att = s.att ∧ 3 ≤ y.rank := by
  intro y hy
  rcases (mem_abortChunk s o y).1 hy with ⟨c, -, rfl⟩ | rfl <;> simp [Ev.att, Ev.rank]

/-- No event of stage 4 or below exceeds the ended phase's stage. -/
theorem rank_le_four (x : Ev) : x.rank ≤ 4 := by cases x <;> simp [Ev.rank]

/-- **Every step keeps the invariant.** -/
theorem step_inv {s t : T}
    -- The invariant holds before the step.
    (hs : Inv s)
    -- One step of the design.
    (hstep : Step s t) :
    Inv t := by
  cases hstep with
  | regCommit c hp hc =>
    -- The attempt has not ended, so it has no outcome yet.
    have hcur : s.cur = none := hs.cur_none (by rcases hp with h | h <;> simp [h])
    refine ⟨?_, hs.aborts_order, ?_, hs.aborts_nodup, ?_, hs.regA_le, hs.cur_ended, ?_, hs.cA,
      hs.hC, hs.hA, hs.att_le, hs.rank_le, hs.ordered, hs.bw_le, hs.bw_cur, hs.bw_validated,
      hs.validated_logged, hs.commit_validated⟩
    · -- `c` joins the end of this attempt's registrations.
      simp only [List.filter_append, List.map_append, hs.commits_order]
      simp
    · -- `c` is fresh in this attempt.
      rw [List.nodup_append]
      refine ⟨hs.commits_nodup, nodup_one c, ?_⟩
      intro x hx y hy hxy
      simp only [List.mem_singleton] at hy
      subst hy; subst hxy
      exact hc ((hs.mem_commits x).1 hx)
    · -- The new registration is of the current attempt.
      intro p hp'
      rcases List.mem_append.1 hp' with h | h
      · exact hs.regC_le p h
      · simp only [List.mem_singleton] at h; subst h; exact Nat.le_refl _
    · -- The new registration's attempt has no outcome: no count changes.
      intro a c'
      rw [hs.cC a c']
      by_cases ha : a = s.att
      · subst ha; simp [outcomeOf, hcur]
      · simp [ha, outcomeOf]
  | regAbort c hp hc =>
    have hcur : s.cur = none := hs.cur_none (by rcases hp with h | h <;> simp [h])
    refine ⟨hs.commits_order, ?_, hs.commits_nodup, ?_, hs.regC_le, ?_, hs.cur_ended, hs.cC, ?_,
      hs.hC, hs.hA, hs.att_le, hs.rank_le, hs.ordered, hs.bw_le, hs.bw_cur, hs.bw_validated,
      hs.validated_logged, hs.commit_validated⟩
    · simp only [List.filter_append, List.map_append, hs.aborts_order]
      simp
    · rw [List.nodup_append]
      refine ⟨hs.aborts_nodup, nodup_one c, ?_⟩
      intro x hx y hy hxy
      simp only [List.mem_singleton] at hy
      subst hy; subst hxy
      exact hc ((hs.mem_aborts x).1 hx)
    · intro p hp'
      rcases List.mem_append.1 hp' with h | h
      · exact hs.regA_le p h
      · simp only [List.mem_singleton] at h; subst h; exact Nat.le_refl _
    · intro a c' o
      rw [hs.cA a c' o]
      by_cases ha : a = s.att
      · subst ha; simp [outcomeOf, hcur]
      · simp [ha, outcomeOf]
  | regBefore c hp =>
    -- Only the pending before_commit list changes.
    exact ⟨hs.commits_order, hs.aborts_order, hs.commits_nodup, hs.aborts_nodup, hs.regC_le,
      hs.regA_le, hs.cur_ended, hs.cC, hs.cA, hs.hC, hs.hA, hs.att_le, hs.rank_le, hs.ordered,
      hs.bw_le, hs.bw_cur, hs.bw_validated, hs.validated_logged, hs.commit_validated⟩
  | write k hp =>
    -- Only the write set grows.
    exact ⟨hs.commits_order, hs.aborts_order, hs.commits_nodup, hs.aborts_nodup, hs.regC_le,
      hs.regA_le, hs.cur_ended, hs.cC, hs.cA, hs.hC, hs.hA, hs.att_le, hs.rank_le, hs.ordered,
      hs.bw_le, fun k' h => List.mem_append.2 (Or.inl (hs.bw_cur k' h)), hs.bw_validated,
      hs.validated_logged, hs.commit_validated⟩
  | commit hp =>
    -- Open becomes preparing: the same stage, still no outcome.
    have hcur : s.cur = none := hs.cur_none (by simp [hp])
    refine ⟨hs.commits_order, hs.aborts_order, hs.commits_nodup, hs.aborts_nodup, hs.regC_le,
      hs.regA_le, ?_, hs.cC, hs.cA, hs.hC, hs.hA, hs.att_le, ?_, hs.ordered, hs.bw_le, hs.bw_cur,
      hs.bw_validated, ?_, hs.commit_validated⟩
    · simp [hcur]
    · intro x hx hxa
      have := hs.rank_le x hx hxa
      simp only [hp, Phase.rank] at this ⊢
      exact this
    · intro ok h; simp at h
  | runBefore c rest ws hp hb =>
    have hcur : s.cur = none := hs.cur_none (by simp [hp])
    obtain ⟨hcC, hcA, hhC, hhA⟩ := counts_append_quiet (e := [Ev.before s.att c])
      hs.cC hs.cA hs.hC hs.hA (by simp [Ev.rank])
    refine ⟨hs.commits_order, hs.aborts_order, hs.commits_nodup, hs.aborts_nodup, hs.regC_le,
      hs.regA_le, hs.cur_ended, hcC, hcA, hhC, hhA, ?_, ?_, ?_, ?_, ?_, ?_,
      fun ok h => by simp [hp] at h, ?_⟩
    · -- The new event is of the current attempt.
      intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact hs.att_le x h
      · simp at h; subst h; simp [Ev.att]
    · -- Stage 0, which the preparing phase has reached.
      intro x hx hxa
      rcases List.mem_append.1 hx with h | h
      · exact hs.rank_le x h hxa
      · simp at h; subst h; simp [Ev.rank, hp, Phase.rank]
    · exact ordered_append hs.ordered (fun x hx hxa => hs.rank_le x hx hxa)
        (fun y hy => by simp at hy; subst hy; rfl)
        (fun y hy => by simp at hy; subst hy; simp [Ev.rank, hp, Phase.rank])
        (List.pairwise_singleton _ _)
    · -- The callback's writes are of the current attempt.
      intro p hp'
      rcases List.mem_append.1 hp' with h | h
      · exact hs.bw_le p h
      · simp only [List.mem_map] at h
        obtain ⟨k, -, rfl⟩ := h
        exact Nat.le_refl _
    · -- The callback's writes join the write set.
      intro k hk
      rcases List.mem_append.1 hk with h | h
      · exact List.mem_append.2 (Or.inl (hs.bw_cur k h))
      · simp only [List.mem_map, Prod.mk.injEq] at h
        obtain ⟨k', hk', -, rfl⟩ := h
        exact List.mem_append.2 (Or.inr hk')
    · -- No validation is added, and the current attempt has none yet.
      intro a k ws' hk hv
      rcases List.mem_append.1 hv with hv | hv
      · rcases List.mem_append.1 hk with h | h
        · exact hs.bw_validated a k ws' h hv
        · simp only [List.mem_map, Prod.mk.injEq] at h
          obtain ⟨k', -, rfl, rfl⟩ := h
          have := hs.rank_le _ hv rfl
          simp [Ev.rank, hp, Phase.rank] at this
      · simp at hv
    · intro a ha
      obtain ⟨ws', hws⟩ := hs.commit_validated a ha
      exact ⟨ws', List.mem_append.2 (Or.inl hws)⟩
  | hookBefore ws hp hb =>
    have hcur : s.cur = none := hs.cur_none (by simp [hp])
    obtain ⟨hcC, hcA, hhC, hhA⟩ := counts_append_quiet (e := [Ev.hookBefore s.att])
      hs.cC hs.cA hs.hC hs.hA (by simp [Ev.rank])
    refine ⟨hs.commits_order, hs.aborts_order, hs.commits_nodup, hs.aborts_nodup, hs.regC_le,
      hs.regA_le, by simp [hcur], hcC, hcA, hhC, hhA, ?_, ?_, ?_, ?_, ?_, ?_,
      fun ok h => by simp at h, ?_⟩
    · intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact hs.att_le x h
      · simp at h; subst h; simp [Ev.att]
    · -- Stage 1, the prepared phase's; older events of the attempt are 0.
      intro x hx hxa
      rcases List.mem_append.1 hx with h | h
      · have := hs.rank_le x h hxa
        simp only [hp, Phase.rank] at this
        simp only [Phase.rank]
        omega
      · simp at h; subst h; simp [Ev.rank, Phase.rank]
    · exact ordered_append hs.ordered (fun x hx hxa => hs.rank_le x hx hxa)
        (fun y hy => by simp at hy; subst hy; rfl)
        (fun y hy => by simp at hy; subst hy; simp [Ev.rank, hp, Phase.rank])
        (List.pairwise_singleton _ _)
    · intro p hp'
      rcases List.mem_append.1 hp' with h | h
      · exact hs.bw_le p h
      · simp only [List.mem_map] at h
        obtain ⟨k, -, rfl⟩ := h
        exact Nat.le_refl _
    · intro k hk
      rcases List.mem_append.1 hk with h | h
      · exact List.mem_append.2 (Or.inl (hs.bw_cur k h))
      · simp only [List.mem_map, Prod.mk.injEq] at h
        obtain ⟨k', hk', -, rfl⟩ := h
        exact List.mem_append.2 (Or.inr hk')
    · intro a k ws' hk hv
      rcases List.mem_append.1 hv with hv | hv
      · rcases List.mem_append.1 hk with h | h
        · exact hs.bw_validated a k ws' h hv
        · simp only [List.mem_map, Prod.mk.injEq] at h
          obtain ⟨k', -, rfl, rfl⟩ := h
          have := hs.rank_le _ hv rfl
          simp [Ev.rank, hp, Phase.rank] at this
      · simp at hv
    · intro a ha
      obtain ⟨ws', hws⟩ := hs.commit_validated a ha
      exact ⟨ws', List.mem_append.2 (Or.inl hws)⟩
  | validate ok hp =>
    have hcur : s.cur = none := hs.cur_none (by simp [hp])
    obtain ⟨hcC, hcA, hhC, hhA⟩ := counts_append_quiet (e := [Ev.validate s.att s.writes])
      hs.cC hs.cA hs.hC hs.hA (by simp [Ev.rank])
    refine ⟨hs.commits_order, hs.aborts_order, hs.commits_nodup, hs.aborts_nodup, hs.regC_le,
      hs.regA_le, by simp [hcur], hcC, hcA, hhC, hhA, ?_, ?_, ?_, hs.bw_le, hs.bw_cur, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact hs.att_le x h
      · simp at h; subst h; simp [Ev.att]
    · -- Stage 2, the validated phase's; older events of the attempt are at
      -- most 1.
      intro x hx hxa
      rcases List.mem_append.1 hx with h | h
      · have := hs.rank_le x h hxa
        simp only [hp, Phase.rank] at this
        simp only [Phase.rank]
        omega
      · simp at h; subst h; simp [Ev.rank, Phase.rank]
    · exact ordered_append hs.ordered (fun x hx hxa => hs.rank_le x hx hxa)
        (fun y hy => by simp at hy; subst hy; rfl)
        (fun y hy => by simp at hy; subst hy; simp [Ev.rank, hp, Phase.rank])
        (List.pairwise_singleton _ _)
    · -- The validation checks the whole write set, so every callback write
      -- of the attempt; an older attempt's validation is unchanged.
      intro a k ws' hk hv
      rcases List.mem_append.1 hv with hv | hv
      · exact hs.bw_validated a k ws' hk hv
      · simp only [List.mem_singleton, Ev.validate.injEq] at hv
        obtain ⟨rfl, rfl⟩ := hv
        exact hs.bw_cur k hk
    · intro ok' h
      exact ⟨s.writes, List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl))⟩
    · intro a ha
      obtain ⟨ws', hws⟩ := hs.commit_validated a ha
      exact ⟨ws', List.mem_append.2 (Or.inl hws)⟩
  | finishCommit hp =>
    have hcur : s.cur = none := hs.cur_none (by simp [hp])
    obtain ⟨hcC, hcA, hhC, hhA⟩ := counts_end (E := commitChunk s) (o := .commit)
      (t := { s with phase := .ended, cur := some .commit, log := s.log ++ commitChunk s })
      hs hcur rfl rfl rfl rfl rfl (commitChunk_nodup hs.commits_nodup)
      (commitChunk_memC s)
      (fun a c o' => by rw [mem_commitChunk]; simp)
      (fun a => by rw [mem_commitChunk]; simp)
      (fun a o' => by rw [mem_commitChunk]; simp)
    refine ⟨hs.commits_order, hs.aborts_order, hs.commits_nodup, hs.aborts_nodup, hs.regC_le,
      hs.regA_le, by simp, hcC, hcA, hhC, hhA, ?_, ?_, ?_, hs.bw_le, hs.bw_cur, ?_,
      fun ok h => by simp at h, ?_⟩
    · intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact hs.att_le x h
      · exact Nat.le_of_eq (commitChunk_att x h).1
    · intro x _ _; simp only [Phase.rank]; exact rank_le_four x
    · refine ordered_append hs.ordered (fun x hx hxa => hs.rank_le x hx hxa)
        (fun y hy => (commitChunk_att y hy).1) (fun y hy => ?_)
        (chunk_sorted (fun c => rfl) rfl)
      have := (commitChunk_att y hy).2
      simp only [hp, Phase.rank]
      omega
    · -- No validation is added.
      intro a k ws' hk hv
      rcases List.mem_append.1 hv with hv | hv
      · exact hs.bw_validated a k ws' hk hv
      · have := (commitChunk_att _ hv).2
        simp [Ev.rank] at this
    · -- The current attempt was validated; older ones as before.
      intro a ha
      by_cases h : a = s.att
      · subst h
        obtain ⟨ws', hws⟩ := hs.validated_logged true hp
        exact ⟨ws', List.mem_append.2 (Or.inl hws)⟩
      · have ha : outcomeOf s a = some .commit := by simp [outcomeOf, h] at ha ⊢
        obtain ⟨ws', hws⟩ := hs.commit_validated a ha
        exact ⟨ws', List.mem_append.2 (Or.inl hws)⟩
  | finishAbort o ho =>
    -- The phase allows this abort: it has not ended, and `o` is no commit.
    have hne : s.phase ≠ .ended := by
      rcases ho with ⟨h, -⟩ | ⟨h, -⟩
      · simp [h]
      · rcases h with h | h | h <;> simp [h]
    have hoc : o ≠ .commit := by
      rcases ho with ⟨-, h⟩ | ⟨-, h⟩
      · simp [h]
      · rcases h with h | h | h | h <;> simp [h]
    have hcur : s.cur = none := hs.cur_none hne
    have hrank : s.phase.rank ≤ 2 := by
      rcases ho with ⟨h, -⟩ | ⟨h, -⟩
      · simp [h, Phase.rank]
      · rcases h with h | h | h <;> simp [h, Phase.rank]
    obtain ⟨hcC, hcA, hhC, hhA⟩ := counts_end (E := abortChunk s o) (o := o)
      (t := { s with phase := .ended, cur := some o, log := s.log ++ abortChunk s o })
      hs hcur rfl rfl rfl rfl rfl (abortChunk_nodup hs.aborts_nodup)
      (fun a c => by rw [mem_abortChunk]; simp [hoc])
      (abortChunk_memA s hoc)
      (fun a => by rw [mem_abortChunk]; simp [hoc])
      (abortChunk_memHA s hoc)
    refine ⟨hs.commits_order, hs.aborts_order, hs.commits_nodup, hs.aborts_nodup, hs.regC_le,
      hs.regA_le, by simp, hcC, hcA, hhC, hhA, ?_, ?_, ?_, hs.bw_le, hs.bw_cur, ?_,
      fun ok h => by simp at h, ?_⟩
    · intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact hs.att_le x h
      · exact Nat.le_of_eq (abortChunk_att x h).1
    · intro x _ _; simp only [Phase.rank]; exact rank_le_four x
    · refine ordered_append hs.ordered (fun x hx hxa => hs.rank_le x hx hxa)
        (fun y hy => (abortChunk_att y hy).1) (fun y hy => ?_)
        (chunk_sorted (fun c => rfl) rfl)
      have := (abortChunk_att y hy).2
      omega
    · intro a k ws' hk hv
      rcases List.mem_append.1 hv with hv | hv
      · exact hs.bw_validated a k ws' hk hv
      · have := (abortChunk_att _ hv).2
        simp [Ev.rank] at this
    · -- The current attempt aborted; older ones as before.
      intro a ha
      by_cases h : a = s.att
      · subst h
        rw [outcomeOf_cur] at ha
        simp at ha
        exact absurd ha hoc
      · have ha : outcomeOf s a = some .commit := by simp [outcomeOf, h] at ha ⊢
        obtain ⟨ws', hws⟩ := hs.commit_validated a ha
        exact ⟨ws', List.mem_append.2 (Or.inl hws)⟩
  | panicBefore c rest hp hb =>
    have hcur : s.cur = none := hs.cur_none (by simp [hp])
    -- The panicking callback's event, then the abort chunk.
    have hnd : (Ev.before s.att c :: abortChunk s .panic).Nodup := by
      rw [List.nodup_cons]
      refine ⟨fun h => ?_, abortChunk_nodup hs.aborts_nodup⟩
      have := (abortChunk_att _ h).2
      simp [Ev.rank] at this
    obtain ⟨hcC, hcA, hhC, hhA⟩ := counts_end (E := Ev.before s.att c :: abortChunk s .panic)
      (o := .panic)
      (t := { s with phase := .ended, cur := some .panic, befores := rest,
                     log := s.log ++ (Ev.before s.att c :: abortChunk s .panic) })
      hs hcur rfl rfl rfl rfl rfl hnd
      (fun a c => by rw [List.mem_cons, mem_abortChunk]; simp)
      (fun a c o' => by
        rw [List.mem_cons, abortChunk_memA s (by simp) a c o']; simp)
      (fun a => by rw [List.mem_cons, mem_abortChunk]; simp)
      (fun a o' => by
        rw [List.mem_cons, abortChunk_memHA s (by simp) a o']; simp)
    refine ⟨hs.commits_order, hs.aborts_order, hs.commits_nodup, hs.aborts_nodup, hs.regC_le,
      hs.regA_le, by simp, hcC, hcA, hhC, hhA, ?_, ?_, ?_, hs.bw_le, hs.bw_cur, ?_,
      fun ok h => by simp at h, ?_⟩
    · intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact hs.att_le x h
      · rcases List.mem_cons.1 h with rfl | h
        · simp [Ev.att]
        · exact Nat.le_of_eq (abortChunk_att x h).1
    · intro x _ _; simp only [Phase.rank]; exact rank_le_four x
    · refine ordered_append hs.ordered (fun x hx hxa => hs.rank_le x hx hxa)
        (fun y hy => ?_) (fun y hy => ?_) ?_
      · rcases List.mem_cons.1 hy with rfl | h
        · rfl
        · exact (abortChunk_att y h).1
      · simp only [hp, Phase.rank]; exact Nat.zero_le _
      · -- The callback's event (stage 0) leads, then the sorted chunk.
        refine List.Pairwise.cons (fun y hy => ?_) (chunk_sorted (fun c => rfl) rfl)
        simp only [Ev.rank]; exact Nat.zero_le _
    · intro a k ws' hk hv
      rcases List.mem_append.1 hv with hv | hv
      · exact hs.bw_validated a k ws' hk hv
      · rcases List.mem_cons.1 hv with h | h
        · simp at h
        · have := (abortChunk_att _ h).2
          simp [Ev.rank] at this
    · intro a ha
      by_cases h : a = s.att
      · subst h
        simp [outcomeOf] at ha
      · have ha : outcomeOf s a = some .commit := by simp [outcomeOf, h] at ha ⊢
        obtain ⟨ws', hws⟩ := hs.commit_validated a ha
        exact ⟨ws', List.mem_append.2 (Or.inl hws)⟩
  | retry hp hc =>
    -- The next attempt starts with nothing registered; every outcome is as
    -- before, since the ended attempt's was a conflict.
    have hout : ∀ a, outcomeOf (retried s) a = outcomeOf s a := by
      intro a
      unfold outcomeOf retried
      simp only
      by_cases h1 : a < s.att
      · -- An earlier attempt: a conflict either way.
        simp [h1, show a < s.att + 1 by omega]
      · by_cases h2 : a = s.att
        · -- The attempt that just conflicted.
          subst h2; simp [hc]
        · -- A later attempt: no outcome either way.
          have h3 : ¬ a < s.att + 1 := by omega
          simp [h1, h2, h3]
    -- State it for the record the step produces, as the goals show it.
    simp only [retried] at hout
    refine ⟨?_, ?_, List.nodup_nil, List.nodup_nil, ?_, ?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_,
      hs.ordered, ?_, ?_, hs.bw_validated, fun ok h => by simp at h, ?_⟩
    · -- No registration is of the new attempt.
      simp only
      rw [List.filter_eq_nil_iff.2]
      · rfl
      · intro p hp'
        have := hs.regC_le p hp'
        simp only [beq_iff_eq]
        omega
    · simp only
      rw [List.filter_eq_nil_iff.2]
      · rfl
      · intro p hp'
        have := hs.regA_le p hp'
        simp only [beq_iff_eq]
        omega
    · intro p hp'; have := hs.regC_le p hp'; simp only; omega
    · intro p hp'; have := hs.regA_le p hp'; simp only; omega
    · intro a c; rw [hs.cC, hout]
    · intro a c o; rw [hs.cA, hout]
    · intro a; rw [hs.hC, hout]
    · intro a o; rw [hs.hA, hout]
    · intro x hx; have := hs.att_le x hx; simp only; omega
    · -- No event is of the new attempt.
      intro x hx hxa
      have := hs.att_le x hx
      simp only at hxa
      omega
    · intro p hp'; have := hs.bw_le p hp'; simp only; omega
    · -- No callback write is of the new attempt.
      intro k hk
      simp only at hk
      have := hs.bw_le _ hk
      simp only at this
      omega
    · intro a ha
      rw [hout] at ha
      exact hs.commit_validated a ha

/-- Several steps keep the invariant. -/
theorem steps_inv {s t : T}
    -- The invariant holds at the start.
    (hs : Inv s)
    -- Any number of steps.
    (hsteps : Steps s t) :
    Inv t := by
  induction hsteps with
  -- No step: nothing changed.
  | refl => exact hs
  -- The steps so far, then one more.
  | tail _ hstep ih => exact step_inv ih hstep

/-- **Every reachable state satisfies the invariant.** -/
theorem reachable_inv {s : T}
    -- `s` is reachable from the start.
    (h : Steps init s) : Inv s :=
  steps_inv init_inv h

/-! ## The laws -/

/-- **Exactly once.** For attempt `a` and callback `c`: on_commit callback
`c` ran once if it was registered in attempt `a` and `a` committed, and
never otherwise; on_abort callback `c` ran once, with reason `o`, if it was
registered in `a` and `a` ended aborted with `o`, and never otherwise; and
the hooks' outcome ran once for each ended attempt, of the matching kind.
An attempt still running has no outcome, so none of these ran for it.
TLA+: `AtMostOnce`, `ExactlyOnce`. -/
theorem exactly_once {s : T}
    -- `s` is reachable from the start.
    (h : Steps init s) (a c : Nat) :
    (s.log.count (.onCommit a c) =
      if (a, c) ∈ s.regC ∧ outcomeOf s a = some .commit then 1 else 0) ∧
    (∀ o, s.log.count (.onAbort a c o) =
      if (a, c) ∈ s.regA ∧ outcomeOf s a = some o ∧ o ≠ .commit then 1 else 0) ∧
    (s.log.count (.hookCommit a) = if outcomeOf s a = some .commit then 1 else 0) ∧
    (∀ o, s.log.count (.hookAbort a o) = if outcomeOf s a = some o ∧ o ≠ .commit then 1 else 0) :=
  let hs := reachable_inv h
  ⟨hs.cC a c, hs.cA a c, hs.hC a, hs.hA a⟩

/-- **Never both.** No attempt runs an on_commit callback and an on_abort
callback: once one of its on_commit callbacks ran, none of its on_abort
callbacks has run or will (the outcome is fixed). -/
theorem never_both {s : T}
    -- `s` is reachable from the start.
    (h : Steps init s) {a c c' : Nat} {o : Outcome}
    -- An on_commit callback of attempt `a` ran.
    (hc : Ev.onCommit a c ∈ s.log) :
    Ev.onAbort a c' o ∉ s.log := by
  have hs := reachable_inv h
  intro ha
  -- Each ran, so each one's condition holds: the outcome is a commit and
  -- is an abort.
  have h1 := List.count_pos_iff.2 hc
  have h2 := List.count_pos_iff.2 ha
  rw [hs.cC] at h1
  rw [hs.cA] at h2
  split at h1
  · split at h2
    · rename_i hx hy
      rw [hx.2] at hy
      simp at hy
      exact hy.2.2 hy.2.1.symm
    · omega
  · omega

/-- **Order.** Within an attempt, an event of an earlier stage comes before
every event of a later stage: before_commit callbacks, then the hooks'
before_commit, then validation, then the transaction's outcome callbacks,
then the hooks' outcome. TLA+: `CallbacksBeforeHooks`. -/
theorem order {s : T}
    -- `s` is reachable from the start.
    (h : Steps init s) {x y : Ev}
    -- Both ran.
    (hx : x ∈ s.log) (hy : y ∈ s.log)
    -- In the same attempt.
    (hatt : x.att = y.att)
    -- `x` is of an earlier stage.
    (hr : x.rank < y.rank) :
    [x, y].Sublist s.log :=
  (reachable_inv h).ordered x hx y hy hatt hr

/-- **The transaction's callbacks before the hooks'.** When an on_commit
callback of attempt `a` ran, the hooks' on_commit ran too, after it. -/
theorem callbacks_before_hooks {s : T}
    -- `s` is reachable from the start.
    (h : Steps init s) {a c : Nat}
    -- An on_commit callback of attempt `a` ran.
    (hc : Ev.onCommit a c ∈ s.log) :
    Ev.hookCommit a ∈ s.log ∧ [Ev.onCommit a c, Ev.hookCommit a].Sublist s.log := by
  have hs := reachable_inv h
  -- The callback ran, so `a` committed, so the hook ran once.
  have h1 := List.count_pos_iff.2 hc
  rw [hs.cC] at h1
  have hcommit : outcomeOf s a = some .commit := by
    split at h1
    · rename_i hx; exact hx.2
    · omega
  have hhook : Ev.hookCommit a ∈ s.log := by
    apply List.count_pos_iff.1
    rw [hs.hC]
    simp [hcommit]
  exact ⟨hhook, hs.ordered _ hc _ hhook rfl (by simp [Ev.rank])⟩

/-- **A commit was validated first.** When an on_commit callback of
attempt `a` ran, attempt `a` was validated, before it. -/
theorem commit_was_validated {s : T}
    -- `s` is reachable from the start.
    (h : Steps init s) {a c : Nat}
    -- An on_commit callback of attempt `a` ran.
    (hc : Ev.onCommit a c ∈ s.log) :
    ∃ ws, Ev.validate a ws ∈ s.log ∧ [Ev.validate a ws, Ev.onCommit a c].Sublist s.log := by
  have hs := reachable_inv h
  have h1 := List.count_pos_iff.2 hc
  rw [hs.cC] at h1
  have hcommit : outcomeOf s a = some .commit := by
    split at h1
    · rename_i hx; exact hx.2
    · omega
  obtain ⟨ws, hws⟩ := hs.commit_validated a hcommit
  exact ⟨ws, hws, hs.ordered _ hws _ hc rfl (by simp [Ev.rank])⟩

/-- **Outcome callbacks in registration order.** In any state the
invariant holds in, a commit runs the attempt's on_commit callbacks in the
order they were registered, then the hooks' on_commit. -/
theorem finish_commit_runs {s : T}
    -- The invariant holds.
    (hs : Inv s) :
    commitChunk s =
      ((s.regC.filter (fun p => p.1 == s.att)).map Prod.snd).map (Ev.onCommit s.att) ++
        [Ev.hookCommit s.att] := by
  unfold commitChunk
  rw [hs.commits_order]

/-- **Outcome callbacks in registration order.** An abort runs the
attempt's on_abort callbacks in the order they were registered, then the
hooks' on_abort. -/
theorem finish_abort_runs {s : T}
    -- The invariant holds.
    (hs : Inv s) (o : Outcome) :
    abortChunk s o =
      ((s.regA.filter (fun p => p.1 == s.att)).map Prod.snd).map (fun c => Ev.onAbort s.att c o) ++
        [Ev.hookAbort s.att o] := by
  unfold abortChunk
  rw [hs.aborts_order]

/-- **Before_commit writes are validated.** Every key a before_commit
callback (or the hooks' before_commit) of attempt `a` wrote is in the write
set attempt `a` validated. TLA+: `NoLostUpdate`. -/
theorem before_writes_validated {s : T}
    -- `s` is reachable from the start.
    (h : Steps init s) {a k : Nat} {ws : List Nat}
    -- A before_commit callback of attempt `a` wrote `k`.
    (hk : (a, k) ∈ s.bw)
    -- Attempt `a` was validated with write set `ws`.
    (hv : Ev.validate a ws ∈ s.log) :
    k ∈ ws :=
  (reachable_inv h).bw_validated a k ws hk hv

/-- **Attempts are isolated.** An on_commit or on_abort callback that ran
for attempt `a` was registered in attempt `a`, and reports `a`'s own
outcome: a re-run never runs a previous attempt's callbacks. TLA+:
`AttemptIsolation`. -/
theorem attempts_isolated {s : T}
    -- `s` is reachable from the start.
    (h : Steps init s) {a c : Nat} :
    (Ev.onCommit a c ∈ s.log → (a, c) ∈ s.regC ∧ outcomeOf s a = some .commit) ∧
    (∀ o, Ev.onAbort a c o ∈ s.log → (a, c) ∈ s.regA ∧ outcomeOf s a = some o) := by
  have hs := reachable_inv h
  refine ⟨fun hc => ?_, fun o ha => ?_⟩
  · -- It ran, so its condition holds.
    have h1 := List.count_pos_iff.2 hc
    rw [hs.cC] at h1
    split at h1
    · rename_i hx; exact hx
    · omega
  · have h1 := List.count_pos_iff.2 ha
    rw [hs.cA] at h1
    split at h1
    · rename_i hx; exact ⟨hx.1, hx.2.1⟩
    · omega

/-- **A panic in before_commit aborts.** If the next before_commit callback
panics, the attempt ends with reason `panic`: every on_abort callback of
the attempt has run with it, and no on_commit callback. TLA+: `PanicAborts`. -/
theorem panic_aborts {s : T}
    -- The invariant holds.
    (hs : Inv s) {c : Nat} {rest : List Nat}
    -- The before_commit pass is running.
    (hp : s.phase = .preparing)
    -- `c` is the next before_commit callback, and it panics.
    (hb : s.befores = c :: rest) :
    let t : T := { s with phase := .ended, cur := some .panic, befores := rest,
                          log := s.log ++ (Ev.before s.att c :: abortChunk s .panic) }
    Step s t ∧ outcomeOf t s.att = some .panic ∧
      (∀ c' ∈ s.aborts, Ev.onAbort s.att c' .panic ∈ t.log) ∧
      (∀ c', Ev.onCommit s.att c' ∉ t.log) := by
  intro t
  have hstep : Step s t := Step.panicBefore s c rest hp hb
  have ht := step_inv hs hstep
  have hout : outcomeOf t s.att = some .panic := by simp [outcomeOf, t]
  refine ⟨hstep, hout, fun c' hc' => ?_, fun c' hm => ?_⟩
  · -- Registered in this attempt, which aborted with `panic`: it ran once.
    apply List.count_pos_iff.1
    have hcond : (s.att, c') ∈ t.regA ∧ outcomeOf t s.att = some .panic ∧ Outcome.panic ≠ .commit :=
      ⟨(hs.mem_aborts c').1 hc', hout, by simp⟩
    rw [ht.cA]
    simp [hcond]
  · -- The attempt did not commit, so no on_commit callback ran.
    have h1 := List.count_pos_iff.2 hm
    rw [ht.cC, hout] at h1
    simp at h1

/-! ## The RED case: callbacks that survive a conflict -/

/-- The defective design: the re-run keeps the conflicted attempt's
on_commit and on_abort callbacks registered on the transaction. -/
inductive StepKeep : T → T → Prop
  /-- Every step of the design. -/
  | step {s t : T}
      -- A step of the design.
      (h : Step s t) : StepKeep s t
  /-- The defect: a re-run that clears the writes but not the callbacks. -/
  | retryKeep (s : T)
      -- The attempt ended ...
      (hp : s.phase = .ended)
      -- ... with a conflict.
      (hc : s.cur = some .conflict) :
      StepKeep s { s with att := s.att + 1, phase := .open_, cur := none, befores := [],
                          writes := [] }

/-- Any number of `StepKeep` steps. -/
inductive StepsKeep : T → T → Prop
  /-- No step at all. -/
  | refl (s : T) : StepsKeep s s
  /-- Some steps, then one more. -/
  | tail {s t u : T} : StepsKeep s t → StepKeep t u → StepsKeep s u

/-- **`surviving_callbacks_break_isolation`.** Attempt 0 registers
on_commit callback 5, is validated with a conflict and aborts. The re-run,
attempt 1, keeps callback 5, is validated cleanly and commits: callback 5
runs for attempt 1's commit although it was registered in attempt 0, whose
outcome was the conflict. `attempts_isolated` fails. -/
theorem surviving_callbacks_break_isolation :
    ∃ t, StepsKeep init t ∧ Ev.onCommit 1 5 ∈ t.log ∧ (1, 5) ∉ t.regC ∧
      Ev.hookAbort 0 .conflict ∈ t.log := by
  refine ⟨_, .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.refl init)
      -- Attempt 0 registers on_commit callback 5 and commits.
      (.step (.regCommit _ 5 (Or.inl rfl) (by decide))))
      (.step (.commit _ rfl)))
      (.step (.hookBefore _ [] rfl rfl)))
      -- Validation finds a conflict; attempt 0 aborts.
      (.step (.validate _ false rfl)))
      (.step (.finishAbort _ .conflict (Or.inl ⟨rfl, rfl⟩))))
      -- The defective re-run keeps callback 5.
      (.retryKeep _ rfl rfl))
      -- Attempt 1 commits cleanly.
      (.step (.commit _ rfl)))
      (.step (.hookBefore _ [] rfl rfl)))
      (.step (.validate _ true rfl)))
      (.step (.finishCommit _ rfl)), by decide, by decide, by decide⟩

/-! ## Delivery on the committing thread (D53)

Above, an attempt's outcome runs its callbacks once. Here is who runs them
and how often, once the outcome comes back through a `CommitTicket`. The
ticket's `Completion` (`src/io_queue/completion.rs`) is decided by the
pipeline, then *delivered*: one compare-and-swap from "decided" to
"delivering" lets one deliverer in, and only that one runs the callbacks.
Every deliverer runs on the thread that holds the commit's queue at that
moment: the queue's poll, the queue's drop (the queue may have moved to
another thread, which then holds it), or the commit's own fallback when its
queue went away before the ticket was registered. A committer that decided
or synced the group is never a deliverer.

Tiny example. Thread A commits with `commit_nowait`; thread B's poll lands
A's group. B only puts a note in A's inbox. A's next poll claims the outcome
and runs A's `on_commit` on A. If A drops its queue at the same moment, the
drop and the poll race for the claim; one wins, and `on_commit` runs once. -/

/-- Who can run an outcome's callbacks: the thread holding the commit's
queue, or (only in the RED case) a committer. -/
inductive Runner where
  /-- The thread `t` that holds the commit's queue. -/
  | holder (t : Nat)
  /-- A committer `c` that decided or synced the commit. -/
  | committer (c : Nat)
  -- Two runners can be compared for equality.
  deriving DecidableEq

/-- Where a ticket's outcome is (`Completion`'s state word). -/
inductive DState where
  /-- Not decided yet. -/
  | pending
  /-- Decided by the pipeline, not delivered. -/
  | decided
  /-- One deliverer won the claim and is running the callbacks. -/
  | delivering
  /-- Delivered: the ticket is ready. -/
  | ready
  -- Two states can be compared for equality.
  deriving DecidableEq

/-- One commit's ticket. -/
structure Ticket where
  /-- The thread holding the commit's queue now. -/
  holder : Nat
  /-- The outcome's state. -/
  st : DState
  /-- Ghost: every run of the outcome callbacks, by who ran it. -/
  ran : List Runner

/-- The steps of one ticket, one atomic step each. -/
inductive DStep : Ticket → Ticket → Prop
  /-- The pipeline decides the outcome. -/
  | decide (k : Ticket)
      -- It was not decided.
      (h : k.st = .pending) :
      -- The state after the step:
      DStep k { k with st := .decided }
  /-- The queue moves to thread `t`, which holds it from now on (the queue is
  `Send`). -/
  | move (k : Ticket) (t : Nat) :
      -- The state after the step:
      DStep k { k with holder := t }
  /-- A deliverer on the holding thread (the poll, the drop, or the commit's
  own fallback) claims the decided outcome with one CAS and runs the
  callbacks there. -/
  | deliver (k : Ticket)
      -- The CAS succeeds only on a decided outcome.
      (h : k.st = .decided) :
      -- The state after the step:
      DStep k { k with st := .delivering, ran := .holder k.holder :: k.ran }
  /-- The deliverer finishes: the ticket is ready. -/
  | finish (k : Ticket)
      -- It is the winner, delivering.
      (h : k.st = .delivering) :
      -- The state after the step:
      DStep k { k with st := .ready }

/-- Any number of ticket steps, one after another. -/
inductive DSteps : Ticket → Ticket → Prop
  /-- No step at all. -/
  | refl (k : Ticket) : DSteps k k
  /-- Some steps, then one more. -/
  | tail {a b c : Ticket} : DSteps a b → DStep b c → DSteps a c

/-- What holds of a ticket in every reachable state. -/
structure DInv (k : Ticket) : Prop where
  /-- Before the claim nobody ran the callbacks. -/
  before : k.st = .pending ∨ k.st = .decided → k.ran = []
  /-- After it, exactly one run. -/
  after : k.st = .delivering ∨ k.st = .ready → k.ran.length = 1
  /-- Every run was by a thread holding the queue. -/
  holder : ∀ r ∈ k.ran, ∃ t, r = .holder t

/-- A fresh ticket, its queue on thread `t`, satisfies the invariant. -/
theorem dinv_init (t : Nat) : DInv ⟨t, .pending, []⟩ := by
  -- Nothing ran; the state is pending, never delivering or ready.
  refine ⟨fun _ => rfl, fun h => ?_, fun r hr => ?_⟩
  · -- Pending is neither delivering nor ready.
    rcases h with h | h <;> cases h
  · -- No run is on the empty list.
    cases hr

/-- **One step keeps the invariant.** -/
theorem dstep_inv {k k' : Ticket}
    -- The invariant holds before the step.
    (hi : DInv k)
    -- One step.
    (h : DStep k k') :
    -- Then:
    DInv k' := by
  -- Look at the step.
  cases h with
  -- Deciding: from pending to decided, still nothing ran.
  | decide hp =>
    -- Nothing ran before, as the outcome was pending.
    have hr : k.ran = [] := hi.before (Or.inl hp)
    -- Decided is not delivering or ready, and the runs are untouched.
    refine ⟨fun _ => hr, fun h => ?_, hi.holder⟩
    -- Decided is neither delivering nor ready.
    rcases h with h | h <;> cases h
  -- Moving the queue changes only who holds it.
  | move t =>
    -- The state and the runs are untouched.
    exact ⟨hi.before, hi.after, hi.holder⟩
  -- The claim: one run, by the holder.
  | deliver hd =>
    -- Nothing ran before, as the outcome was only decided.
    have hr : k.ran = [] := hi.before (Or.inr hd)
    -- Delivering now, with exactly the one new run.
    refine ⟨fun h => ?_, fun _ => ?_, fun r hm => ?_⟩
    · -- Delivering is neither pending nor decided.
      rcases h with h | h <;> cases h
    · -- One run: the new one on an empty list.
      simp [hr]
    · -- The only run is the holder's.
      simp [hr] at hm
      -- It is `.holder` of the thread that held the queue.
      exact ⟨k.holder, hm⟩
  -- Finishing: ready, the runs untouched.
  | finish hd =>
    -- The single run stays.
    have hl : k.ran.length = 1 := hi.after (Or.inl hd)
    -- Ready is neither pending nor decided.
    refine ⟨fun h => ?_, fun _ => hl, hi.holder⟩
    -- Ready is neither pending nor decided.
    rcases h with h | h <;> cases h

/-- **The invariant holds after any number of steps.** -/
theorem dsteps_inv {k k' : Ticket}
    -- Steps from `k` to `k'`.
    (h : DSteps k k')
    -- The invariant holds at `k`.
    (hi : DInv k) :
    -- Then:
    DInv k' := by
  -- By induction on the steps.
  induction h with
  -- No step: the same state.
  | refl => exact hi
  -- Steps, then one more: the last step keeps it.
  | tail _ hs ih => exact dstep_inv ih hs

/-- **An outcome is delivered at most once, and exactly once when the
ticket is ready**, however many paths (the poll, the drop, the fallback)
try. TLA+: `AtMostOnce` and `ExactlyOnce` (`TxnCallbacks.tla`, with
`MC_TxnCallbacks_Red_DeliverNoClaim` as the RED). Rules out: the poll and
the queue's drop both running A's `on_commit`. -/
theorem delivered_once {t : Nat} {k : Ticket}
    -- `k` is reachable from a fresh ticket.
    (h : DSteps ⟨t, .pending, []⟩ k) :
    -- Then:
    k.ran.length ≤ 1 ∧ (k.st = .ready → k.ran.length = 1) := by
  -- The invariant of `k`.
  have hi := dsteps_inv h (dinv_init t)
  -- The second half is one field.
  refine ⟨?_, fun hr => hi.after (Or.inr hr)⟩
  -- Every state is before or after the claim; count the runs in each.
  cases hs : k.st with
  -- Pending: no run.
  | pending => simp [hi.before (Or.inl hs)]
  -- Decided: no run.
  | decided => simp [hi.before (Or.inr hs)]
  -- Delivering: one run.
  | delivering => simp [hi.after (Or.inl hs)]
  -- Ready: one run.
  | ready => simp [hi.after (Or.inr hs)]

/-- **Every delivery runs on the thread that holds the commit's queue**,
never on a committer. TLA+: `OnCommittingThread`, with
`MC_TxnCallbacks_Red_HelperDelivers` as the RED. Rules out: thread B, which
landed A's group, running A's `on_commit` on B. -/
theorem delivered_on_queue_thread {t : Nat} {k : Ticket}
    -- `k` is reachable from a fresh ticket.
    (h : DSteps ⟨t, .pending, []⟩ k)
    -- A run of the outcome callbacks.
    {r : Runner} (hr : r ∈ k.ran) :
    -- Then:
    ∃ q, r = .holder q :=
  -- One field of the invariant.
  (dsteps_inv h (dinv_init t)).holder r hr

/-! ### RED: delivering without the claim

The bug: a deliverer checks that the outcome is decided and runs the
callbacks, but does not CAS the state word, so a second path delivers
too. -/

/-- The broken deliver: the outcome stays decided. -/
def deliverNoClaim (k : Ticket) : Ticket :=
  -- One more run by the holder; the state word is left as it was.
  { k with ran := .holder k.holder :: k.ran }

/-- **RED: without the claim an outcome is delivered twice.** The poll and
the queue's drop both find the outcome decided and both run its
callbacks. TLA+: `MC_TxnCallbacks_Red_DeliverNoClaim` breaks `AtMostOnce`. -/
theorem no_claim_delivers_twice :
    -- Two broken deliveries of a decided outcome make two runs.
    (deliverNoClaim (deliverNoClaim ⟨1, .decided, []⟩)).ran.length = 2 := by
  -- Two runs, one per broken delivery.
  rfl

end Regolith.Callbacks
