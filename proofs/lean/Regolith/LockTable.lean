-- The barging lock and its proofs, which this file builds on.
import Regolith.Sync

/-!
# LockTable: the pessimistic lock table (plan 4.6, 4.10, 4.11; D49, D53)

This file backs the TLA+ model `proofs/tla/LockTable.tla` (configurations
`MC_LockTable_*`). TLC checks the protocol there step by atomic step, for
three or four transactions. Here the same rules are proved for every number
of transactions, every number of steps and every bound.

## The story

A pessimistic transaction locks a key before it reads or writes it. The
key's lock is the barging lock of `Regolith.Sync` (the code reuses
`regolith::sync`'s wait queue for it, `src/sync/owned_lock.rs`), so this
file does not prove that lock again: it builds the lock table on top of it
and proves what the table adds.

Tiny example. Transactions 1 and 2 want the same key; each runs on its own
thread, and each thread has its own inbox (its `IoQueue`).

1. 1 takes the lock. 2 asks without waiting (`try_get_for_update`), finds
   the lock taken, joins the lock's line and goes back to other work.
2. 1 commits with `commit_nowait`: its commit is written, not yet visible.
   The lock stays held. If it were released now, 2 would read the key
   without 1's commit in it.
3. The commit lands (becomes visible), on whatever thread. Only now is the
   lock released. The release wakes 2: a note "the lock may be free" goes
   into 2's own inbox, never into anybody else's.
4. 2's thread looks at its inbox; only that makes 2's wait ready. 2 asks
   again and takes the lock.

What is proved, in plain words:

1. `mutual_exclusion`: at most one transaction holds the key. And
   `retired_unused`: a table entry that left the table has no user, so two
   transactions can never hold two different locks for one key. TLA+:
   `MutualExclusion`, `TableSound`.
2. `no_stranded_front` and `handed_is_told`: while the lock is free the
   front waiter has been told, and a waiter handed the lock has been told;
   told means its note is in its own inbox or its wait is ready. TLA+:
   `NoStrandedFront`, `WokenIsTold`.
3. `bounded_bypass`: a waiter never loses more than `B` races. TLA+:
   `BoundedBypass`.
4. `note_on_own_queue` and `ready_by_own_queue`: a note is only ever in the
   inbox of the transaction it is for, and a wait is made ready only by
   that transaction's own inbox being read. TLA+: `OwnQueue`.
5. `isolation_at_landing`: while a commit is written and not yet visible,
   only its own transaction holds the key. TLA+: `IsolationAtLanding`.
6. The RED cases, as counterexamples: `retire_unchecked_strands_a_user`,
   `undelivered_note_strands`, `unbounded_barging_breaks_bound`,
   `wrong_queue_breaks_own_queue` and `release_at_write_breaks_isolation`.

How to read the Lean: `def` defines a function or a property, `theorem`
states a fact and its proof follows `:= by`. Lines starting with `--` are
comments. `l.filter p` keeps the elements of `l` that pass the test `p`;
`decide P` turns a yes-or-no fact `P` into the answer `true` or `false`.
-/

-- Everything below is named Regolith.LockTable.<name>.
namespace Regolith.LockTable

/-! ## A table entry and its use count -/

/-- One entry of the lock table: the lock of one key (`KeyLock` in
`src/transaction/lock_table.rs`), as far as its use count goes. -/
structure Entry where
  /-- The use count (`KeyLock::uses`): how many calls use the entry. -/
  uses : Nat
  /-- The entry left the table (`RETIRED`). -/
  retired : Bool
  /-- Ghost: the calls that hold a use right now, by name. -/
  users : List Nat

/-- A new entry, used once already by the call `r` that made it
(`KeyLock::new` starts the count at 1). -/
def Entry.made (r : Nat) : Entry := ⟨1, false, [r]⟩

/-- The steps of an entry's use count. -/
inductive EStep : Entry → Entry → Prop
  /-- A call looks the entry up and takes a use (`KeyLock::pin`): the
  compare-and-swap refuses a retired entry. -/
  | pin (s : Entry) (r : Nat)
      -- The entry is still in the table.
      (h : s.retired = false) :
      -- After: one more use, and `r` is among the users.
      EStep s { s with uses := s.uses + 1, users := r :: s.users }
  /-- A call gives its use back (`LockTable::unpin`, the decrement). -/
  | unpin (s : Entry) (r : Nat)
      -- `r` holds a use.
      (h : r ∈ s.users) :
      -- After: one use fewer, and `r` is no longer among the users.
      EStep s { s with uses := s.uses - 1, users := s.users.erase r }
  /-- The entry is taken out of the table (`KeyLock::retire`): one
  compare-and-swap that succeeds only from a count of zero. -/
  | retire (s : Entry)
      -- Nobody uses it.
      (h : s.uses = 0) :
      -- After: the entry is marked retired.
      EStep s { s with retired := true }

/-- Any number of entry steps, one after another. -/
inductive ESteps : Entry → Entry → Prop
  /-- No step at all. -/
  | refl (s : Entry) : ESteps s s
  /-- Some steps, then one more. -/
  | tail {s t u : Entry} : ESteps s t → EStep t u → ESteps s u

/-- What stays true of an entry: the count is exactly the number of users,
and a retired entry has none. -/
def EInv (s : Entry) : Prop :=
  -- The count is the number of users, and if the entry is retired the user
  -- list is empty.
  s.uses = s.users.length ∧ (s.retired = true → s.users = [])

/-- Every entry step keeps `EInv`. -/
theorem estep_inv {s t : Entry}
    -- It held before the step.
    (hs : EInv s)
    -- One step.
    (h : EStep s t) :
    -- Then it holds after the step.
    EInv t := by
  -- Split the invariant into its two halves.
  obtain ⟨hc, hr⟩ := hs
  -- Look at which step was taken.
  cases h with
  -- A call took a use.
  | pin r hret =>
    -- One more use and one more user; the entry is not retired, so the
    -- second half asks nothing.
    refine ⟨by simp [hc], fun hx => ?_⟩
    -- "Retired" contradicts the step's condition.
    simp [hret] at hx
  -- A call gave its use back.
  | unpin r hmem =>
    -- One use fewer, and the user list is one shorter.
    refine ⟨by simp [hc, List.length_erase_of_mem hmem], fun hx => ?_⟩
    -- A retired entry had no users, but `r` was one: impossible.
    have := hr hx
    -- Rewrite the user list as empty in "`r` is a user".
    rw [this] at hmem
    -- Nothing is a member of the empty list.
    simp at hmem
  -- The entry was retired.
  | retire hzero =>
    -- The count does not change; a count of zero means no users.
    refine ⟨hc, fun _ => ?_⟩
    -- The user list has length zero,
    have hl : s.users.length = 0 := by omega
    -- so it is the empty list.
    exact List.length_eq_zero_iff.1 hl

/-- Any number of entry steps keep `EInv`. -/
theorem esteps_inv {s t : Entry}
    -- It held at the start.
    (hs : EInv s)
    -- Any number of steps.
    (h : ESteps s t) :
    -- Then it holds at the end.
    EInv t := by
  -- By induction on the steps taken.
  induction h with
  -- No step: nothing changed.
  | refl => exact hs
  -- The steps so far, then one more, which keeps it.
  | tail _ hstep ih => exact estep_inv ih hstep

/-- **A retired entry is used by nobody.** Once an entry has left the
table, no call holds a use of it: nobody holds its lock, waits in its line
or is about to take it. So the key's next entry is the only one in use, and
two transactions never hold two locks for one key. TLA+: `TableSound`. -/
theorem retired_unused {r : Nat} {s : Entry}
    -- `s` is reachable from a freshly made entry.
    (h : ESteps (Entry.made r) s)
    -- It has left the table.
    (hret : s.retired = true) :
    -- Then nobody uses it.
    s.users = [] := by
  -- A freshly made entry has one use, one user, and is not retired.
  have h0 : EInv (Entry.made r) := ⟨rfl, fun hx => by simp [Entry.made] at hx⟩
  -- So the invariant holds in `s`, and its second half is the claim.
  exact (esteps_inv h0 h).2 hret

/-! ## The table: a lock, inboxes and pending commits -/

/-- The state of one key in the lock table. A transaction's lock call is
named by a natural number, as a request is in `Regolith.Sync`. -/
structure T where
  /-- The key's lock: who holds it, who waits, who was woken
  (`OwnedLock`, proved in `Regolith.Sync`). -/
  lock : Sync.M
  /-- Each thread's inbox (`QueueShared::inbox`): the waits whose note
  "the lock may be free" was pushed there and not read yet. -/
  inbox : Nat → List Nat
  /-- The waits that are ready, each with the thread whose reading of its
  inbox made it ready (`WaitSlot::complete`). -/
  ready : List (Nat × Nat)
  /-- The transactions whose commit is written and not yet visible
  (`commit_nowait` before the commit lands). -/
  pending : List Nat

/-- The start: the lock free, every inbox empty, nothing ready, nothing
pending. -/
def init : T := ⟨Sync.init, fun _ => [], [], []⟩

/-- The inbox of thread `q` after the lock moved from `old` to `new`. A
note is kept only while its wait is still woken (a waiter that tried again
or gave up has used its note up). Every request the step newly woke gets a
note, in the inbox of its own thread `Q r` (`Note::deliver`). -/
def notes (Q : Nat → Nat) (old new : Sync.M) (inbox : Nat → List Nat) (q : Nat) : List Nat :=
  -- The old notes of inbox `q` whose request is still woken, then the
  -- requests the step newly woke whose own thread is `q`.
  (inbox q).filter (fun r => decide (r ∈ new.woken)) ++
    new.woken.filter (fun r => decide (r ∉ old.woken) && decide (Q r = q))

/-- The steps of the table, for bound `B`, where `Q r` is the thread (and
inbox) of transaction `r`. -/
inductive Step (B : Nat) (Q : Nat → Nat) : T → T → Prop
  /-- Any step of the key's lock: a take, a wait, a release, a retry, a
  give-up. Every waiter it wakes is told through its own inbox. It may not
  take the lock from a transaction whose commit is still pending: the code
  releases a `commit_nowait`'s lock only when the commit has landed. -/
  | lock (s : T) (m : Sync.M)
      -- The lock takes one of its own steps.
      (h : Sync.Step B s.lock m)
      -- Every pending committer still owns the lock afterwards.
      (keep : ∀ r ∈ s.pending, r ∈ m.owners) :
      -- After: the lock is `m`, the notes are delivered, a ready wait is kept
      -- only while its request is still woken, and the pending commits stay.
      Step B Q s ⟨m, notes Q s.lock m s.inbox,
                  s.ready.filter (fun p => decide (p.1 ∈ m.woken)), s.pending⟩
  /-- Thread `q` reads its inbox (`IoQueue::poll`): every note in it makes
  its wait ready, and it is `q` that made it ready. -/
  | poll (s : T) (q : Nat) :
      -- After: inbox `q` is empty, and each note that was in it is a ready
      -- wait, made ready by `q`.
      Step B Q s { s with inbox := fun x => if x = q then [] else s.inbox x,
                          ready := s.ready ++ (s.inbox q).map (fun r => (r, q)) }
  /-- A holder commits with `commit_nowait`: its commit is written and not
  yet visible. The lock is not touched. -/
  | write (s : T) (r : Nat)
      -- `r` holds the lock.
      (hr : r ∈ s.lock.owners) :
      -- After: `r` is among the pending commits.
      Step B Q s { s with pending := r :: s.pending }
  /-- The commit lands: it is visible now. From here on its transaction
  may release the lock like any holder. -/
  | land (s : T) (r : Nat) :
      -- After: `r` is no longer among the pending commits.
      Step B Q s { s with pending := s.pending.filter (fun x => decide (x ≠ r)) }

/-- Any number of table steps, one after another. -/
inductive Steps (B : Nat) (Q : Nat → Nat) : T → T → Prop
  /-- No step at all. -/
  | refl (s : T) : Steps B Q s s
  /-- Some steps, then one more. -/
  | tail {s t u : T} : Steps B Q s t → Step B Q t u → Steps B Q s u

/-- A request has been told that the lock may be its: the note is in its
own thread's inbox, or its wait was made ready by its own thread. -/
def Told (Q : Nat → Nat) (s : T) (r : Nat) : Prop :=
  -- Its note is in its own thread's inbox, or its wait is ready and its
  -- own thread made it so.
  r ∈ s.inbox (Q r) ∨ (r, Q r) ∈ s.ready

/-- What stays true of the table. -/
structure Inv (Q : Nat → Nat) (s : T) : Prop where
  /-- Every woken request has been told. -/
  told : ∀ r ∈ s.lock.woken, Told Q s r
  /-- A note sits only in the inbox of the request's own thread. -/
  own_inbox : ∀ q r, r ∈ s.inbox q → Q r = q
  /-- A wait was made ready only by its own thread. -/
  own_ready : ∀ r q, (r, q) ∈ s.ready → q = Q r
  /-- Every note is for a request that is still woken: none is stale. -/
  fresh_inbox : ∀ q r, r ∈ s.inbox q → r ∈ s.lock.woken
  /-- Every ready wait is of a request that is still woken. -/
  fresh_ready : ∀ r q, (r, q) ∈ s.ready → r ∈ s.lock.woken
  /-- A transaction whose commit is pending holds the lock. -/
  pending_holds : ∀ r ∈ s.pending, r ∈ s.lock.owners

/-- The invariant holds at the start: nothing is woken, noted, ready or
pending. -/
theorem init_inv (Q : Nat → Nat) : Inv Q init where
  -- Nobody is woken at the start.
  told := fun r hr => by simp [init, Sync.init] at hr
  -- Every inbox is empty.
  own_inbox := fun q r hr => by simp [init] at hr
  -- Nothing is ready.
  own_ready := fun r q hr => by simp [init] at hr
  -- Every inbox is empty.
  fresh_inbox := fun q r hr => by simp [init] at hr
  -- Nothing is ready.
  fresh_ready := fun r q hr => by simp [init] at hr
  -- Nothing is pending.
  pending_holds := fun r hr => by simp [init] at hr

/-- Every table step keeps the invariant. -/
theorem step_inv {B : Nat} {Q : Nat → Nat} {s t : T}
    -- It held before the step.
    (hs : Inv Q s)
    -- One step.
    (h : Step B Q s t) :
    -- Then it holds after the step.
    Inv Q t := by
  -- Look at which step was taken.
  cases h with
  -- A step of the key's lock.
  | lock m hstep keep =>
    -- The lock moved to `m`; build the six facts one by one.
    refine ⟨fun r hr => ?_, fun q r hr => ?_, fun r q hr => ?_, fun q r hr => ?_,
            fun r q hr => ?_, keep⟩
    -- Told: `r` is woken after the step.
    ·
      -- Was it woken before?
      by_cases hold : r ∈ s.lock.woken
      -- Yes, it was woken before.
      ·
        -- It had been told, by a note or a ready wait.
        rcases hs.told r hold with hi | hrd
        -- By a note.
        ·
          -- The note is kept, since `r` is still woken.
          exact Or.inl (by simp [notes, hi, hr])
        -- By a ready wait.
        ·
          -- The ready wait is kept, since `r` is still woken.
          exact Or.inr (by simp [hrd, hr])
      -- No, it was not woken before.
      ·
        -- The step woke it, so it put a note in `r`'s own inbox.
        exact Or.inl (by simp [notes, hr, hold])
    -- Own inbox: a note is in inbox `q` after the step.
    ·
      -- Where did it come from? Spell the new inbox out.
      simp only [notes, List.mem_append, List.mem_filter, Bool.and_eq_true,
        decide_eq_true_eq] at hr
      -- An old note, or a new one.
      rcases hr with ⟨hi, _⟩ | ⟨_, _, hq⟩
      -- An old note.
      ·
        -- It was in its own inbox already.
        exact hs.own_inbox q r hi
      -- A new note.
      ·
        -- It is put in the inbox of `Q r`.
        exact hq
    -- Own ready: a ready wait that is kept was ready before.
    ·
      -- Spell out what a kept ready wait is: an old one that passed the test.
      simp only [List.mem_filter, decide_eq_true_eq] at hr
      -- It was made ready by its own thread then.
      exact hs.own_ready r q hr.1
    -- Fresh inbox: every note left is for a request woken now.
    ·
      -- Spell the new inbox out: old notes that were kept, and new ones.
      simp only [notes, List.mem_append, List.mem_filter, Bool.and_eq_true,
        decide_eq_true_eq] at hr
      -- An old note was kept only if so; a new one is for a woken request.
      rcases hr with ⟨_, hw⟩ | ⟨hw, _, _⟩ <;> exact hw
    -- Fresh ready: only waits of requests woken now were kept.
    ·
      -- Spell out the test a kept wait passed.
      simp only [List.mem_filter, decide_eq_true_eq] at hr
      -- The filter's test says it.
      exact hr.2
  -- A thread read its inbox.
  | poll q =>
    -- Thread `q` read its inbox; the lock did not move.
    refine ⟨fun r hr => ?_, fun x r hr => ?_, fun r x hr => ?_, fun x r hr => ?_,
            fun r x hr => ?_, hs.pending_holds⟩
    -- Told: `r` is woken, and the lock did not move.
    ·
      -- `r` was told before, by a note or a ready wait.
      rcases hs.told r hr with hi | hrd
      -- By a note.
      ·
        -- Is `r`'s inbox the one just read?
        by_cases hq : Q r = q
        -- Yes: the note was read.
        ·
          -- It became a ready wait, made ready by `q = Q r`: the second half of told.
          refine Or.inr ?_
          -- The new ready list is the old one plus the notes read.
          simp only [List.mem_append, List.mem_map]
          -- It is among the notes read, paired with `q`.
          exact Or.inr ⟨r, by rw [← hq]; exact hi, by rw [hq]⟩
        -- No.
        ·
          -- `r`'s inbox was not touched: the note is still in it.
          exact Or.inl (by simp [hq, hi])
      -- By a ready wait.
      ·
        -- A ready wait stays ready.
        exact Or.inr (List.mem_append.2 (Or.inl hrd))
    -- Own inbox: a note still in an inbox was there before.
    ·
      -- Is inbox `x` the one just read?
      by_cases hx : x = q
      -- Yes: the inbox just read.
      ·
        -- It is empty: no note is in it.
        simp [hx] at hr
      -- No: another inbox.
      ·
        -- It is unchanged.
        simp only [hx, ite_false] at hr
        -- So the old fact applies.
        exact hs.own_inbox x r hr
    -- Own ready: an old ready wait, or a note just read.
    ·
      -- Spell the new ready list out: the old one plus the notes read.
      simp only [List.mem_append, List.mem_map, Prod.mk.injEq] at hr
      -- Split the two cases.
      rcases hr with hrd | ⟨y, hy, rfl, rfl⟩
      -- An old ready wait.
      ·
        -- It was made ready by its own thread.
        exact hs.own_ready r x hrd
      -- A note just read from inbox `x`.
      ·
        -- It was in its own inbox: `Q r = x`.
        exact (hs.own_inbox _ _ hy).symm
    -- Fresh inbox: a note still in an inbox was there before.
    ·
      -- Is inbox `x` the one just read?
      by_cases hx : x = q
      -- Yes: the inbox just read.
      ·
        -- It is empty.
        simp [hx] at hr
      -- No: another inbox.
      ·
        -- It is unchanged.
        simp only [hx, ite_false] at hr
        -- So the old fact applies.
        exact hs.fresh_inbox x r hr
    -- Fresh ready: an old ready wait, or a note just read.
    ·
      -- Spell the new ready list out: the old one plus the notes read.
      simp only [List.mem_append, List.mem_map, Prod.mk.injEq] at hr
      -- Split the two cases.
      rcases hr with hrd | ⟨y, hy, rfl, rfl⟩
      -- An old ready wait.
      ·
        -- It is of a woken request.
        exact hs.fresh_ready r x hrd
      -- A note just read.
      ·
        -- It was for a woken request.
        exact hs.fresh_inbox _ _ hy
  -- A commit was written.
  | write r hr =>
    -- Only the pending list grew, by a transaction that holds the lock.
    refine ⟨hs.told, hs.own_inbox, hs.own_ready, hs.fresh_inbox, hs.fresh_ready,
            fun x hx => ?_⟩
    -- `x` is the new committer or an old one.
    rcases List.mem_cons.1 hx with rfl | hx
    -- The new committer.
    ·
      -- It holds the lock: the step required it.
      exact hr
    -- An old one.
    ·
      -- It held the lock before, and the lock did not move.
      exact hs.pending_holds x hx
  -- A commit landed.
  | land r =>
    -- Only the pending list shrank.
    refine ⟨hs.told, hs.own_inbox, hs.own_ready, hs.fresh_inbox, hs.fresh_ready,
            fun x hx => ?_⟩
    -- Whoever is still pending was pending before.
    exact hs.pending_holds x (List.mem_filter.1 hx).1

/-- **Every reachable state satisfies the invariant.** -/
theorem reachable_inv {B : Nat} {Q : Nat → Nat} {s : T}
    -- `s` is reachable from the start.
    (h : Steps B Q init s) :
    -- Then the invariant holds in `s`.
    Inv Q s := by
  -- By induction on the steps taken.
  induction h with
  -- No step: the start satisfies it.
  | refl => exact init_inv Q
  -- One more step keeps it.
  | tail _ hstep ih => exact step_inv ih hstep

/-- The key's lock, seen on its own, only ever takes steps of the lock
proved in `Regolith.Sync`: the table adds inboxes and pending commits
around it and changes nothing inside it. -/
theorem lock_reachable {B : Nat} {Q : Nat → Nat} {s : T}
    -- `s` is reachable from the start.
    (h : Steps B Q init s) :
    -- Then its lock is reachable from the lock's own start.
    Sync.Steps B Sync.init s.lock := by
  -- By induction on the steps taken.
  induction h with
  -- No step: the lock is at its own start.
  | refl => exact .refl _
  -- Some steps, then one more.
  | tail _ hstep ih =>
    -- Look at which step was taken last.
    cases hstep with
    -- A lock step: one more step of the lock.
    | lock m hl _ => exact .tail ih hl
    -- Reading an inbox does not move the lock.
    | poll q => exact ih
    -- Writing a commit does not move the lock.
    | write r _ => exact ih
    -- A landing does not move the lock.
    | land r => exact ih

/-! ## The laws -/

/-- **Rule 1, mutual exclusion.** At most one transaction holds the key,
by its own take or by a handoff. TLA+: `MutualExclusion`. -/
theorem mutual_exclusion {B : Nat} {Q : Nat → Nat}
    -- The bound is at least 1.
    (hB : 0 < B) {s : T}
    -- `s` is reachable from the start.
    (h : Steps B Q init s) :
    -- Then the holders, by a take or by a handoff, are at most one.
    (s.lock.owners ++ s.lock.handed).length ≤ 1 :=
  -- The lock is the one proved in `Regolith.Sync`.
  (Sync.mutual_exclusion hB (lock_reachable h)).1

/-- **Rule 2, no lost wake-up: the front of a free lock was told.** While
the lock is free and somebody waits, the front waiter's note is in its own
inbox or its wait is ready. TLA+: `NoStrandedFront` with `WokenIsTold`. -/
theorem no_stranded_front {B : Nat} {Q : Nat → Nat}
    -- The bound is at least 1.
    (hB : 0 < B) {s : T}
    -- `s` is reachable from the start.
    (h : Steps B Q init s) {x : Nat} {t : List Nat}
    -- `x` is the front of the line.
    (hq : s.lock.queue = x :: t)
    -- The lock is free.
    (hf : s.lock.free = true) :
    -- Then `x` has been told.
    Told Q s x :=
  -- The lock woke its front (`Regolith.Sync`), and the table told it.
  (reachable_inv h).told x (Sync.no_stranded_head hB (lock_reachable h) hq hf)

/-- **Rule 2, no lost wake-up: a handoff is told.** A transaction handed
the lock has its note in its own inbox, or its wait is ready. TLA+:
`WokenIsTold`. -/
theorem handed_is_told {B : Nat} {Q : Nat → Nat}
    -- The bound is at least 1.
    (hB : 0 < B) {s : T}
    -- `s` is reachable from the start.
    (h : Steps B Q init s) {x : Nat}
    -- `x` was handed the lock.
    (hx : x ∈ s.lock.handed) :
    -- Then `x` has been told.
    Told Q s x :=
  -- The lock woke it (`Regolith.Sync`), and the table told it.
  (reachable_inv h).told x (Sync.handed_woken hB (lock_reachable h) hx)

/-- **Rule 3, bounded bypass.** A waiting transaction has lost at most `B`
races. TLA+: `BoundedBypass`. -/
theorem bounded_bypass {B : Nat} {Q : Nat → Nat}
    -- The bound is at least 1.
    (hB : 0 < B) {s : T}
    -- `s` is reachable from the start.
    (h : Steps B Q init s) {x : Nat}
    -- `x` waits.
    (hx : x ∈ s.lock.queue) :
    -- Then it has lost at most `B` races.
    s.lock.bypass x ≤ B :=
  -- The lock is the one proved in `Regolith.Sync`.
  Sync.bounded_bypass hB (lock_reachable h) hx

/-- **Rule 4, delivery on the waiter's own queue: notes.** A note for
transaction `r` is only ever in the inbox of `r`'s own thread. TLA+:
`OwnQueue`. -/
theorem note_on_own_queue {B : Nat} {Q : Nat → Nat} {s : T}
    -- `s` is reachable from the start.
    (h : Steps B Q init s) {q r : Nat}
    -- A note for `r` is in inbox `q`.
    (hr : r ∈ s.inbox q) :
    -- Then `q` is `r`'s own thread.
    q = Q r :=
  -- The invariant says `Q r = q`.
  ((reachable_inv h).own_inbox q r hr).symm

/-- **Rule 4, delivery on the waiter's own queue: readiness.** A wait is
made ready only by its own thread reading its own inbox. TLA+:
`OwnQueue`. -/
theorem ready_by_own_queue {B : Nat} {Q : Nat → Nat} {s : T}
    -- `s` is reachable from the start.
    (h : Steps B Q init s) {q r : Nat}
    -- `r`'s wait was made ready by thread `q`.
    (hr : (r, q) ∈ s.ready) :
    -- Then `q` is `r`'s own thread.
    q = Q r :=
  -- The invariant says so.
  (reachable_inv h).own_ready r q hr

/-- **Rule 5, release at landing keeps isolation.** While transaction
`r`'s commit is written and not yet visible, any transaction that holds
the key is `r` itself: nobody else can read the key before the commit is
in it. TLA+: `IsolationAtLanding`. -/
theorem isolation_at_landing {B : Nat} {Q : Nat → Nat}
    -- The bound is at least 1.
    (hB : 0 < B) {s : T}
    -- `s` is reachable from the start.
    (h : Steps B Q init s) {r u : Nat}
    -- `r`'s commit is pending.
    (hr : r ∈ s.pending)
    -- `u` holds the key, by its own take or by a handoff.
    (hu : u ∈ s.lock.owners ++ s.lock.handed) :
    -- Then `u` is `r`.
    u = r := by
  -- A pending committer holds the lock,
  have hown : r ∈ s.lock.owners ++ s.lock.handed :=
    -- by the invariant: it is among the owners,
    List.mem_append.2 (Or.inl ((reachable_inv h).pending_holds r hr))
  -- and there is at most one holder.
  have hle := mutual_exclusion hB h
  -- There is at least one, `r`.
  have hpos : 0 < (s.lock.owners ++ s.lock.handed).length := List.length_pos_of_mem hown
  -- So the holders are exactly `[r]`,
  have hone := Sync.eq_single_of_mem (by omega) hown
  -- and `u`, a holder, is in that list.
  rw [hone] at hu
  -- The only element of `[r]` is `r`.
  simpa using hu

/-! ## The RED cases -/

/-- The entry steps with the defect: the entry is retired whatever its
count (a plain store where the code has a compare-and-swap). -/
inductive EStepNoCas : Entry → Entry → Prop
  /-- As `EStep.pin`. -/
  | pin (s : Entry) (r : Nat)
      -- The entry is still in the table.
      (h : s.retired = false) :
      -- After: one more use, and `r` is among the users.
      EStepNoCas s { s with uses := s.uses + 1, users := r :: s.users }
  /-- As `EStep.unpin`. -/
  | unpin (s : Entry) (r : Nat)
      -- `r` holds a use.
      (h : r ∈ s.users) :
      -- After: one use fewer, and `r` is no longer among the users.
      EStepNoCas s { s with uses := s.uses - 1, users := s.users.erase r }
  /-- The defect: no look at the count. -/
  | retire (s : Entry) :
      -- After: the entry is marked retired.
      EStepNoCas s { s with retired := true }

/-- Any number of `EStepNoCas` steps. -/
inductive EStepsNoCas : Entry → Entry → Prop
  /-- No step at all. -/
  | refl (s : Entry) : EStepsNoCas s s
  /-- Some steps, then one more. -/
  | tail {s t u : Entry} : EStepsNoCas s t → EStepNoCas t u → EStepsNoCas s u

/-- **`retire_unchecked_strands_a_user`.** Call 1 made the entry and gives
its use back. Call 2 takes a use. The entry is then retired without a look
at the count: it has left the table while call 2 still uses it, and the
next caller will make a second lock for the same key. The law of
`retired_unused` fails. -/
theorem retire_unchecked_strands_a_user :
    -- Some reachable state is retired and still has call 2 as its user.
    ∃ s, EStepsNoCas (Entry.made 1) s ∧ s.retired = true ∧ s.users = [2] := by
  -- The state is whatever these three steps reach:
  refine ⟨_, .tail (.tail (.tail (.refl _)
    -- call 1 gives its use back,
    (.unpin _ 1 (by decide)))
    -- call 2 takes one,
    (.pin _ 2 rfl))
    -- and the entry is retired anyway.
    (.retire _), rfl, by decide⟩

/-- The table steps with the defect: a lock step wakes waiters and
delivers no note. -/
inductive StepNoNote (B : Nat) : T → T → Prop
  /-- The defect: the lock moves, and the inboxes stay as they were. -/
  | lock (s : T) (m : Sync.M)
      -- The lock takes one of its own steps.
      (h : Sync.Step B s.lock m) :
      -- After: only the lock moved; no inbox changed.
      StepNoNote B s { s with lock := m }

/-- Any number of `StepNoNote` steps. -/
inductive StepsNoNote (B : Nat) : T → T → Prop
  /-- No step at all. -/
  | refl (s : T) : StepsNoNote B s s
  /-- Some steps, then one more. -/
  | tail {s t u : T} : StepsNoNote B s t → StepNoNote B t u → StepsNoNote B s u

/-- **`undelivered_note_strands`.** Transaction 1 holds, transaction 2
waits, transaction 1 releases. The lock woke 2, but no note was delivered:
the lock is free, 2 is its front, and 2 has no note in its inbox and no
ready wait. The law of `no_stranded_front` fails. -/
theorem undelivered_note_strands :
    -- Some reachable state has the lock free and 2 at the front, and 2 was
    -- never told.
    ∃ s, StepsNoNote 1 init s ∧ s.lock.free = true ∧ s.lock.queue = [2] ∧
      ¬ Told (fun r => r) s 2 := by
  -- The state is whatever these three steps reach:
  refine ⟨_, .tail (.tail (.tail (.refl _)
    -- transaction 1 takes the lock,
    (.lock _ _ (.fast _ 1 (by decide) rfl rfl)))
    -- transaction 2 joins the line,
    (.lock _ _ (.enqueue _ 2 (by decide) (Or.inl rfl))))
    -- and transaction 1 releases.
    (.lock _ _ (.release _ 1 (by decide))), by decide, by decide, ?_⟩
  -- Neither half of "told" holds: both the inbox and the ready list are
  -- still empty.
  simp [Told, init]

/-- **`unbounded_barging_breaks_bound`.** With a bound of 1 and a lock
that never hands off, a waiter loses 2 races. The law of `bounded_bypass`
fails. (The counterexample is the lock's own, from `Regolith.Sync`.) -/
theorem unbounded_barging_breaks_bound :
    -- Some state the lock reaches without handoffs has 2 waiting with 2 lost
    -- races.
    ∃ s, Sync.StepsNoHand Sync.init s ∧ 2 ∈ s.queue ∧ s.bypass 2 = 2 :=
  -- Proved for the lock in `Regolith.Sync`.
  Sync.unbounded_barging_breaks_bound

/-- The inbox after a lock step with the defect: a new note goes into the
inbox of the thread after the right one. -/
def notesWrong (Q : Nat → Nat) (old new : Sync.M) (inbox : Nat → List Nat) (q : Nat) : List Nat :=
  -- The old notes of inbox `q` whose request is still woken, then the
  -- requests newly woken, each in the inbox one after its own thread's.
  (inbox q).filter (fun r => decide (r ∈ new.woken)) ++
    new.woken.filter (fun r => decide (r ∉ old.woken) && decide (Q r + 1 = q))

/-- The table steps with the defect: notes are delivered to the wrong
inbox. -/
inductive StepWrongQueue (B : Nat) (Q : Nat → Nat) : T → T → Prop
  /-- The defect: as `Step.lock`, with `notesWrong`. -/
  | lock (s : T) (m : Sync.M)
      -- The lock takes one of its own steps.
      (h : Sync.Step B s.lock m) :
      -- After: the lock is `m`, and the new notes went to the wrong inboxes.
      StepWrongQueue B Q s { s with lock := m, inbox := notesWrong Q s.lock m s.inbox }

/-- Any number of `StepWrongQueue` steps. -/
inductive StepsWrongQueue (B : Nat) (Q : Nat → Nat) : T → T → Prop
  /-- No step at all. -/
  | refl (s : T) : StepsWrongQueue B Q s s
  /-- Some steps, then one more. -/
  | tail {s t u : T} : StepsWrongQueue B Q s t → StepWrongQueue B Q t u →
      StepsWrongQueue B Q s u

/-- **`wrong_queue_breaks_own_queue`.** Transaction 1 holds, transaction 2
waits, transaction 1 releases. The note for transaction 2 lands in thread
3's inbox: thread 3 would complete transaction 2's wait. The law of
`note_on_own_queue` fails. -/
theorem wrong_queue_breaks_own_queue :
    -- Some reachable state has the note for transaction 2 in inbox 3.
    ∃ s, StepsWrongQueue 1 (fun r => r) init s ∧ 2 ∈ s.inbox 3 := by
  -- The state is whatever these three steps reach:
  refine ⟨_, .tail (.tail (.tail (.refl _)
    -- transaction 1 takes the lock,
    (.lock _ _ (.fast _ 1 (by decide) rfl rfl)))
    -- transaction 2 joins the line,
    (.lock _ _ (.enqueue _ 2 (by decide) (Or.inl rfl))))
    -- and transaction 1 releases, which wakes transaction 2.
    (.lock _ _ (.release _ 1 (by decide))), ?_⟩
  -- Work the three steps out: the note for 2 is in inbox 3.
  decide

/-- The table steps with the defect: a lock step may take the lock from a
transaction whose commit is still pending (the lock is released when the
commit is written). -/
inductive StepNoKeep (B : Nat) : T → T → Prop
  /-- The defect: as `Step.lock`, without the condition on pending
  commits. -/
  | lock (s : T) (m : Sync.M)
      -- The lock takes one of its own steps.
      (h : Sync.Step B s.lock m) :
      -- After: only the lock moved, whoever was pending.
      StepNoKeep B s { s with lock := m }
  /-- As `Step.write`. -/
  | write (s : T) (r : Nat)
      -- `r` holds the lock.
      (hr : r ∈ s.lock.owners) :
      -- After: `r` is among the pending commits.
      StepNoKeep B s { s with pending := r :: s.pending }

/-- Any number of `StepNoKeep` steps. -/
inductive StepsNoKeep (B : Nat) : T → T → Prop
  /-- No step at all. -/
  | refl (s : T) : StepsNoKeep B s s
  /-- Some steps, then one more. -/
  | tail {s t u : T} : StepsNoKeep B s t → StepNoKeep B t u → StepsNoKeep B s u

/-- **`release_at_write_breaks_isolation`.** Transaction 1 takes the key
and writes its commit, which is not visible yet. Its lock is released at
once, and transaction 2 takes the key: it would read the key as it was
before transaction 1's commit. The law of `isolation_at_landing` fails. -/
theorem release_at_write_breaks_isolation :
    -- Some reachable state has 1's commit pending while 2 holds the key.
    ∃ s, StepsNoKeep 1 init s ∧ 1 ∈ s.pending ∧ 2 ∈ s.lock.owners := by
  -- The state is whatever these four steps reach:
  refine ⟨_, .tail (.tail (.tail (.tail (.refl _)
    -- transaction 1 takes the lock,
    (.lock _ _ (.fast _ 1 (by decide) rfl rfl)))
    -- writes its commit,
    (.write _ 1 (by decide)))
    -- releases while the commit is still pending,
    (.lock _ _ (.release _ 1 (by decide))))
    -- and transaction 2 takes the free lock.
    (.lock _ _ (.fast _ 2 (by decide) rfl rfl)), by decide, by decide⟩

-- End of the namespace opened at the top.
end Regolith.LockTable
