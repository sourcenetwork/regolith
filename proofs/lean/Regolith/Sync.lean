/-!
# Sync: the barging lock with bounded bypass (regolith::sync, D49)

This file backs the TLA+ model `proofs/tla/Sync.tla`, invariants
`MutualExclusion`, `BoundedBypass`, `HandoffExclusive` and `NoLostWakeup`
(configurations `MC_Sync_*`), and the exclusive side of
`proofs/tla/SyncRwLock.tla`. TLC checks the concurrent protocol there, step
by atomic step, for three tasks. Here the Mutex is a sequential state
machine over the abstract steps (barging fast path, enqueue, release, three
kinds of poll, two kinds of cancel); a reachable state is the result of any
sequence of them, so every interleaving of those steps is covered. The
theorems hold for every number of requests, every number of steps and
every bound `B` (D49's BOUND).

The protocol (D49). The fast path takes a free lock whenever no handoff is
owed, even while waiters queue: barging. A release with waiters frees the
lock and wakes the head, which competes when polled, unless the head has
lost `B` races: then the lock passes straight to the head, stays held, and
the owed bit shuts barging until the head takes it. A woken head that loses
keeps its place and counts the loss. A cancelled waiter passes on a handoff
it was owed (to the next waiter, or frees the lock), and a wake it was given
(to the next head).

What is proved, in plain words:

1. `step_inv` and `reachable_inv`: the invariant holds in every reachable
   state.
2. `mutual_exclusion`: at most one request holds the lock, and none while
   it is free. TLA+: `MutualExclusion`.
3. `bounded_bypass`, `lose_below_bound`, `bypass_counts_losses`: a queued
   request's bypass count never exceeds `B`; a loss happens only below `B`;
   and only a loss changes a queued request's count, by one. So a request
   loses at most `B` races. `release_hands_off_at_bound`: once it has lost
   `B`, the next release hands it the lock. TLA+: `BoundedBypass`.
4. `owed_exclusive` and `owed_blocks_barging`: while a handoff is owed to
   `w`, `w` holds the lock and nobody else does, and no step makes anyone
   but `w` an owner. TLA+: `HandoffExclusive`.
5. `no_stranded_head` and `handed_woken`: while the lock is free, the head
   waiter has been woken; a request handed the lock has been woken.
   TLA+: `NoLostWakeup`.
6. The RED cases, as counterexamples: `unbounded_barging_breaks_bound` (a
   release that never hands off lets a waiter lose more than `B` races) and
   `release_without_wake_strands` (a release that wakes nobody leaves the
   head asleep beside a free lock).

How to read the Lean: `def` defines a function or a property, `theorem`
states a fact and its proof follows `:= by`. Lines starting with `--` are
comments. `l.erase x` is `l` without its first `x`; `o.toList` is `[w]`
for `some w` and `[]` for `none`.
-/

namespace Regolith.Sync

/-! ## The state -/

/-- The lock's state. A request is named by a natural number, fresh for
every acquire. -/
structure M where
  /-- The lock is free. -/
  free : Bool
  /-- The handoff-owed bit, naming the request the lock was handed to. -/
  owed : Option Nat
  /-- The waiting requests, oldest first. A woken head keeps its place. -/
  queue : List Nat
  /-- Requests that hold the lock and know it. -/
  owners : List Nat
  /-- Requests the lock was handed to, not yet polled: they hold it. -/
  handed : List Nat
  /-- Requests whose woken bit is set: woken, not yet polled. -/
  woken : List Nat
  /-- Each request's bypass count: races it lost. -/
  bypass : Nat → Nat
  /-- Ghost: every request that ever entered (fast path or queue). -/
  enq : List Nat

/-- The start: the lock free, nobody waiting, holding or woken. -/
def init : M := ⟨true, none, [], [], [], [], fun _ => 0, []⟩

/-- `f` with `f r` replaced by `v`. -/
def upd (f : Nat → Nat) (r v : Nat) : Nat → Nat := fun x => if x = r then v else f x

/-- Wake the head waiter, unless its woken bit is set already. -/
def wakeHead (s : M) : M :=
  match s.queue with
  -- Nobody waits: nobody to wake.
  | [] => s
  -- The head `h` is woken if it is not already.
  | h :: _ => if h ∈ s.woken then s else { s with woken := s.woken ++ [h] }

/-- A release, after the owner's guard is gone: free the lock and wake
the head, or, if the head has lost `B` races, hand it the lock (it stays
held), set the owed bit and wake it. -/
def relFrom (B : Nat) (s : M) : M :=
  match s.queue with
  -- Nobody waits: one RMW frees the lock.
  | [] => { s with free := true }
  | h :: t =>
    if s.bypass h < B
      -- Below the bound: free, and the head competes when polled.
      then wakeHead { s with free := true }
      -- At the bound: hand off; the head is popped, holds, and is woken.
      else { s with owed := some h, handed := s.handed ++ [h], queue := t,
                    woken := s.woken ++ [h] }

/-- A handoff passes on (its waiter was cancelled): to the next waiter,
whatever its count, or the lock is freed if nobody waits. -/
def passOn (s : M) : M :=
  match s.queue with
  -- Nobody waits: free the lock.
  | [] => { s with free := true }
  -- The next waiter is handed the lock, and woken.
  | h :: t => { s with owed := some h, handed := s.handed ++ [h], queue := t,
                       woken := s.woken ++ [h] }

/-- After a waiting request leaves: if the lock is free and no handoff is
owed, the new head is woken (a wake the leaver had is passed on). -/
def wakeIfFree (s : M) : M :=
  if s.free = true ∧ s.owed = none then wakeHead s else s

/-! ## The steps -/

/-- The design's steps, for bound `B`. -/
inductive Step (B : Nat) : M → M → Prop
  /-- The fast path (try_lock, or lock uncontended): a fresh request `r`
  takes the free lock if no handoff is owed, whoever waits. -/
  | fast (s : M) (r : Nat)
      -- `r` is a fresh request.
      (hr : r ∉ s.enq)
      -- The lock is free.
      (hf : s.free = true)
      -- No handoff is owed.
      (ho : s.owed = none) :
      Step B s { s with free := false, owners := r :: s.owners, enq := s.enq ++ [r] }
  /-- A contended lock: the fast path failed, so the fresh request `r`
  registers at the tail with a count of 0. (Its re-check after registering
  is the fast path again, which failed for the same reason.) -/
  | enqueue (s : M) (r : Nat)
      -- `r` is a fresh request.
      (hr : r ∉ s.enq)
      -- The fast path is shut: the lock is held, or a handoff is owed.
      (hc : s.free = false ∨ s.owed ≠ none) :
      Step B s { s with queue := s.queue ++ [r], enq := s.enq ++ [r], bypass := upd s.bypass r 0 }
  /-- An owner drops its guard. -/
  | release (s : M) (r : Nat)
      -- `r` holds the lock.
      (hr : r ∈ s.owners) :
      Step B s (relFrom B { s with owners := s.owners.erase r })
  /-- A woken request that was handed the lock takes it; the owed bit
  clears. -/
  | pollHanded (s : M) (h : Nat)
      -- `h` was woken ...
      (hw : h ∈ s.woken)
      -- ... and handed the lock.
      (hh : h ∈ s.handed) :
      Step B s { s with owners := h :: s.owners, handed := s.handed.erase h,
                        woken := s.woken.erase h, owed := none }
  /-- A woken request wins the race: the lock is free and no handoff owed. -/
  | pollWin (s : M) (h : Nat)
      -- `h` was woken ...
      (hw : h ∈ s.woken)
      -- ... and not handed the lock.
      (hh : h ∉ s.handed)
      -- The lock is free.
      (hf : s.free = true)
      -- No handoff is owed.
      (ho : s.owed = none) :
      Step B s { s with free := false, owners := h :: s.owners, queue := s.queue.erase h,
                        woken := s.woken.erase h }
  /-- A woken request loses the race (someone barged in): it keeps its
  place, its count goes up by one, and its woken bit clears. -/
  | pollLose (s : M) (h : Nat)
      -- `h` was woken ...
      (hw : h ∈ s.woken)
      -- ... and not handed the lock.
      (hh : h ∉ s.handed)
      -- The fast path is shut for it.
      (hc : s.free = false ∨ s.owed ≠ none) :
      Step B s { s with bypass := upd s.bypass h (s.bypass h + 1), woken := s.woken.erase h }
  /-- A waiting request's future is dropped: it leaves, and a wake it had
  passes to the new head. -/
  | cancelWaiting (s : M) (r : Nat)
      -- `r` waits.
      (hr : r ∈ s.queue) :
      Step B s (wakeIfFree { s with queue := s.queue.erase r, woken := s.woken.erase r })
  /-- A request handed the lock is dropped before it was polled: the
  handoff passes on. -/
  | cancelHanded (s : M) (r : Nat)
      -- `r` was handed the lock.
      (hr : r ∈ s.handed) :
      Step B s (passOn { s with handed := s.handed.erase r, woken := s.woken.erase r,
                                owed := none })

/-- Any number of steps, one after another. -/
inductive Steps (B : Nat) : M → M → Prop
  /-- No step at all. -/
  | refl (s : M) : Steps B s s
  /-- Some steps, then one more. -/
  | tail {s t u : M} : Steps B s t → Step B t u → Steps B s u

/-! ## The invariant -/

/-- The protocol's invariant, for bound `B`. -/
structure Inv (B : Nat) (s : M) : Prop where
  /-- The lock is free, or held by exactly one request. -/
  excl : (s.owners ++ s.handed).length + (if s.free = true then 1 else 0) = 1
  /-- A handoff is pending exactly when owed, to the request owed. -/
  handed_owed : s.handed = s.owed.toList
  /-- A woken request holds the lock by handoff, or is the head with a
  count below the bound. -/
  woken_ok : ∀ x ∈ s.woken, x ∈ s.handed ∨ ∃ t, s.queue = x :: t ∧ s.bypass x < B
  /-- A request handed the lock has been woken. -/
  handed_woken : ∀ x ∈ s.handed, x ∈ s.woken
  /-- Every waiting request's count is within the bound. -/
  bypass_le : ∀ x ∈ s.queue, s.bypass x ≤ B
  /-- Only the head has ever lost: the others have a count of 0. -/
  tail_zero : ∀ h t, s.queue = h :: t → ∀ x ∈ t, s.bypass x = 0
  /-- While the lock is free, the head has been woken. -/
  stranded : ∀ h t, s.queue = h :: t → s.free = true → h ∈ s.woken
  /-- While a handoff is owed, only its request is woken. -/
  owed_woken : s.owed ≠ none → ∀ x ∈ s.woken, x ∈ s.handed
  /-- Requests entered once each. -/
  enq_nodup : s.enq.Nodup
  /-- Every request in the lock's lists entered. -/
  all_enq : ∀ x, x ∈ s.queue ∨ x ∈ s.owners ∨ x ∈ s.handed ∨ x ∈ s.woken → x ∈ s.enq
  /-- No request waits twice. -/
  queue_nodup : s.queue.Nodup
  /-- A waiting request holds nothing. -/
  queue_fresh : ∀ x ∈ s.queue, x ∉ s.owners ∧ x ∉ s.handed
  /-- No request is woken twice. -/
  woken_nodup : s.woken.Nodup

/-! ## Helper facts -/

/-- A list of length one that holds `x` is `[x]`. -/
theorem eq_single_of_mem {l : List Nat} {x : Nat}
    -- `l` has one element ...
    (hl : l.length = 1)
    -- ... and `x` is in it.
    (hx : x ∈ l) :
    l = [x] := by
  -- One element: `l = [a]`, and `x ∈ [a]` means `x = a`.
  match l, hl with
  | [a], _ => simp only [List.mem_singleton] at hx; rw [hx]

/-- Under the invariant, if `r` owns the lock, it is held by `r` alone. -/
theorem Inv.owner_alone {B : Nat} {s : M}
    -- The invariant holds.
    (hs : Inv B s) {r : Nat}
    -- `r` owns the lock.
    (hr : r ∈ s.owners) :
    s.owners = [r] ∧ s.handed = [] ∧ s.free = false ∧ s.owed = none := by
  have hx := hs.excl
  -- `r` is among the holders, so the holders are not empty.
  have hpos : 0 < (s.owners ++ s.handed).length :=
    List.length_pos_of_mem (List.mem_append.2 (Or.inl hr))
  -- So the lock is not free, and there is exactly one holder.
  have hfree : s.free = false := by
    cases hf : s.free
    · rfl
    · rw [hf] at hx; simp only [ite_true] at hx; omega
  rw [hfree] at hx
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at hx
  have h1 := eq_single_of_mem hx (List.mem_append.2 (Or.inl hr))
  -- The single holder is `r`, an owner; nobody is handed the lock.
  have ho : s.owners = [r] := by
    cases ho : s.owners with
    | nil => rw [ho] at hr; simp at hr
    | cons a l =>
      rw [ho] at h1
      simp only [List.cons_append, List.cons.injEq, List.append_eq_nil_iff] at h1
      obtain ⟨rfl, rfl, -⟩ := h1
      rfl
  have hh : s.handed = [] := by
    rw [ho] at h1; simpa using h1
  -- No handoff pending, so none owed.
  have hn : s.owed = none := by
    have := hs.handed_owed
    rw [hh] at this
    cases ho' : s.owed with
    | none => rfl
    | some w => rw [ho'] at this; simp at this
  exact ⟨ho, hh, hfree, hn⟩

/-- Under the invariant, a handoff owed to `w` means `w` alone holds the
lock, by handoff, and the lock is not free. -/
theorem Inv.owed_alone {B : Nat} {s : M}
    -- The invariant holds.
    (hs : Inv B s) {w : Nat}
    -- A handoff is owed to `w`.
    (hw : s.owed = some w) :
    s.handed = [w] ∧ s.owners = [] ∧ s.free = false := by
  have hh : s.handed = [w] := by rw [hs.handed_owed, hw]; rfl
  have hx := hs.excl
  rw [hh] at hx
  -- One holder already: no owner, and the lock is not free.
  have : s.owners = [] ∧ s.free = false := by
    cases ho : s.owners with
    | nil =>
      cases hf : s.free
      · exact ⟨rfl, rfl⟩
      · rw [ho, hf] at hx; simp at hx
    | cons a l => rw [ho] at hx; simp at hx; omega
  exact ⟨hh, this⟩

/-- Under the invariant, while the lock is free nobody holds it. -/
theorem Inv.free_empty {B : Nat} {s : M}
    -- The invariant holds.
    (hs : Inv B s)
    -- The lock is free.
    (hf : s.free = true) :
    s.owners = [] ∧ s.handed = [] ∧ s.owed = none := by
  have hx := hs.excl
  rw [hf] at hx
  simp only [ite_true] at hx
  have hl : (s.owners ++ s.handed).length = 0 := by omega
  rw [List.length_eq_zero_iff, List.append_eq_nil_iff] at hl
  obtain ⟨ho, hh⟩ := hl
  refine ⟨ho, hh, ?_⟩
  -- No handoff pending, so none owed.
  have := hs.handed_owed
  rw [hh] at this
  cases ho' : s.owed with
  | none => rfl
  | some w => rw [ho'] at this; simp at this

/-- Under the invariant, a woken request not handed the lock is the head,
with a count below the bound. -/
theorem Inv.woken_head {B : Nat} {s : M}
    -- The invariant holds.
    (hs : Inv B s) {h : Nat}
    -- `h` was woken ...
    (hw : h ∈ s.woken)
    -- ... and not handed the lock.
    (hh : h ∉ s.handed) :
    ∃ t, s.queue = h :: t ∧ s.bypass h < B := by
  rcases hs.woken_ok h hw with hx | hx
  · exact absurd hx hh
  · exact hx

/-! ## What the helpers change -/

/-- Waking the head changes only the woken list: here is every other
field, unchanged. -/
theorem wakeHead_fields (u : M) :
    (wakeHead u).free = u.free ∧ (wakeHead u).owed = u.owed ∧ (wakeHead u).queue = u.queue ∧
    (wakeHead u).owners = u.owners ∧ (wakeHead u).handed = u.handed ∧
    (wakeHead u).bypass = u.bypass ∧ (wakeHead u).enq = u.enq := by
  -- Each branch keeps the fields, or replaces only `woken`.
  unfold wakeHead
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Waking the head when the queue is `h :: t`: `h` joins the woken list
unless it is in it already. -/
theorem wakeHead_woken {u : M} {h : Nat} {t : List Nat}
    -- The head is `h`.
    (hq : u.queue = h :: t) :
    (wakeHead u).woken = if h ∈ u.woken then u.woken else u.woken ++ [h] := by
  -- The match takes the `h :: t` branch.
  simp only [wakeHead, hq]
  split <;> rfl

/-- Waking the head of an empty queue changes nothing. -/
theorem wakeHead_nil {u : M}
    -- Nobody waits.
    (hq : u.queue = []) :
    wakeHead u = u := by
  unfold wakeHead
  rw [hq]

/-- With the lock free and nothing owed, `wakeIfFree` wakes the head. -/
theorem wakeIfFree_free {u : M}
    -- The lock is free ...
    (hf : u.free = true)
    -- ... and nothing is owed.
    (ho : u.owed = none) :
    wakeIfFree u = wakeHead u := by
  unfold wakeIfFree
  simp [hf, ho]

/-- With the lock held, `wakeIfFree` changes nothing. -/
theorem wakeIfFree_held {u : M}
    -- The lock is held.
    (hf : u.free = false) :
    wakeIfFree u = u := by
  unfold wakeIfFree
  simp [hf]

/-! ## Two shapes the invariant takes -/

/-- **A free lock.** Nobody holds it, no handoff is owed, and exactly the
head (if any) is woken, with a count below the bound; everyone behind it
has a count of 0. Such a state satisfies the invariant. -/
theorem inv_free {B : Nat} {u : M}
    -- The lock is free, unowed, unheld.
    (hf : u.free = true) (ho : u.owed = none) (hown : u.owners = []) (hh : u.handed = [])
    -- Exactly the head is woken.
    (hw : u.woken = u.queue.take 1)
    -- The head is below the bound.
    (hhead : ∀ h t, u.queue = h :: t → u.bypass h < B)
    -- Those behind it have not lost.
    (htail : ∀ h t, u.queue = h :: t → ∀ x ∈ t, u.bypass x = 0)
    -- Requests entered once, and every waiter entered.
    (hen : u.enq.Nodup) (hall : ∀ x ∈ u.queue, x ∈ u.enq)
    -- No request waits twice.
    (hqn : u.queue.Nodup) :
    Inv B u := by
  -- The woken requests are the head, which is in the queue.
  have hwq : ∀ x ∈ u.woken, ∃ t, u.queue = x :: t := by
    intro x hx
    rw [hw] at hx
    cases hq : u.queue with
    | nil => rw [hq] at hx; simp at hx
    | cons h t => rw [hq] at hx; simp at hx; exact ⟨t, by rw [hx]⟩
  refine ⟨by simp [hf, hown, hh], by simp [hh, ho], ?_, by simp [hh], ?_, htail, ?_,
    by simp [ho], hen, ?_, hqn, by simp [hown, hh], ?_⟩
  · -- A woken request is the head, below the bound.
    intro x hx
    obtain ⟨t, ht⟩ := hwq x hx
    exact Or.inr ⟨t, ht, hhead x t ht⟩
  · -- The head is below the bound; the others are at 0.
    intro x hx
    cases hq : u.queue with
    | nil => rw [hq] at hx; simp at hx
    | cons h t =>
      rw [hq] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Nat.le_of_lt (hhead x t hq)
      · rw [htail h t hq x hx]; exact Nat.zero_le _
  · -- The head is the woken one.
    intro h t hq _
    rw [hw, hq]
    simp
  · -- Every request named entered: owners and handed are empty, the woken
    -- one waits.
    intro x hx
    rcases hx with hx | hx | hx | hx
    · exact hall x hx
    · rw [hown] at hx; simp at hx
    · rw [hh] at hx; simp at hx
    · obtain ⟨t, ht⟩ := hwq x hx
      exact hall x (by rw [ht]; exact List.mem_cons_self)
  · -- At most one woken request.
    rw [hw]
    cases u.queue with
    | nil => simp
    | cons h t => simp

/-- **A lock just handed off.** Request `h` was handed the lock, owed and
woken; nobody else holds it or is woken; the waiters left have counts of
0. Such a state satisfies the invariant. -/
theorem inv_handoff {B : Nat} {u : M} {h : Nat}
    -- The lock is held, by handoff to `h`, which is owed and woken.
    (hf : u.free = false) (ho : u.owed = some h) (hown : u.owners = []) (hh : u.handed = [h])
    (hw : u.woken = [h])
    -- The waiters left have not lost.
    (hz : ∀ x ∈ u.queue, u.bypass x = 0)
    -- `h` no longer waits.
    (hhq : h ∉ u.queue)
    -- Requests entered once; every waiter, and `h`, entered.
    (hen : u.enq.Nodup) (hall : ∀ x ∈ u.queue, x ∈ u.enq) (hhe : h ∈ u.enq)
    -- No request waits twice.
    (hqn : u.queue.Nodup) :
    Inv B u := by
  refine ⟨by simp [hf, hown, hh], by simp [hh, ho], ?_, ?_, ?_, ?_, ?_, ?_, hen, ?_, hqn, ?_, ?_⟩
  · -- The woken one holds by handoff.
    intro x hx; rw [hw] at hx; left; rw [hh]; exact hx
  · -- The handed one is woken.
    intro x hx; rw [hh] at hx; rw [hw]; exact hx
  · -- Waiters are at 0.
    intro x hx; rw [hz x hx]; exact Nat.zero_le _
  · -- Waiters are at 0.
    intro h' t hq x hx; exact hz x (by rw [hq]; exact List.mem_cons_of_mem _ hx)
  · -- The lock is held.
    intro h' t _ hfr; rw [hf] at hfr; simp at hfr
  · -- Only the handed one is woken.
    intro _ x hx; rw [hw] at hx; rw [hh]; exact hx
  · -- Every request named entered.
    intro x hx
    rcases hx with hx | hx | hx | hx
    · exact hall x hx
    · rw [hown] at hx; simp at hx
    · rw [hh] at hx; simp at hx; rw [hx]; exact hhe
    · rw [hw] at hx; simp at hx; rw [hx]; exact hhe
  · -- A waiter is neither an owner nor `h`.
    intro x hx
    refine ⟨by simp [hown], ?_⟩
    rw [hh]; simp only [List.mem_singleton]
    intro e; subst e; exact hhq hx
  · -- One woken request.
    rw [hw]; simp

/-- Under the invariant, while the lock is free exactly the head (if any)
is woken. -/
theorem Inv.free_woken {B : Nat} {s : M}
    -- The invariant holds.
    (hs : Inv B s)
    -- The lock is free.
    (hf : s.free = true) :
    s.woken = s.queue.take 1 := by
  obtain ⟨-, hh, -⟩ := hs.free_empty hf
  -- Every woken request is the head.
  have hsub : ∀ x ∈ s.woken, ∃ t, s.queue = x :: t := by
    intro x hx
    rcases hs.woken_ok x hx with h' | ⟨t, ht, -⟩
    · rw [hh] at h'; simp at h'
    · exact ⟨t, ht⟩
  cases hq : s.queue with
  | nil =>
    -- No head: nobody woken.
    cases hw : s.woken with
    | nil => rfl
    | cons x l =>
      obtain ⟨t, ht⟩ := hsub x (by rw [hw]; exact List.mem_cons_self)
      rw [hq] at ht; simp at ht
  | cons h t =>
    -- The head is woken (no stranding), and nobody else.
    have hhw := hs.stranded h t hq hf
    have hn := hs.woken_nodup
    simp only [List.take_succ_cons, List.take_zero]
    have hall : ∀ x ∈ s.woken, x = h := by
      intro x hx
      obtain ⟨t', ht'⟩ := hsub x hx
      rw [hq] at ht'
      simp only [List.cons.injEq] at ht'
      exact ht'.1.symm
    cases hw : s.woken with
    | nil => rw [hw] at hhw; simp at hhw
    | cons a l =>
      have ha := hall a (by rw [hw]; exact List.mem_cons_self)
      subst ha
      rw [hw, List.nodup_cons] at hn
      cases l with
      | nil => rfl
      | cons b l' =>
        have hb := hall b (by rw [hw]; simp)
        subst hb
        exact absurd List.mem_cons_self hn.1

/-! ## Every step keeps the invariant -/

/-- The start satisfies the invariant. -/
theorem init_inv (B : Nat) : Inv B init :=
  -- The lock is free and nobody waits: the free shape.
  inv_free rfl rfl rfl rfl rfl (by simp [init]) (by simp [init]) List.nodup_nil
    (by simp [init]) List.nodup_nil

/-- **Every step keeps the invariant**, for a bound of at least 1. -/
theorem step_inv {B : Nat}
    -- The bound is at least 1.
    (hB : 0 < B) {s t : M}
    -- The invariant holds before the step.
    (hs : Inv B s)
    -- One step of the design.
    (hstep : Step B s t) :
    Inv B t := by
  cases hstep with
  | fast r hr hf ho =>
    -- The lock was free, so nobody held it; `r` takes it.
    obtain ⟨hown, hhand, -⟩ := hs.free_empty hf
    -- `r` is fresh, so in none of the lock's lists.
    have hfresh : ∀ x, x ∈ s.queue ∨ x ∈ s.owners ∨ x ∈ s.handed ∨ x ∈ s.woken → x ≠ r :=
      fun x hx e => hr (e ▸ hs.all_enq x hx)
    refine ⟨?_, hs.handed_owed, hs.woken_ok, hs.handed_woken, hs.bypass_le, hs.tail_zero,
      ?_, hs.owed_woken, ?_, ?_, hs.queue_nodup, ?_, hs.woken_nodup⟩
    · -- One holder, `r`; the lock is no longer free.
      simp [hown, hhand]
    · -- The lock is not free.
      intro h t _ hfr; simp at hfr
    · -- `r` is new to the entry list.
      rw [List.nodup_append]
      refine ⟨hs.enq_nodup, by simp, ?_⟩
      intro a ha b hb hab
      simp only [List.mem_singleton] at hb
      subst hb; subst hab
      exact hr ha
    · -- `r` entered now; everyone else as before.
      intro x hx
      rw [List.mem_append, List.mem_singleton]
      simp only [List.mem_cons] at hx
      rcases hx with hx | (rfl | hx) | hx | hx
      · exact Or.inl (hs.all_enq x (Or.inl hx))
      · exact Or.inr rfl
      · exact Or.inl (hs.all_enq x (Or.inr (Or.inl hx)))
      · exact Or.inl (hs.all_enq x (Or.inr (Or.inr (Or.inl hx))))
      · exact Or.inl (hs.all_enq x (Or.inr (Or.inr (Or.inr hx))))
    · -- A waiter is not `r`, and held nothing.
      intro x hx
      refine ⟨?_, (hs.queue_fresh x hx).2⟩
      simp only [List.mem_cons, not_or]
      exact ⟨hfresh x (Or.inl hx), (hs.queue_fresh x hx).1⟩
  | enqueue r hr hc =>
    -- The lock is held: a handoff owed means someone holds it.
    have hfree : s.free = false := by
      rcases hc with h | h
      · exact h
      · cases hf : s.free
        · rfl
        · exfalso; exact h (hs.free_empty hf).2.2
    -- `r` is fresh, so in none of the lock's lists.
    have hfresh : ∀ x, x ∈ s.queue ∨ x ∈ s.owners ∨ x ∈ s.handed ∨ x ∈ s.woken → x ≠ r :=
      fun x hx e => hr (e ▸ hs.all_enq x hx)
    -- `upd` leaves every request but `r` alone.
    have hupd : ∀ x, x ≠ r → upd s.bypass r 0 x = s.bypass x := by
      intro x hx; simp [upd, hx]
    refine ⟨hs.excl, hs.handed_owed, ?_, hs.handed_woken, ?_, ?_, ?_, hs.owed_woken, ?_, ?_, ?_,
      ?_, hs.woken_nodup⟩
    · -- A woken waiter was the head of a non-empty queue; it still is.
      intro x hx
      rcases hs.woken_ok x hx with h | ⟨t, hq, hb⟩
      · exact Or.inl h
      · refine Or.inr ⟨t ++ [r], by simp [hq], ?_⟩
        dsimp only; rw [hupd x (hfresh x (Or.inr (Or.inr (Or.inr hx))))]
        exact hb
    · -- `r` has count 0; the others as before.
      intro x hx
      rw [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · dsimp only; rw [hupd x (hfresh x (Or.inl hx))]; exact hs.bypass_le x hx
      · simp [upd]
    · -- Behind the head: the old tail and `r`, all at 0.
      intro h t hq x hx
      cases hq0 : s.queue with
      | nil =>
        -- `r` alone: no tail.
        rw [hq0] at hq; simp at hq; obtain ⟨-, rfl⟩ := hq; simp at hx
      | cons h' t' =>
        rw [hq0] at hq
        simp only [List.cons_append, List.cons.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        rw [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · dsimp only; rw [hupd x (hfresh x (Or.inl (by rw [hq0]; exact List.mem_cons_of_mem _ hx)))]
          exact hs.tail_zero _ t' hq0 x hx
        · simp [upd]
    · -- The lock is held.
      intro h t _ hf; rw [hfree] at hf; simp at hf
    · -- `r` is new to the entry list.
      rw [List.nodup_append]
      refine ⟨hs.enq_nodup, by simp, ?_⟩
      intro a ha b hb hab
      simp only [List.mem_singleton] at hb
      subst hb; subst hab
      exact hr ha
    · -- `r` entered now; everyone else as before.
      intro x hx
      rw [List.mem_append, List.mem_singleton]
      rw [List.mem_append, List.mem_singleton] at hx
      rcases hx with (hx | rfl) | hx | hx | hx
      · exact Or.inl (hs.all_enq x (Or.inl hx))
      · exact Or.inr rfl
      · exact Or.inl (hs.all_enq x (Or.inr (Or.inl hx)))
      · exact Or.inl (hs.all_enq x (Or.inr (Or.inr (Or.inl hx))))
      · exact Or.inl (hs.all_enq x (Or.inr (Or.inr (Or.inr hx))))
    · -- `r` is new to the queue.
      rw [List.nodup_append]
      refine ⟨hs.queue_nodup, by simp, ?_⟩
      intro a ha b hb hab
      simp only [List.mem_singleton] at hb
      subst hb; subst hab
      exact hfresh a (Or.inl ha) rfl
    · -- `r` holds nothing; the others as before.
      intro x hx
      rw [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hs.queue_fresh x hx
      · exact ⟨fun h => hfresh x (Or.inr (Or.inl h)) rfl,
          fun h => hfresh x (Or.inr (Or.inr (Or.inl h))) rfl⟩
  | release r hr =>
    -- `r` held the lock alone.
    obtain ⟨hown, hhand, hfree, howed⟩ := hs.owner_alone hr
    -- Nobody is woken unless it is the head with a count below the bound.
    have hwk : ∀ x ∈ s.woken, ∃ t, s.queue = x :: t ∧ s.bypass x < B := by
      intro x hx
      rcases hs.woken_ok x hx with h | h
      · rw [hhand] at h; simp at h
      · exact h
    have hqn := hs.queue_nodup
    have hallq : ∀ x ∈ s.queue, x ∈ s.enq := fun x hx => hs.all_enq x (Or.inl hx)
    unfold relFrom
    simp only [hown, List.erase_cons_head]
    cases hq : s.queue with
    | nil =>
      -- Nobody waits: the lock is free, and nobody is woken.
      have hwe : s.woken = [] := by
        cases hw : s.woken with
        | nil => rfl
        | cons x l =>
          obtain ⟨t, ht, -⟩ := hwk x (by rw [hw]; exact List.mem_cons_self)
          rw [hq] at ht; simp at ht
      exact inv_free rfl howed rfl hhand (by simp [hwe]) (by simp) (by simp) hs.enq_nodup
        (by simp) (by simp)
    | cons h t =>
      rw [hq] at hqn hallq
      by_cases hb : s.bypass h < B
      · -- Below the bound: free, and wake the head. Either way exactly the
        -- head ends up woken: a woken request before was the head.
        simp only [hb, ite_true]
        have hsub : ∀ x ∈ s.woken, x = h := by
          intro x hx
          obtain ⟨t', ht', -⟩ := hwk x hx
          rw [hq] at ht'; simp only [List.cons.injEq] at ht'; exact ht'.1.symm
        -- The head is below the bound; those behind it at 0; all entered.
        have hhead : ∀ h' t', h :: t = h' :: t' → s.bypass h' < B := by
          intro h' t' e; simp only [List.cons.injEq] at e; obtain ⟨e1, -⟩ := e; rw [← e1]; exact hb
        have htail : ∀ h' t', h :: t = h' :: t' → ∀ x ∈ t', s.bypass x = 0 := by
          intro h' t' e x hx; simp only [List.cons.injEq] at e; obtain ⟨-, e2⟩ := e
          rw [← e2] at hx; exact hs.tail_zero h t hq x hx
        unfold wakeHead
        simp only
        by_cases hhw : h ∈ s.woken
        · -- Already woken: `s.woken` is exactly `[h]`.
          simp only [hhw, ite_true]
          have hw1 : s.woken = [h] := by
            cases hw : s.woken with
            | nil => rw [hw] at hhw; simp at hhw
            | cons a l =>
              have ha := hsub a (by rw [hw]; exact List.mem_cons_self)
              rw [ha] at hw
              have hnd := hs.woken_nodup
              rw [hw, List.nodup_cons] at hnd
              cases l with
              | nil => rw [ha]
              | cons b l' =>
                have hb' := hsub b (by rw [hw]; simp)
                rw [hb'] at hnd
                exact absurd List.mem_cons_self hnd.1
          exact inv_free rfl howed rfl hhand (by simp [hw1]) hhead htail hs.enq_nodup hallq hqn
        · -- Not woken: `s.woken` is empty, and `h` is woken now.
          simp only [hhw, ite_false]
          have hw0 : s.woken = [] := by
            cases hw : s.woken with
            | nil => rfl
            | cons a l =>
              have ha := hsub a (by rw [hw]; exact List.mem_cons_self)
              exact absurd (by rw [hw, ha]; exact List.mem_cons_self) hhw
          exact inv_free rfl howed rfl hhand (by simp [hw0]) hhead htail hs.enq_nodup hallq hqn
      · -- At the bound: hand off to the head.
        simp only [hb, ite_false]
        -- Nobody was woken: a woken request would be the head below the bound.
        have hwe : s.woken = [] := by
          cases hw : s.woken with
          | nil => rfl
          | cons x l =>
            obtain ⟨t', ht, hbx⟩ := hwk x (by rw [hw]; exact List.mem_cons_self)
            rw [hq] at ht
            simp only [List.cons.injEq] at ht
            obtain ⟨rfl, -⟩ := ht
            exact absurd hbx hb
        rw [List.nodup_cons] at hqn
        exact inv_handoff hfree rfl rfl (by simp [hhand]) (by simp [hwe])
          (fun x hx => hs.tail_zero h t hq x hx) hqn.1 hs.enq_nodup
          (fun x hx => hallq x (List.mem_cons_of_mem _ hx)) (hallq h List.mem_cons_self) hqn.2
  | pollHanded h hw hh =>
    -- The lock was handed to `h` alone, and only `h` is woken.
    have hho : s.owed = some h := by
      have := hs.handed_owed
      rw [this] at hh
      cases ho : s.owed with
      | none => rw [ho] at hh; simp at hh
      | some w => rw [ho] at hh; simp at hh; rw [hh]
    obtain ⟨hhand, hown, hfree⟩ := hs.owed_alone hho
    have hwk : s.woken = [h] := by
      have hsub : ∀ x ∈ s.woken, x = h := by
        intro x hx
        have := hs.owed_woken (by simp [hho]) x hx
        rw [hhand] at this; simpa using this
      cases hw' : s.woken with
      | nil => rw [hw'] at hw; simp at hw
      | cons a l =>
        have ha := hsub a (by rw [hw']; exact List.mem_cons_self)
        subst ha
        have hn := hs.woken_nodup
        rw [hw', List.nodup_cons] at hn
        cases l with
        | nil => rfl
        | cons b l' =>
          have hb := hsub b (by rw [hw']; simp)
          subst hb
          exact absurd List.mem_cons_self hn.1
    refine ⟨by simp [hown, hhand, hfree], by simp [hhand], ?_, by simp [hhand], hs.bypass_le,
      hs.tail_zero, by simp [hfree], by simp, hs.enq_nodup, ?_, hs.queue_nodup, ?_,
      by simp [hwk]⟩
    · intro x hx; simp [hwk] at hx
    · -- The new owner `h` was handed the lock; the rest shrank.
      intro x hx
      apply hs.all_enq x
      rcases hx with hx | hx | hx | hx
      · exact Or.inl hx
      · rcases List.mem_cons.1 hx with e | hx
        · exact Or.inr (Or.inr (Or.inl (e ▸ hh)))
        · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr (Or.inl (List.mem_of_mem_erase hx)))
      · exact Or.inr (Or.inr (Or.inr (List.mem_of_mem_erase hx)))
    · intro x hx
      refine ⟨?_, by simp [hhand]⟩
      simp only [hown, List.mem_cons, List.not_mem_nil, or_false]
      intro e; subst e
      exact (hs.queue_fresh x hx).2 (by rw [hhand]; exact List.mem_cons_self)
  | pollWin h hw hh hf ho =>
    -- The lock was free: nobody held it. `h` is the head.
    obtain ⟨hown, hhand, -⟩ := hs.free_empty hf
    obtain ⟨t, hq, -⟩ := hs.woken_head hw hh
    have hqn := hs.queue_nodup
    rw [hq, List.nodup_cons] at hqn
    -- Only `h` was woken (the free shape), so nobody is woken after.
    have hwk : s.woken = [h] := by rw [hs.free_woken hf, hq]; simp
    -- The head leaves the queue, and its woken bit with it.
    have hqe : s.queue.erase h = t := by rw [hq, List.erase_cons_head]
    have hwe : s.woken.erase h = [] := by rw [hwk, List.erase_cons_head]
    simp only [hqe, hwe]
    refine ⟨by simp [hown, hhand], by simp [hhand, ho], by simp, by simp [hhand], ?_, ?_,
      by simp, by simp [ho], hs.enq_nodup, ?_, hqn.2, ?_, by simp⟩
    · intro x hx; exact hs.bypass_le x (by rw [hq]; exact List.mem_cons_of_mem _ hx)
    · intro h' t' ht' x hx
      -- The new queue is `t`, the old tail.
      have ht2 : t = h' :: t' := ht'
      exact hs.tail_zero h t hq x (by rw [ht2]; exact List.mem_cons_of_mem _ hx)
    · -- The new owner `h` waited; the rest is drawn from before.
      intro x hx
      apply hs.all_enq x
      rcases hx with hx | hx | hx | hx
      · exact Or.inl (by rw [hq]; exact List.mem_cons_of_mem _ hx)
      · rcases List.mem_cons.1 hx with e | hx
        · exact Or.inl (by rw [hq, e]; exact List.mem_cons_self)
        · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr (Or.inl hx))
      · simp at hx
    · intro x hx
      refine ⟨?_, by simp [hhand]⟩
      simp only [hown, List.mem_cons, List.not_mem_nil, or_false]
      intro e; subst e; exact hqn.1 hx
  | pollLose h hw hh hc =>
    -- `h` is the head, with a count below the bound.
    obtain ⟨t, hq, hb⟩ := hs.woken_head hw hh
    have hqn := hs.queue_nodup
    rw [hq, List.nodup_cons] at hqn
    -- The lock is held: a handoff owed means someone holds it.
    have hfree : s.free = false := by
      rcases hc with h' | h'
      · exact h'
      · cases hf : s.free
        · rfl
        · exfalso; exact h' (hs.free_empty hf).2.2
    -- `upd` leaves every request but `h` alone.
    have hupd : ∀ x, x ≠ h → upd s.bypass h (s.bypass h + 1) x = s.bypass x := by
      intro x hx; simp [upd, hx]
    refine ⟨hs.excl, hs.handed_owed, ?_, ?_, ?_, ?_, ?_, ?_, hs.enq_nodup, ?_, hs.queue_nodup,
      hs.queue_fresh, hs.woken_nodup.erase h⟩
    · -- The others woken are as before (not `h`, which is no longer woken).
      intro x hx
      have hx' := (List.Nodup.mem_erase_iff hs.woken_nodup).1 hx
      rcases hs.woken_ok x hx'.2 with h' | ⟨t', ht', -⟩
      · exact Or.inl h'
      · rw [hq] at ht'; simp only [List.cons.injEq] at ht'
        exact absurd ht'.1.symm hx'.1
    · -- `h` holds nothing, so it is not among those handed the lock.
      intro x hx
      have hxh : x ≠ h := fun e => hh (e ▸ hx)
      exact (List.mem_erase_of_ne hxh).2 (hs.handed_woken x hx)
    · -- `h`'s count was below the bound, so one more is within it.
      intro x hx
      by_cases hxh : x = h
      · subst hxh; simp only [upd, ite_true]; omega
      · dsimp only; rw [hupd x hxh]; exact hs.bypass_le x hx
    · -- Those behind `h` are not `h`.
      intro h' t' ht' x hx
      rw [hq] at ht'
      simp only [List.cons.injEq] at ht'
      obtain ⟨-, e2⟩ := ht'
      rw [← e2] at hx
      have hxh : x ≠ h := fun e => hqn.1 (e ▸ hx)
      dsimp only; rw [hupd x hxh]
      exact hs.tail_zero h t hq x hx
    · -- The lock is held.
      intro h' t' _ hf; rw [hfree] at hf; simp at hf
    · -- Fewer woken.
      intro ho x hx
      exact hs.owed_woken ho x (List.mem_of_mem_erase hx)
    · intro x hx
      rcases hx with hx | hx | hx | hx
      · exact hs.all_enq x (Or.inl hx)
      · exact hs.all_enq x (Or.inr (Or.inl hx))
      · exact hs.all_enq x (Or.inr (Or.inr (Or.inl hx)))
      · exact hs.all_enq x (Or.inr (Or.inr (Or.inr (List.mem_of_mem_erase hx))))
  | cancelWaiting r hr =>
    have hqn0 := hs.queue_nodup
    -- `r` holds nothing.
    have hrh : r ∉ s.handed := (hs.queue_fresh r hr).2
    -- The state with `r` gone, before any wake is passed on.
    generalize hX : ({ s with queue := s.queue.erase r, woken := s.woken.erase r } : M) = X
    -- Its fields.
    have hXf : X.free = s.free := by rw [← hX]
    have hXo : X.owed = s.owed := by rw [← hX]
    have hXq : X.queue = s.queue.erase r := by rw [← hX]
    have hXw : X.woken = s.woken.erase r := by rw [← hX]
    have hXown : X.owners = s.owners := by rw [← hX]
    have hXh : X.handed = s.handed := by rw [← hX]
    have hXb : X.bypass = s.bypass := by rw [← hX]
    have hXe : X.enq = s.enq := by rw [← hX]
    -- The queue's head, before.
    obtain ⟨h0, t0, hq⟩ : ∃ h0 t0, s.queue = h0 :: t0 := by
      cases hq : s.queue with
      | nil => rw [hq] at hr; simp at hr
      | cons h0 t0 => exact ⟨h0, t0, rfl⟩
    have hqn := hqn0
    rw [hq, List.nodup_cons] at hqn
    have hall : ∀ x ∈ h0 :: t0, x ∈ s.enq := fun x hx => hs.all_enq x (Or.inl (hq ▸ hx))
    by_cases hf : s.free = true
    · -- The lock is free: nobody holds it, and exactly the head is woken.
      obtain ⟨hown, hhand, howed⟩ := hs.free_empty hf
      have hwk := hs.free_woken hf
      rw [hq] at hwk
      simp only [List.take_succ_cons, List.take_zero] at hwk
      rw [wakeIfFree_free (by rw [hXf, hf]) (by rw [hXo, howed])]
      obtain ⟨wf, wo, wq, wown, wh, wb, we⟩ := wakeHead_fields X
      by_cases hrh0 : r = h0
      · -- The head left: the next waiter (count 0) is the new head, woken.
        have hXq' : X.queue = t0 := by rw [hXq, hq, hrh0, List.erase_cons_head]
        have hXw' : X.woken = [] := by rw [hXw, hwk, hrh0, List.erase_cons_head]
        cases ht0 : t0 with
        | nil =>
          -- Nobody is left to wake.
          rw [wakeHead_nil (by rw [hXq', ht0])]
          exact inv_free (by rw [hXf, hf]) (by rw [hXo, howed]) (by rw [hXown, hown])
            (by rw [hXh, hhand]) (by rw [hXw', hXq', ht0]; rfl) (by rw [hXq', ht0]; simp)
            (by rw [hXq', ht0]; simp) (by rw [hXe]; exact hs.enq_nodup) (by rw [hXq', ht0]; simp)
            (by rw [hXq', ht0]; simp)
        | cons h1 t1 =>
          -- The next waiter becomes the head and is woken.
          have hXq'' : X.queue = h1 :: t1 := by rw [hXq', ht0]
          rw [ht0] at hqn hall
          have hw1 := wakeHead_woken hXq''
          rw [hXw'] at hw1
          apply inv_free (by rw [wf, hXf, hf]) (by rw [wo, hXo, howed]) (by rw [wown, hXown, hown])
            (by rw [wh, hXh, hhand])
          · rw [hw1, wq, hXq'']; simp
          · intro h' t' e
            rw [wq, hXq''] at e
            simp only [List.cons.injEq] at e
            obtain ⟨e1, -⟩ := e
            rw [wb, hXb, ← e1, hs.tail_zero h0 t0 hq h1 (by rw [ht0]; exact List.mem_cons_self)]
            exact hB
          · intro h' t' e x hx
            rw [wq, hXq''] at e
            simp only [List.cons.injEq] at e
            obtain ⟨-, e2⟩ := e
            rw [← e2] at hx
            rw [wb, hXb]
            exact hs.tail_zero h0 t0 hq x (by rw [ht0]; exact List.mem_cons_of_mem _ hx)
          · rw [we, hXe]; exact hs.enq_nodup
          · intro x hx; rw [wq, hXq''] at hx; rw [we, hXe]
            exact hall x (List.mem_cons_of_mem _ hx)
          · rw [wq, hXq'']; exact hqn.2
      · -- A waiter behind the head left: the head stays, still woken.
        have hne : (h0 == r) = false := by simp; exact fun e => hrh0 e.symm
        have hXq' : X.queue = h0 :: t0.erase r := by
          rw [hXq, hq]; exact List.erase_cons_tail (by simpa using hne)
        have hXw' : X.woken = [h0] := by
          rw [hXw, hwk]; exact List.erase_of_not_mem (by simp; exact fun e => hrh0 e)
        have hw1 := wakeHead_woken hXq'
        rw [hXw'] at hw1
        simp only [List.mem_singleton, ite_true] at hw1
        apply inv_free (by rw [wf, hXf, hf]) (by rw [wo, hXo, howed]) (by rw [wown, hXown, hown])
          (by rw [wh, hXh, hhand])
        · rw [hw1, wq, hXq']; simp
        · intro h' t' e
          rw [wq, hXq'] at e
          simp only [List.cons.injEq] at e
          obtain ⟨e1, -⟩ := e
          rw [wb, hXb, ← e1]
          obtain ⟨-, -, hb⟩ := hs.woken_head (h := h0) (by rw [hwk]; simp) (by rw [hhand]; simp)
          exact hb
        · intro h' t' e x hx
          rw [wq, hXq'] at e
          simp only [List.cons.injEq] at e
          obtain ⟨-, e2⟩ := e
          rw [← e2] at hx
          rw [wb, hXb]
          exact hs.tail_zero h0 t0 hq x (List.mem_of_mem_erase hx)
        · rw [we, hXe]; exact hs.enq_nodup
        · intro x hx
          rw [wq, hXq'] at hx
          rw [we, hXe]
          rcases List.mem_cons.1 hx with e | hx
          · rw [e]; exact hall h0 List.mem_cons_self
          · exact hall x (List.mem_cons_of_mem _ (List.mem_of_mem_erase hx))
        · rw [wq, hXq', List.nodup_cons]
          exact ⟨fun hm => hqn.1 (List.mem_of_mem_erase hm), hqn.2.erase r⟩
    · -- The lock is held: no wake is passed on; `r` simply leaves.
      have hf' : s.free = false := by cases h' : s.free <;> simp_all
      rw [wakeIfFree_held (by rw [hXf, hf'])]
      refine ⟨by rw [hXown, hXh, hXf]; exact hs.excl, by rw [hXh, hXo]; exact hs.handed_owed,
        ?_, ?_, ?_, ?_, ?_, ?_, by rw [hXe]; exact hs.enq_nodup, ?_,
        by rw [hXq]; exact hqn0.erase r, ?_, by rw [hXw]; exact hs.woken_nodup.erase r⟩
      · -- A woken request still holds by handoff, or is still the head.
        intro x hx
        rw [hXw] at hx
        rw [hXh, hXq, hXb]
        have hx' := (List.Nodup.mem_erase_iff hs.woken_nodup).1 hx
        rcases hs.woken_ok x hx'.2 with h' | ⟨t', ht', hbx⟩
        · exact Or.inl h'
        · refine Or.inr ⟨t'.erase r, ?_, hbx⟩
          rw [ht']
          exact List.erase_cons_tail (by simpa using fun e => hx'.1 e)
      · -- A handed request is not `r`, so it is still woken.
        intro x hx
        rw [hXh] at hx
        rw [hXw]
        have hxr : x ≠ r := fun e => hrh (e ▸ hx)
        exact (List.mem_erase_of_ne hxr).2 (hs.handed_woken x hx)
      · intro x hx; rw [hXq] at hx; rw [hXb]; exact hs.bypass_le x (List.mem_of_mem_erase hx)
      · -- Behind the head: drawn from the old tail.
        intro h t ht x hx
        rw [hXq] at ht
        rw [hXb]
        by_cases hrh0 : r = h0
        · rw [hq, hrh0, List.erase_cons_head] at ht
          exact hs.tail_zero h0 t0 hq x (by rw [ht]; exact List.mem_cons_of_mem _ hx)
        · rw [hq, List.erase_cons_tail (by simpa using fun e => hrh0 e.symm)] at ht
          simp only [List.cons.injEq] at ht
          obtain ⟨-, e2⟩ := ht
          rw [← e2] at hx
          exact hs.tail_zero h0 t0 hq x (List.mem_of_mem_erase hx)
      · intro h t _ hfr; rw [hXf, hf'] at hfr; simp at hfr
      · intro ho x hx
        rw [hXo] at ho; rw [hXw] at hx; rw [hXh]
        exact hs.owed_woken ho x (List.mem_of_mem_erase hx)
      · intro x hx
        rw [hXq, hXown, hXh, hXw] at hx
        rw [hXe]
        rcases hx with hx | hx | hx | hx
        · exact hs.all_enq x (Or.inl (List.mem_of_mem_erase hx))
        · exact hs.all_enq x (Or.inr (Or.inl hx))
        · exact hs.all_enq x (Or.inr (Or.inr (Or.inl hx)))
        · exact hs.all_enq x (Or.inr (Or.inr (Or.inr (List.mem_of_mem_erase hx))))
      · intro x hx; rw [hXq] at hx; rw [hXown, hXh]
        exact hs.queue_fresh x (List.mem_of_mem_erase hx)
  | cancelHanded r hr =>
    -- The lock was handed to `r` alone, and only `r` is woken.
    have hho : s.owed = some r := by
      have := hs.handed_owed
      rw [this] at hr
      cases ho : s.owed with
      | none => rw [ho] at hr; simp at hr
      | some w => rw [ho] at hr; simp at hr; rw [hr]
    obtain ⟨hhand, hown, hfree⟩ := hs.owed_alone hho
    have hwk : s.woken = [r] := by
      have hsub : ∀ x ∈ s.woken, x = r := by
        intro x hx
        have := hs.owed_woken (by simp [hho]) x hx
        rw [hhand] at this; simpa using this
      have hrw := hs.handed_woken r (by rw [hhand]; exact List.mem_cons_self)
      cases hw' : s.woken with
      | nil => rw [hw'] at hrw; simp at hrw
      | cons a l =>
        have ha := hsub a (by rw [hw']; exact List.mem_cons_self)
        subst ha
        have hn := hs.woken_nodup
        rw [hw', List.nodup_cons] at hn
        cases l with
        | nil => rfl
        | cons b l' =>
          have hb := hsub b (by rw [hw']; simp)
          subst hb
          exact absurd List.mem_cons_self hn.1
    have hqn := hs.queue_nodup
    have hall : ∀ x ∈ s.queue, x ∈ s.enq := fun x hx => hs.all_enq x (Or.inl hx)
    unfold passOn
    simp only [hhand, hwk, List.erase_cons_head]
    cases hq : s.queue with
    | nil =>
      -- Nobody waits: the lock is freed.
      exact inv_free rfl rfl hown rfl (by simp) (by simp) (by simp) hs.enq_nodup (by simp)
        (by simp)
    | cons h t =>
      -- The next waiter is handed the lock.
      rw [hq] at hqn hall
      rw [List.nodup_cons] at hqn
      exact inv_handoff hfree rfl hown (by simp) (by simp)
        (fun x hx => hs.tail_zero h t hq x hx) hqn.1 hs.enq_nodup
        (fun x hx => hall x (List.mem_cons_of_mem _ hx)) (hall h List.mem_cons_self) hqn.2

/-- Several steps keep the invariant. -/
theorem steps_inv {B : Nat}
    -- The bound is at least 1.
    (hB : 0 < B) {s t : M}
    -- The invariant holds at the start.
    (hs : Inv B s)
    -- Any number of steps.
    (hsteps : Steps B s t) :
    Inv B t := by
  induction hsteps with
  -- No step: nothing changed.
  | refl => exact hs
  -- The steps so far, then one more.
  | tail _ hstep ih => exact step_inv hB ih hstep

/-- **Every reachable state satisfies the invariant.** -/
theorem reachable_inv {B : Nat}
    -- The bound is at least 1.
    (hB : 0 < B) {s : M}
    -- `s` is reachable from the start.
    (h : Steps B init s) :
    Inv B s :=
  steps_inv hB (init_inv B) h

/-! ## The laws -/

/-- **Mutual exclusion.** At most one request holds the lock, and none
while it is free. TLA+: `MutualExclusion`. -/
theorem mutual_exclusion {B : Nat}
    -- The bound is at least 1.
    (hB : 0 < B) {s : M}
    -- `s` is reachable from the start.
    (h : Steps B init s) :
    (s.owners ++ s.handed).length ≤ 1 ∧ (s.free = true → s.owners ++ s.handed = []) := by
  have hx := (reachable_inv hB h).excl
  refine ⟨by split at hx <;> omega, fun hf => ?_⟩
  rw [hf] at hx
  simp only [ite_true] at hx
  exact List.length_eq_zero_iff.1 (by omega)

/-- **Bounded bypass.** A waiting request's count of lost races never
exceeds the bound `B`. TLA+: `BoundedBypass`. -/
theorem bounded_bypass {B : Nat}
    -- The bound is at least 1.
    (hB : 0 < B) {s : M}
    -- `s` is reachable from the start.
    (h : Steps B init s) {x : Nat}
    -- `x` waits.
    (hx : x ∈ s.queue) :
    s.bypass x ≤ B :=
  (reachable_inv hB h).bypass_le x hx

/-- **A loss happens only below the bound.** A woken request that was not
handed the lock (the only kind that can lose) has lost fewer than `B`
races; so a loss takes its count to at most `B`. -/
theorem lose_below_bound {B : Nat}
    -- The bound is at least 1.
    (hB : 0 < B) {s : M}
    -- `s` is reachable from the start.
    (h : Steps B init s) {x : Nat}
    -- `x` was woken ...
    (hw : x ∈ s.woken)
    -- ... and not handed the lock.
    (hh : x ∉ s.handed) :
    s.bypass x < B := by
  obtain ⟨-, -, hb⟩ := (reachable_inv hB h).woken_head hw hh
  exact hb

/-- **The count counts losses.** A step that changes a waiting request's
count adds one to it, and the request was woken and not handed the lock:
it lost a race. With `lose_below_bound` and `bounded_bypass`, a request
loses at most `B` races in one acquire. -/
theorem bypass_counts_losses {B : Nat}
    -- The bound is at least 1.
    (hB : 0 < B) {s t : M}
    -- `s` is reachable from the start.
    (h : Steps B init s)
    -- One step.
    (hstep : Step B s t) {x : Nat}
    -- `x` waits.
    (hx : x ∈ s.queue)
    -- Its count changed.
    (hne : t.bypass x ≠ s.bypass x) :
    t.bypass x = s.bypass x + 1 ∧ x ∈ s.woken ∧ x ∉ s.handed := by
  have hs := reachable_inv hB h
  -- The helpers leave every count alone.
  have hwh : ∀ u : M, (wakeHead u).bypass = u.bypass := by
    intro u; unfold wakeHead; split
    · rfl
    · split <;> rfl
  cases hstep with
  | fast => exact absurd rfl hne
  | enqueue r hr _ =>
    -- `r` is fresh, so not `x`, which entered before.
    have hxr : x ≠ r := fun e => hr (e ▸ hs.all_enq x (Or.inl hx))
    simp [upd, hxr] at hne
  | release r _ =>
    exfalso; apply hne
    unfold relFrom; split
    · rfl
    · split
      · rw [hwh]
      · rfl
  | pollHanded => exact absurd rfl hne
  | pollWin => exact absurd rfl hne
  | pollLose h' hw hh _ =>
    -- Only the loser's count changes.
    by_cases hxh : x = h'
    · subst hxh; simp only [upd, ite_true]; exact ⟨trivial, hw, hh⟩
    · simp [upd, hxh] at hne
  | cancelWaiting r _ =>
    exfalso; apply hne
    unfold wakeIfFree; split
    · rw [hwh]
    · rfl
  | cancelHanded r _ =>
    exfalso; apply hne
    unfold passOn; split <;> rfl

/-- **At the bound, the next release hands off.** If the head has lost
`B` races and the owner releases, the head is handed the lock: owed, held
by it, woken, and the lock is not free. -/
theorem release_hands_off_at_bound {B : Nat} {s : M} {h r : Nat} {t : List Nat}
    -- `h` is the head ...
    (hq : s.queue = h :: t)
    -- ... and has lost `B` races.
    (hb : B ≤ s.bypass h) :
    let u := relFrom B { s with owners := s.owners.erase r }
    u.owed = some h ∧ h ∈ u.handed ∧ h ∈ u.woken ∧ u.free = s.free := by
  have : ¬ s.bypass h < B := by omega
  simp [relFrom, hq, this]

/-- **Handoff-owed exclusivity, state.** While a handoff is owed to `w`,
`w` alone holds the lock, by handoff, and the lock is not free.
TLA+: `HandoffExclusive`. -/
theorem owed_exclusive {B : Nat}
    -- The bound is at least 1.
    (hB : 0 < B) {s : M}
    -- `s` is reachable from the start.
    (h : Steps B init s) {w : Nat}
    -- A handoff is owed to `w`.
    (hw : s.owed = some w) :
    s.handed = [w] ∧ s.owners = [] ∧ s.free = false :=
  (reachable_inv hB h).owed_alone hw

/-- **Handoff-owed exclusivity, steps.** While a handoff is owed to `w`,
no step makes anyone but `w` an owner: barging is shut, and the lock goes
to `w`. TLA+: `HandoffExclusive`. -/
theorem owed_blocks_barging {B : Nat}
    -- The bound is at least 1.
    (hB : 0 < B) {s t : M}
    -- `s` is reachable from the start.
    (h : Steps B init s) {w : Nat}
    -- A handoff is owed to `w`.
    (hw : s.owed = some w)
    -- One step.
    (hstep : Step B s t) :
    ∀ x ∈ t.owners, x ∈ s.owners ∨ x = w := by
  have hs := reachable_inv hB h
  obtain ⟨hhand, hown, hfree⟩ := hs.owed_alone hw
  intro x hx
  cases hstep with
  | fast _ _ _ ho => rw [hw] at ho; simp at ho
  | enqueue => exact Or.inl hx
  | release r hr => rw [hown] at hr; simp at hr
  | pollHanded h' _ hh =>
    -- The new owner is the one handed the lock: `w`.
    rw [hhand] at hh
    simp only [List.mem_singleton] at hh
    subst hh
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Or.inr rfl
    · exact Or.inl hx
  | pollWin _ _ _ hf => rw [hfree] at hf; simp at hf
  | pollLose => exact Or.inl hx
  | cancelWaiting r _ =>
    -- The lock is held: no wake, no owner change.
    have : (wakeIfFree { s with queue := s.queue.erase r, woken := s.woken.erase r }).owners =
        s.owners := by
      unfold wakeIfFree; simp only [hfree, Bool.false_eq_true, false_and, ite_false]
    rw [this] at hx; exact Or.inl hx
  | cancelHanded r _ =>
    -- A passed-on handoff makes nobody an owner yet.
    have : (passOn { s with handed := s.handed.erase r, woken := s.woken.erase r,
                            owed := none }).owners = s.owners := by
      unfold passOn; split <;> rfl
    rw [this] at hx; exact Or.inl hx

/-- **No stranded head.** While the lock is free, the head waiter has been
woken: no waiter sleeps beside a free lock. TLA+: `NoLostWakeup`. -/
theorem no_stranded_head {B : Nat}
    -- The bound is at least 1.
    (hB : 0 < B) {s : M}
    -- `s` is reachable from the start.
    (h : Steps B init s) {x : Nat} {t : List Nat}
    -- `x` is the head.
    (hq : s.queue = x :: t)
    -- The lock is free.
    (hf : s.free = true) :
    x ∈ s.woken :=
  (reachable_inv hB h).stranded x t hq hf

/-- **A handoff is woken.** A request handed the lock has been woken.
TLA+: `NoLostWakeup` (GrantedWoken). -/
theorem handed_woken {B : Nat}
    -- The bound is at least 1.
    (hB : 0 < B) {s : M}
    -- `s` is reachable from the start.
    (h : Steps B init s) {x : Nat}
    -- `x` was handed the lock.
    (hx : x ∈ s.handed) :
    x ∈ s.woken :=
  (reachable_inv hB h).handed_woken x hx

/-! ## The RED cases -/

/-- The unbounded-barging design: a release always frees the lock and
wakes the head; it never hands off. -/
inductive StepNoHand : M → M → Prop
  /-- As `Step.fast`. -/
  | fast (s : M) (r : Nat)
      -- `r` is fresh, the lock free, nothing owed.
      (hr : r ∉ s.enq) (hf : s.free = true) (ho : s.owed = none) :
      StepNoHand s { s with free := false, owners := r :: s.owners, enq := s.enq ++ [r] }
  /-- As `Step.enqueue`. -/
  | enqueue (s : M) (r : Nat)
      -- `r` is fresh, and the fast path is shut.
      (hr : r ∉ s.enq) (hc : s.free = false ∨ s.owed ≠ none) :
      StepNoHand s { s with queue := s.queue ++ [r], enq := s.enq ++ [r],
                            bypass := upd s.bypass r 0 }
  /-- The defect: free and wake the head, whatever its count. -/
  | release (s : M) (r : Nat)
      -- `r` holds the lock.
      (hr : r ∈ s.owners) :
      StepNoHand s (wakeHead { s with owners := s.owners.erase r, free := true })
  /-- As `Step.pollLose`. -/
  | pollLose (s : M) (h : Nat)
      -- `h` was woken, not handed, and the fast path is shut.
      (hw : h ∈ s.woken) (hh : h ∉ s.handed) (hc : s.free = false ∨ s.owed ≠ none) :
      StepNoHand s { s with bypass := upd s.bypass h (s.bypass h + 1), woken := s.woken.erase h }

/-- Any number of `StepNoHand` steps. -/
inductive StepsNoHand : M → M → Prop
  /-- No step at all. -/
  | refl (s : M) : StepsNoHand s s
  /-- Some steps, then one more. -/
  | tail {s t u : M} : StepsNoHand s t → StepNoHand t u → StepsNoHand s u

/-- **`unbounded_barging_breaks_bound`.** With bound 1 and no handoff,
request 2 waits, is woken, and loses to barging request 3; at release it
is woken again (the design would hand it the lock here) and loses to
barging request 4. It has lost 2 races, more than the bound: the law of
`bounded_bypass` fails. -/
theorem unbounded_barging_breaks_bound :
    ∃ s, StepsNoHand init s ∧ 2 ∈ s.queue ∧ s.bypass 2 = 2 := by
  refine ⟨_, .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.refl init)
    -- Request 1 takes the lock; request 2 waits.
    (.fast _ 1 (by decide) rfl rfl))
    (.enqueue _ 2 (by decide) (Or.inl rfl)))
    -- Request 1 releases: the lock is free and request 2 woken.
    (.release _ 1 (by decide)))
    -- Request 3 barges in; request 2 is polled and loses.
    (.fast _ 3 (by decide) rfl rfl))
    (.pollLose _ 2 (by decide) (by decide) (Or.inl rfl)))
    -- Request 3 releases: no handoff, request 2 woken again.
    (.release _ 3 (by decide)))
    -- Request 4 barges in; request 2 loses again.
    (.fast _ 4 (by decide) rfl rfl))
    (.pollLose _ 2 (by decide) (by decide) (Or.inl rfl)), by decide, by decide⟩

/-- The release-without-wake design: a release with waiters frees the lock
and wakes nobody. -/
inductive StepNoWake : M → M → Prop
  /-- As `Step.fast`. -/
  | fast (s : M) (r : Nat)
      -- `r` is fresh, the lock free, nothing owed.
      (hr : r ∉ s.enq) (hf : s.free = true) (ho : s.owed = none) :
      StepNoWake s { s with free := false, owners := r :: s.owners, enq := s.enq ++ [r] }
  /-- As `Step.enqueue`. -/
  | enqueue (s : M) (r : Nat)
      -- `r` is fresh, and the fast path is shut.
      (hr : r ∉ s.enq) (hc : s.free = false ∨ s.owed ≠ none) :
      StepNoWake s { s with queue := s.queue ++ [r], enq := s.enq ++ [r],
                            bypass := upd s.bypass r 0 }
  /-- The defect: free the lock, wake nobody. -/
  | release (s : M) (r : Nat)
      -- `r` holds the lock.
      (hr : r ∈ s.owners) :
      StepNoWake s { s with owners := s.owners.erase r, free := true }

/-- Any number of `StepNoWake` steps. -/
inductive StepsNoWake : M → M → Prop
  /-- No step at all. -/
  | refl (s : M) : StepsNoWake s s
  /-- Some steps, then one more. -/
  | tail {s t u : M} : StepsNoWake s t → StepNoWake t u → StepsNoWake s u

/-- **`release_without_wake_strands`.** Request 1 holds, request 2 waits,
request 1 releases without waking anyone: the lock is free and its head,
request 2, is not woken. The law of `no_stranded_head` fails. -/
theorem release_without_wake_strands :
    ∃ s, StepsNoWake init s ∧ s.queue = [2] ∧ s.free = true ∧ 2 ∉ s.woken := by
  refine ⟨_, .tail (.tail (.tail (.refl init)
    -- Request 1 takes the lock; request 2 waits.
    (.fast _ 1 (by decide) rfl rfl))
    (.enqueue _ 2 (by decide) (Or.inl rfl)))
    -- Request 1 releases and wakes nobody.
    (.release _ 1 (by decide)), by decide, rfl, by decide⟩

end Regolith.Sync
