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

## The story, for a reader who has never seen the code

A lock lets one task at a time into a piece of code. regolith's async locks
(src/sync/) let a task take the lock whenever it is free, even when others
are queued for it ("barging"): the alternative, handing the lock to the
longest waiter, leaves it idle until that sleeping task is scheduled.

Tiny example of what barging can do: task A waits. Every time the lock is
released A is woken, but task B, already running, grabs the lock first.
A loses the race again and again. So a waiter counts its lost races, and
once it has lost `B` of them the next release hands the lock straight to it
and nobody may barge meanwhile.

What could go wrong: two holders at once; a waiter that loses for ever; a
newcomer slipping in during a handoff; a waiter asleep beside a free lock.
The theorems below rule each of these out for the abstract lock, for any
number of requests.

One difference from the code on this branch (src/sync/contend.rs): there
the waiter itself raises the owed bit, in the retry that would be its
`MAX_BYPASS`-th loss (`Lock::take_or_owe`), and the next drain pass hands
the lock over; here the release decides the handoff when it sees a head
that has lost `B` races. The bound proved is the same; the step that
establishes it is not the code's.

## The protocol

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

-- Everything below is named Regolith.Sync.<name>.
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
  -- Look at the queue.
  match s.queue with
  -- Nobody waits: nobody to wake.
  | [] => s
  -- The head `h` is woken if it is not already.
  | h :: _ => if h ∈ s.woken then s else { s with woken := s.woken ++ [h] }

/-- A release, after the owner's guard is gone: free the lock and wake
the head, or, if the head has lost `B` races, hand it the lock (it stays
held), set the owed bit and wake it. -/
def relFrom (B : Nat) (s : M) : M :=
  -- Look at the queue.
  match s.queue with
  -- Nobody waits: one RMW frees the lock.
  | [] => { s with free := true }
  -- A head h, with the others t behind it:
  | h :: t =>
    -- has the head lost fewer than B races?
    if s.bypass h < B
      -- Below the bound: free, and the head competes when polled.
      then wakeHead { s with free := true }
      -- At the bound: hand off; the head is popped, holds, and is woken.
      else { s with owed := some h, handed := s.handed ++ [h], queue := t,
                    woken := s.woken ++ [h] }

/-- A handoff passes on (its waiter was cancelled): to the next waiter,
whatever its count, or the lock is freed if nobody waits. -/
def passOn (s : M) : M :=
  -- Look at the queue.
  match s.queue with
  -- Nobody waits: free the lock.
  | [] => { s with free := true }
  -- The next waiter is handed the lock, and woken.
  | h :: t => { s with owed := some h, handed := s.handed ++ [h], queue := t,
                       woken := s.woken ++ [h] }

/-- After a waiting request leaves: if the lock is free and no handoff is
owed, the new head is woken (a wake the leaver had is passed on). -/
def wakeIfFree (s : M) : M :=
  -- With the lock free and no handoff owed, wake the head; otherwise change nothing.
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
      -- After the step: the lock is held, r is an owner, and r has entered.
      Step B s { s with free := false, owners := r :: s.owners, enq := s.enq ++ [r] }
  /-- A contended lock: the fast path failed, so the fresh request `r`
  registers at the tail with a count of 0. (Its re-check after registering
  is the fast path again, which failed for the same reason.) -/
  | enqueue (s : M) (r : Nat)
      -- `r` is a fresh request.
      (hr : r ∉ s.enq)
      -- The fast path is shut: the lock is held, or a handoff is owed.
      (hc : s.free = false ∨ s.owed ≠ none) :
      -- After the step: r is at the tail of the queue, has entered, and has a count of 0.
      Step B s { s with queue := s.queue ++ [r], enq := s.enq ++ [r], bypass := upd s.bypass r 0 }
  /-- An owner drops its guard. -/
  | release (s : M) (r : Nat)
      -- `r` holds the lock.
      (hr : r ∈ s.owners) :
      -- After the step: r is no longer an owner, and the release rule ran.
      Step B s (relFrom B { s with owners := s.owners.erase r })
  /-- A woken request that was handed the lock takes it; the owed bit
  clears. -/
  | pollHanded (s : M) (h : Nat)
      -- `h` was woken ...
      (hw : h ∈ s.woken)
      -- ... and handed the lock.
      (hh : h ∈ s.handed) :
      -- After the step: h is an owner, no longer "handed",
      Step B s { s with owners := h :: s.owners, handed := s.handed.erase h,
                        -- no longer "woken", and no handoff is owed.
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
      -- After the step: the lock is held, h is an owner, h has left the queue,
      Step B s { s with free := false, owners := h :: s.owners, queue := s.queue.erase h,
                        -- and h is no longer "woken".
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
      -- After the step: h's count is one more, and h is no longer "woken".
      Step B s { s with bypass := upd s.bypass h (s.bypass h + 1), woken := s.woken.erase h }
  /-- A waiting request's future is dropped: it leaves, and a wake it had
  passes to the new head. -/
  | cancelWaiting (s : M) (r : Nat)
      -- `r` waits.
      (hr : r ∈ s.queue) :
      -- After the step: r has left the queue and the woken list, and the new head is woken if the
      -- lock is free.
      Step B s (wakeIfFree { s with queue := s.queue.erase r, woken := s.woken.erase r })
  /-- A request handed the lock is dropped before it was polled: the
  handoff passes on. -/
  | cancelHanded (s : M) (r : Nat)
      -- `r` was handed the lock.
      (hr : r ∈ s.handed) :
      -- After the step: r is no longer "handed" or "woken", nothing is owed for a moment,
      Step B s (passOn { s with handed := s.handed.erase r, woken := s.woken.erase r,
                                -- and the handoff passes on.
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
    -- The statement: l is the one-element list [x].
    l = [x] := by
  -- One element: `l = [a]`, and `x ∈ [a]` means `x = a`.
  -- Look at l, knowing its length is 1.
  match l, hl with
  -- It is [a] for some a; x is in it, so x is a; replace.
  | [a], _ => simp only [List.mem_singleton] at hx; rw [hx]

/-- Under the invariant, if `r` owns the lock, it is held by `r` alone. -/
theorem Inv.owner_alone {B : Nat} {s : M}
    -- The invariant holds.
    (hs : Inv B s) {r : Nat}
    -- `r` owns the lock.
    (hr : r ∈ s.owners) :
    -- The statement: r is the only owner, nobody was handed the lock, the lock is not free, and no
    -- handoff is owed.
    s.owners = [r] ∧ s.handed = [] ∧ s.free = false ∧ s.owed = none := by
  -- Start from "the holders plus one-if-free make exactly 1".
  have hx := hs.excl
  -- `r` is among the holders, so the holders are not empty.
  have hpos : 0 < (s.owners ++ s.handed).length :=
    -- (r is one of the holders)
    List.length_pos_of_mem (List.mem_append.2 (Or.inl hr))
  -- So the lock is not free, and there is exactly one holder.
  have hfree : s.free = false := by
    -- Split on whether the lock is free.
    cases hf : s.free
    -- Not free: that is the claim.
    · rfl
    -- Free: then there would be at least one holder plus one for "free", more than 1. Arithmetic
    -- says no.
    · rw [hf] at hx; simp only [ite_true] at hx; omega
  -- Use "not free" in the count.
  rw [hfree] at hx
  -- The count now says: the holders number exactly 1.
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at hx
  -- A one-element list holding r is [r].
  have h1 := eq_single_of_mem hx (List.mem_append.2 (Or.inl hr))
  -- The single holder is `r`, an owner; nobody is handed the lock.
  have ho : s.owners = [r] := by
    -- Split on the owners list.
    cases ho : s.owners with
    -- Empty: but r is an owner. Impossible.
    | nil => rw [ho] at hr; simp at hr
    -- A first owner a and more owners l.
    | cons a l =>
      -- Use that shape in "the holders are [r]".
      rw [ho] at h1
      -- Compare the two lists piece by piece.
      simp only [List.cons_append, List.cons.injEq, List.append_eq_nil_iff] at h1
      -- So a is r, and nothing follows.
      obtain ⟨rfl, rfl, -⟩ := h1
      -- The owners are [r].
      rfl
  -- Nobody was handed the lock:
  have hh : s.handed = [] := by
    -- The holders are [r] and the owners are [r]: nobody is left to be "handed".
    rw [ho] at h1; simpa using h1
  -- No handoff pending, so none owed.
  have hn : s.owed = none := by
    -- The "handed" list is the owed request, if any.
    have := hs.handed_owed
    -- And the "handed" list is empty.
    rw [hh] at this
    -- Split on the owed bit.
    cases ho' : s.owed with
    -- None owed: that is the claim.
    | none => rfl
    -- Owed to w: then w would be "handed". Impossible.
    | some w => rw [ho'] at this; simp at this
  -- All four parts.
  exact ⟨ho, hh, hfree, hn⟩

/-- Under the invariant, a handoff owed to `w` means `w` alone holds the
lock, by handoff, and the lock is not free. -/
theorem Inv.owed_alone {B : Nat} {s : M}
    -- The invariant holds.
    (hs : Inv B s) {w : Nat}
    -- A handoff is owed to `w`.
    (hw : s.owed = some w) :
    -- The statement: w alone was handed the lock, there is no owner, and the lock is not free.
    s.handed = [w] ∧ s.owners = [] ∧ s.free = false := by
  -- The "handed" list is the owed request: [w].
  have hh : s.handed = [w] := by rw [hs.handed_owed, hw]; rfl
  -- Start from "the holders plus one-if-free make exactly 1".
  have hx := hs.excl
  -- w is one holder already.
  rw [hh] at hx
  -- One holder already: no owner, and the lock is not free.
  have : s.owners = [] ∧ s.free = false := by
    -- Split on the owners list.
    cases ho : s.owners with
    -- No owner.
    | nil =>
      -- Split on whether the lock is free.
      cases hf : s.free
      -- Not free: both claims hold.
      · exact ⟨rfl, rfl⟩
      -- Free: one holder plus one for "free" is 2, not 1. Impossible.
      · rw [ho, hf] at hx; simp at hx
    -- An owner as well: at least two holders. Impossible by arithmetic.
    | cons a l => rw [ho] at hx; simp at hx; omega
  -- All three parts.
  exact ⟨hh, this⟩

/-- Under the invariant, while the lock is free nobody holds it. -/
theorem Inv.free_empty {B : Nat} {s : M}
    -- The invariant holds.
    (hs : Inv B s)
    -- The lock is free.
    (hf : s.free = true) :
    -- The statement: there is no owner, nobody was handed the lock, and no handoff is owed.
    s.owners = [] ∧ s.handed = [] ∧ s.owed = none := by
  -- Start from "the holders plus one-if-free make exactly 1".
  have hx := hs.excl
  -- The lock is free.
  rw [hf] at hx
  -- So the count says: holders plus 1 is 1.
  simp only [ite_true] at hx
  -- So there are no holders.
  have hl : (s.owners ++ s.handed).length = 0 := by omega
  -- An empty joined list means both parts are empty.
  rw [List.length_eq_zero_iff, List.append_eq_nil_iff] at hl
  -- Name the two parts: no owners, nobody handed.
  obtain ⟨ho, hh⟩ := hl
  -- Two of the three claims; "nothing owed" is left.
  refine ⟨ho, hh, ?_⟩
  -- No handoff pending, so none owed.
  have := hs.handed_owed
  -- The "handed" list is empty.
  rw [hh] at this
  -- Split on the owed bit.
  cases ho' : s.owed with
  -- None owed: that is the claim.
  | none => rfl
  -- Owed to w: then w would be "handed". Impossible.
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
    -- The statement: h is the head of the queue, with a count below B.
    ∃ t, s.queue = h :: t ∧ s.bypass h < B := by
  -- A woken request was handed the lock, or is the head below the bound.
  rcases hs.woken_ok h hw with hx | hx
  -- Handed: but h was not.
  · exact absurd hx hh
  -- The head below the bound: that is the claim.
  · exact hx

/-! ## What the helpers change -/

/-- Waking the head changes only the woken list: here is every other
field, unchanged. -/
theorem wakeHead_fields (u : M) :
    -- The statement: after waking the head, every field but the woken list is what it was.
    (wakeHead u).free = u.free ∧ (wakeHead u).owed = u.owed ∧ (wakeHead u).queue = u.queue ∧
    (wakeHead u).owners = u.owners ∧ (wakeHead u).handed = u.handed ∧
    (wakeHead u).bypass = u.bypass ∧ (wakeHead u).enq = u.enq := by
  -- Each branch keeps the fields, or replaces only `woken`.
  unfold wakeHead
  -- Split on the queue.
  split
  -- Nobody waits: nothing changed at all.
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- A head: whether it was already woken or not, only the woken list can differ.
  · split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Waking the head when the queue is `h :: t`: `h` joins the woken list
unless it is in it already. -/
theorem wakeHead_woken {u : M} {h : Nat} {t : List Nat}
    -- The head is `h`.
    (hq : u.queue = h :: t) :
    -- The statement: the woken list afterwards is the old one, plus h unless h was in it.
    (wakeHead u).woken = if h ∈ u.woken then u.woken else u.woken ++ [h] := by
  -- The match takes the `h :: t` branch.
  simp only [wakeHead, hq]
  -- Whether h was already woken or not, both sides are the same list.
  split <;> rfl

/-- Waking the head of an empty queue changes nothing. -/
theorem wakeHead_nil {u : M}
    -- Nobody waits.
    (hq : u.queue = []) :
    -- The statement: nothing changes.
    wakeHead u = u := by
  -- Unfold "wake the head".
  unfold wakeHead
  -- The queue is empty, so the first branch is taken.
  rw [hq]

/-- With the lock free and nothing owed, `wakeIfFree` wakes the head. -/
theorem wakeIfFree_free {u : M}
    -- The lock is free ...
    (hf : u.free = true)
    -- ... and nothing is owed.
    (ho : u.owed = none) :
    -- The statement: here "wake if free" is "wake the head".
    wakeIfFree u = wakeHead u := by
  -- Unfold "wake if free".
  unfold wakeIfFree
  -- Its condition is true.
  simp [hf, ho]

/-- With the lock held, `wakeIfFree` changes nothing. -/
theorem wakeIfFree_held {u : M}
    -- The lock is held.
    (hf : u.free = false) :
    -- The statement: here "wake if free" changes nothing.
    wakeIfFree u = u := by
  -- Unfold "wake if free".
  unfold wakeIfFree
  -- Its condition is false.
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
    -- The statement: such a state satisfies the invariant.
    Inv B u := by
  -- The woken requests are the head, which is in the queue.
  have hwq : ∀ x ∈ u.woken, ∃ t, u.queue = x :: t := by
    -- Take a woken request x.
    intro x hx
    -- The woken ones are the first element of the queue, if any.
    rw [hw] at hx
    -- Split on the queue.
    cases hq : u.queue with
    -- Empty: then nobody is woken. Impossible.
    | nil => rw [hq] at hx; simp at hx
    -- A head h: then x is h, and the queue starts with x.
    | cons h t => rw [hq] at hx; simp at hx; exact ⟨t, by rw [hx]⟩
  -- Thirteen facts. Those settled at once: one free lock and no holders; nothing handed and nothing
  -- owed; nothing handed needs waking; the tail counts (given); nothing owed; entries are distinct
  -- (given); the queue is distinct (given); a waiter is no holder.
  refine ⟨by simp [hf, hown, hh], by simp [hh, ho], ?_, by simp [hh], ?_, htail, ?_,
    by simp [ho], hen, ?_, hqn, by simp [hown, hh], ?_⟩
  -- A woken request is the head, below the bound.
  ·
    -- Take a woken request x.
    intro x hx
    -- It is the head.
    obtain ⟨t, ht⟩ := hwq x hx
    -- The head is below the bound: the second alternative.
    exact Or.inr ⟨t, ht, hhead x t ht⟩
  -- The head is below the bound; the others are at 0.
  ·
    -- Take a waiting request x.
    intro x hx
    -- Split on the queue.
    cases hq : u.queue with
    -- Empty: then nobody waits. Impossible.
    | nil => rw [hq] at hx; simp at hx
    -- A head h and a tail t.
    | cons h t =>
      -- x is in h :: t.
      rw [hq] at hx
      -- x is the head, or in the tail.
      rcases List.mem_cons.1 hx with rfl | hx
      -- The head: below B, so at most B.
      · exact Nat.le_of_lt (hhead x t hq)
      -- In the tail: its count is 0, which is at most B.
      · rw [htail h t hq x hx]; exact Nat.zero_le _
  -- The head is the woken one.
  ·
    -- Take the queue's head h.
    intro h t hq _
    -- The woken list is the first element of the queue: [h].
    rw [hw, hq]
    -- h is in [h].
    simp
  -- Every request named entered: owners and handed are empty, the woken one waits.
  ·
    -- Take a request x that waits, owns, was handed, or was woken.
    intro x hx
    -- Split on which.
    rcases hx with hx | hx | hx | hx
    -- It waits: every waiter entered.
    · exact hall x hx
    -- It owns: there is no owner. Impossible.
    · rw [hown] at hx; simp at hx
    -- It was handed: nobody was. Impossible.
    · rw [hh] at hx; simp at hx
    -- It was woken: then it is the head of the queue,
    · obtain ⟨t, ht⟩ := hwq x hx
      -- and every waiter entered.
      exact hall x (by rw [ht]; exact List.mem_cons_self)
  -- At most one woken request.
  ·
    -- The woken list is the first element of the queue.
    rw [hw]
    -- Split on the queue.
    cases u.queue with
    -- Empty: nobody woken, trivially distinct.
    | nil => simp
    -- A head: one woken request, trivially distinct.
    | cons h t => simp

/-- **A lock just handed off.** Request `h` was handed the lock, owed and
woken; nobody else holds it or is woken; the waiters left have counts of
0. Such a state satisfies the invariant. -/
theorem inv_handoff {B : Nat} {u : M} {h : Nat}
    -- The lock is held, by handoff to `h`, which is owed and woken.
    (hf : u.free = false) (ho : u.owed = some h) (hown : u.owners = []) (hh : u.handed = [h])
    -- (the woken list is exactly [h])
    (hw : u.woken = [h])
    -- The waiters left have not lost.
    (hz : ∀ x ∈ u.queue, u.bypass x = 0)
    -- `h` no longer waits.
    (hhq : h ∉ u.queue)
    -- Requests entered once; every waiter, and `h`, entered.
    (hen : u.enq.Nodup) (hall : ∀ x ∈ u.queue, x ∈ u.enq) (hhe : h ∈ u.enq)
    -- No request waits twice.
    (hqn : u.queue.Nodup) :
    -- The statement: such a state satisfies the invariant.
    Inv B u := by
  -- Thirteen facts. Settled at once: one holder and not free; the handed one is the owed one;
  -- entries are distinct (given); the queue is distinct (given). The rest follow.
  refine ⟨by simp [hf, hown, hh], by simp [hh, ho], ?_, ?_, ?_, ?_, ?_, ?_, hen, ?_, hqn, ?_, ?_⟩
  -- The woken one holds by handoff.
  ·
    -- Take a woken x: it is h, and h is handed: the first alternative.
    intro x hx; rw [hw] at hx; left; rw [hh]; exact hx
  -- The handed one is woken.
  ·
    -- Take a handed x: it is h, and h is woken.
    intro x hx; rw [hh] at hx; rw [hw]; exact hx
  -- Waiters are at 0.
  ·
    -- Take a waiter x: its count is 0, at most B.
    intro x hx; rw [hz x hx]; exact Nat.zero_le _
  -- Waiters are at 0.
  ·
    -- Take the queue's head and a waiter x behind it: x waits, so its count is 0.
    intro h' t hq x hx; exact hz x (by rw [hq]; exact List.mem_cons_of_mem _ hx)
  -- The lock is held.
  ·
    -- "The lock is free" contradicts "the lock is held": nothing to show.
    intro h' t _ hfr; rw [hf] at hfr; simp at hfr
  -- Only the handed one is woken.
  ·
    -- Take a woken x: it is h, and h is handed.
    intro _ x hx; rw [hw] at hx; rw [hh]; exact hx
  -- Every request named entered.
  ·
    -- Take a request x that waits, owns, was handed, or was woken.
    intro x hx
    -- Split on which.
    rcases hx with hx | hx | hx | hx
    -- It waits: every waiter entered.
    · exact hall x hx
    -- It owns: there is no owner. Impossible.
    · rw [hown] at hx; simp at hx
    -- It was handed: then it is h, which entered.
    · rw [hh] at hx; simp at hx; rw [hx]; exact hhe
    -- It was woken: then it is h, which entered.
    · rw [hw] at hx; simp at hx; rw [hx]; exact hhe
  -- A waiter is neither an owner nor `h`.
  ·
    -- Take a waiter x.
    intro x hx
    -- There is no owner; "x was not handed" is left.
    refine ⟨by simp [hown], ?_⟩
    -- The handed list is [h], so "handed" means "is h".
    rw [hh]; simp only [List.mem_singleton]
    -- If x were h, then h would wait. It does not.
    intro e; subst e; exact hhq hx
  -- One woken request.
  ·
    -- The woken list is [h]: trivially distinct.
    rw [hw]; simp

/-- Under the invariant, while the lock is free exactly the head (if any)
is woken. -/
theorem Inv.free_woken {B : Nat} {s : M}
    -- The invariant holds.
    (hs : Inv B s)
    -- The lock is free.
    (hf : s.free = true) :
    -- The statement: the woken list is the first element of the queue (or empty).
    s.woken = s.queue.take 1 := by
  -- With the lock free, nobody was handed it.
  obtain ⟨-, hh, -⟩ := hs.free_empty hf
  -- Every woken request is the head.
  have hsub : ∀ x ∈ s.woken, ∃ t, s.queue = x :: t := by
    -- Take a woken x.
    intro x hx
    -- It was handed the lock, or it is the head.
    rcases hs.woken_ok x hx with h' | ⟨t, ht, -⟩
    -- Handed: nobody was. Impossible.
    · rw [hh] at h'; simp at h'
    -- The head: that is the claim.
    · exact ⟨t, ht⟩
  -- Split on the queue.
  cases hq : s.queue with
  -- Case: nobody waits.
  | nil =>
    -- No head: nobody woken.
    cases hw : s.woken with
    -- Nobody woken: both sides are empty.
    | nil => rfl
    -- Somebody woken, x:
    | cons x l =>
      -- then x would be the head of the queue,
      obtain ⟨t, ht⟩ := hsub x (by rw [hw]; exact List.mem_cons_self)
      -- but the queue is empty. Impossible.
      rw [hq] at ht; simp at ht
  -- Case: a head h and a tail t.
  | cons h t =>
    -- The head is woken (no stranding), and nobody else.
    have hhw := hs.stranded h t hq hf
    -- Woken requests are distinct.
    have hn := hs.woken_nodup
    -- The first element of the queue is [h].
    simp only [List.take_succ_cons, List.take_zero]
    -- Every woken request is the head h:
    have hall : ∀ x ∈ s.woken, x = h := by
      -- Take a woken x.
      intro x hx
      -- It is the head of the queue.
      obtain ⟨t', ht'⟩ := hsub x hx
      -- The queue is h :: t.
      rw [hq] at ht'
      -- So x and h are the same.
      simp only [List.cons.injEq] at ht'
      -- Written the other way round.
      exact ht'.1.symm
    -- Split on the woken list.
    cases hw : s.woken with
    -- Empty: but h is woken. Impossible.
    | nil => rw [hw] at hhw; simp at hhw
    -- A first woken a and more, l.
    | cons a l =>
      -- a is h.
      have ha := hall a (by rw [hw]; exact List.mem_cons_self)
      -- Replace a by h.
      subst ha
      -- "Distinct" for h :: l says h is not in l, and l is distinct.
      rw [hw, List.nodup_cons] at hn
      -- Split on l.
      cases l with
      -- Empty: the woken list is [h], as claimed.
      | nil => rfl
      -- Another woken b:
      | cons b l' =>
        -- b is h too.
        have hb := hall b (by rw [hw]; simp)
        -- Replace b by h.
        subst hb
        -- Then h would be in l, against "distinct".
        exact absurd List.mem_cons_self hn.1

/-! ## Every step keeps the invariant -/

/-- The start satisfies the invariant. -/
theorem init_inv (B : Nat) : Inv B init :=
  -- The lock is free and nobody waits: the free shape.
  inv_free rfl rfl rfl rfl rfl (by simp [init]) (by simp [init]) List.nodup_nil
    -- (the remaining conditions of the free shape hold for the start state by computing)
    (by simp [init]) List.nodup_nil

/-- **Every step keeps the invariant**, for a bound of at least 1. -/
theorem step_inv {B : Nat}
    -- The bound is at least 1.
    (hB : 0 < B) {s t : M}
    -- The invariant holds before the step.
    (hs : Inv B s)
    -- One step of the design.
    (hstep : Step B s t) :
    -- The statement: the invariant holds after the step.
    Inv B t := by
  -- Split on the kind of step.
  cases hstep with
  -- Case: the fast path, for a fresh request r.
  | fast r hr hf ho =>
    -- The lock was free, so nobody held it; `r` takes it.
    obtain ⟨hown, hhand, -⟩ := hs.free_empty hf
    -- `r` is fresh, so in none of the lock's lists.
    have hfresh : ∀ x, x ∈ s.queue ∨ x ∈ s.owners ∨ x ∈ s.handed ∨ x ∈ s.woken → x ≠ r :=
      -- (if x were r, then r would have entered before; it is fresh)
      fun x hx e => hr (e ▸ hs.all_enq x hx)
    -- Thirteen facts. Unchanged ones are passed through; five are left to show.
    refine ⟨?_, hs.handed_owed, hs.woken_ok, hs.handed_woken, hs.bypass_le, hs.tail_zero,
      ?_, hs.owed_woken, ?_, ?_, hs.queue_nodup, ?_, hs.woken_nodup⟩
    -- One holder, `r`; the lock is no longer free.
    ·
      -- The owners are [r], nobody is handed, the lock is held: the count is 1.
      simp [hown, hhand]
    -- The lock is not free.
    ·
      -- "The lock is free" is false after the step: nothing to show.
      intro h t _ hfr; simp at hfr
    -- `r` is new to the entry list.
    ·
      -- "Distinct" for the old entries followed by [r] splits into three parts.
      rw [List.nodup_append]
      -- The old entries were distinct; [r] is; and no old entry equals r, which is left to show.
      refine ⟨hs.enq_nodup, by simp, ?_⟩
      -- Take an old entry a and a member b of [r] that are equal.
      intro a ha b hb hab
      -- b is r.
      simp only [List.mem_singleton] at hb
      -- So a is r.
      subst hb; subst hab
      -- But r had not entered.
      exact hr ha
    -- `r` entered now; everyone else as before.
    ·
      -- Take a request x in one of the lock's lists after the step.
      intro x hx
      -- To show: x was an old entry, or x is r.
      rw [List.mem_append, List.mem_singleton]
      -- "x is an owner" now means: x is r or an old owner.
      simp only [List.mem_cons] at hx
      -- Split on which list x is in.
      rcases hx with hx | (rfl | hx) | hx | hx
      -- It waits: it entered before.
      · exact Or.inl (hs.all_enq x (Or.inl hx))
      -- It is r: it enters now.
      · exact Or.inr rfl
      -- An old owner: it entered before.
      · exact Or.inl (hs.all_enq x (Or.inr (Or.inl hx)))
      -- Handed: it entered before.
      · exact Or.inl (hs.all_enq x (Or.inr (Or.inr (Or.inl hx))))
      -- Woken: it entered before.
      · exact Or.inl (hs.all_enq x (Or.inr (Or.inr (Or.inr hx))))
    -- A waiter is not `r`, and held nothing.
    ·
      -- Take a waiter x.
      intro x hx
      -- It was not handed the lock (as before); "x is not an owner" is left.
      refine ⟨?_, (hs.queue_fresh x hx).2⟩
      -- "x is an owner" now means: x is r or an old owner. Neither holds:
      simp only [List.mem_cons, not_or]
      -- x is not r (r is fresh), and x was no owner.
      exact ⟨hfresh x (Or.inl hx), (hs.queue_fresh x hx).1⟩
  -- Case: a fresh request r joins the queue.
  | enqueue r hr hc =>
    -- The lock is held: a handoff owed means someone holds it.
    have hfree : s.free = false := by
      -- Split on why the fast path was shut.
      rcases hc with h | h
      -- The lock is held: that is the claim.
      · exact h
      -- A handoff is owed: split on whether the lock is free.
      · cases hf : s.free
        -- Not free: that is the claim.
        · rfl
        -- Free: then nothing would be owed. A contradiction.
        · exfalso; exact h (hs.free_empty hf).2.2
    -- `r` is fresh, so in none of the lock's lists.
    have hfresh : ∀ x, x ∈ s.queue ∨ x ∈ s.owners ∨ x ∈ s.handed ∨ x ∈ s.woken → x ≠ r :=
      -- (if x were r, then r would have entered before; it is fresh)
      fun x hx e => hr (e ▸ hs.all_enq x hx)
    -- `upd` leaves every request but `r` alone.
    have hupd : ∀ x, x ≠ r → upd s.bypass r 0 x = s.bypass x := by
      -- Take a request other than r: the update is at r, so its count is untouched.
      intro x hx; simp [upd, hx]
    -- Thirteen facts. Unchanged ones are passed through; eight are left to show.
    refine ⟨hs.excl, hs.handed_owed, ?_, hs.handed_woken, ?_, ?_, ?_, hs.owed_woken, ?_, ?_, ?_,
      ?_, hs.woken_nodup⟩
    -- A woken waiter was the head of a non-empty queue; it still is.
    ·
      -- Take a woken request x.
      intro x hx
      -- It was handed the lock, or it is the head below the bound.
      rcases hs.woken_ok x hx with h | ⟨t, hq, hb⟩
      -- Handed: as before.
      · exact Or.inl h
      -- The head: the queue is now x, its old tail, and r at the end; its count is left to check.
      · refine Or.inr ⟨t ++ [r], by simp [hq], ?_⟩
        -- x is not r, so its count is unchanged,
        dsimp only; rw [hupd x (hfresh x (Or.inr (Or.inr (Or.inr hx))))]
        -- and was below the bound.
        exact hb
    -- `r` has count 0; the others as before.
    ·
      -- Take a waiter x after the step.
      intro x hx
      -- It is an old waiter, or r.
      rw [List.mem_append, List.mem_singleton] at hx
      -- Split on which.
      rcases hx with hx | rfl
      -- An old waiter: not r, so its count is unchanged and was within the bound.
      · dsimp only; rw [hupd x (hfresh x (Or.inl hx))]; exact hs.bypass_le x hx
      -- r: its count is 0.
      · simp [upd]
    -- Behind the head: the old tail and `r`, all at 0.
    ·
      -- Take the new queue's head h, its tail t, and a request x in the tail.
      intro h t hq x hx
      -- Split on the old queue.
      cases hq0 : s.queue with
      -- Case: it was empty.
      | nil =>
        -- `r` alone: no tail.
        -- Then the new queue is [r], whose tail is empty: there is no x.
        rw [hq0] at hq; simp at hq; obtain ⟨-, rfl⟩ := hq; simp at hx
      -- Case: it had a head h' and a tail t'.
      | cons h' t' =>
        -- The new queue is h' :: (t' ++ [r]).
        rw [hq0] at hq
        -- Compare with h :: t, piece by piece.
        simp only [List.cons_append, List.cons.injEq] at hq
        -- So h is h', and t is t' with r at the end.
        obtain ⟨rfl, rfl⟩ := hq
        -- x is in t', or x is r.
        rw [List.mem_append, List.mem_singleton] at hx
        -- Split on which.
        rcases hx with hx | rfl
        -- In the old tail: x is not r, so its count is unchanged,
        · dsimp only; rw [hupd x (hfresh x (Or.inl (by rw [hq0]; exact List.mem_cons_of_mem _ hx)))]
          -- and it was 0.
          exact hs.tail_zero _ t' hq0 x hx
        -- r: its count is 0.
        · simp [upd]
    -- The lock is held.
    ·
      -- "The lock is free" contradicts "the lock is held": nothing to show.
      intro h t _ hf; rw [hfree] at hf; simp at hf
    -- `r` is new to the entry list.
    ·
      -- "Distinct" for the old entries followed by [r] splits into three parts.
      rw [List.nodup_append]
      -- The old entries were distinct; [r] is; and no old entry equals r, which is left to show.
      refine ⟨hs.enq_nodup, by simp, ?_⟩
      -- Take an old entry a and a member b of [r] that are equal.
      intro a ha b hb hab
      -- b is r.
      simp only [List.mem_singleton] at hb
      -- So a is r.
      subst hb; subst hab
      -- But r had not entered.
      exact hr ha
    -- `r` entered now; everyone else as before.
    ·
      -- Take a request x in one of the lock's lists after the step.
      intro x hx
      -- To show: x was an old entry, or x is r.
      rw [List.mem_append, List.mem_singleton]
      -- "x waits" now means: x is an old waiter or r.
      rw [List.mem_append, List.mem_singleton] at hx
      -- Split on which list x is in.
      rcases hx with (hx | rfl) | hx | hx | hx
      -- An old waiter: it entered before.
      · exact Or.inl (hs.all_enq x (Or.inl hx))
      -- It is r: it enters now.
      · exact Or.inr rfl
      -- An owner: it entered before.
      · exact Or.inl (hs.all_enq x (Or.inr (Or.inl hx)))
      -- Handed: it entered before.
      · exact Or.inl (hs.all_enq x (Or.inr (Or.inr (Or.inl hx))))
      -- Woken: it entered before.
      · exact Or.inl (hs.all_enq x (Or.inr (Or.inr (Or.inr hx))))
    -- `r` is new to the queue.
    ·
      -- "Distinct" for the old queue followed by [r] splits into three parts.
      rw [List.nodup_append]
      -- The old queue was distinct; [r] is; and no old waiter equals r, which is left to show.
      refine ⟨hs.queue_nodup, by simp, ?_⟩
      -- Take an old waiter a and a member b of [r] that are equal.
      intro a ha b hb hab
      -- b is r.
      simp only [List.mem_singleton] at hb
      -- So a is r.
      subst hb; subst hab
      -- But r is fresh, so it is no old waiter.
      exact hfresh a (Or.inl ha) rfl
    -- `r` holds nothing; the others as before.
    ·
      -- Take a waiter x after the step.
      intro x hx
      -- It is an old waiter, or r.
      rw [List.mem_append, List.mem_singleton] at hx
      -- Split on which.
      rcases hx with hx | rfl
      -- An old waiter: it held nothing before.
      · exact hs.queue_fresh x hx
      -- r: it is fresh, so it is no owner,
      · exact ⟨fun h => hfresh x (Or.inr (Or.inl h)) rfl,
          -- and it was not handed the lock.
          fun h => hfresh x (Or.inr (Or.inr (Or.inl h))) rfl⟩
  -- Case: an owner r drops its guard.
  | release r hr =>
    -- `r` held the lock alone.
    obtain ⟨hown, hhand, hfree, howed⟩ := hs.owner_alone hr
    -- Nobody is woken unless it is the head with a count below the bound.
    have hwk : ∀ x ∈ s.woken, ∃ t, s.queue = x :: t ∧ s.bypass x < B := by
      -- Take a woken request x.
      intro x hx
      -- It was handed the lock, or it is the head below the bound.
      rcases hs.woken_ok x hx with h | h
      -- Handed: nobody was. Impossible.
      · rw [hhand] at h; simp at h
      -- The head below the bound: that is the claim.
      · exact h
    -- The queue has no request twice.
    have hqn := hs.queue_nodup
    -- Every waiter entered.
    have hallq : ∀ x ∈ s.queue, x ∈ s.enq := fun x hx => hs.all_enq x (Or.inl hx)
    -- Unfold the release rule.
    unfold relFrom
    -- The owners were [r]; without r there is none.
    simp only [hown, List.erase_cons_head]
    -- Split on the queue.
    cases hq : s.queue with
    -- Case: nobody waits.
    | nil =>
      -- Nobody waits: the lock is free, and nobody is woken.
      have hwe : s.woken = [] := by
        -- Split on the woken list.
        cases hw : s.woken with
        -- Empty: that is the claim.
        | nil => rfl
        -- Somebody woken, x:
        | cons x l =>
          -- then x would be the head of the queue,
          obtain ⟨t, ht, -⟩ := hwk x (by rw [hw]; exact List.mem_cons_self)
          -- but the queue is empty. Impossible.
          rw [hq] at ht; simp at ht
      -- The free shape, with an empty queue: every condition is immediate.
      exact inv_free rfl howed rfl hhand (by simp [hwe]) (by simp) (by simp) hs.enq_nodup
        -- (the last two: no waiter to have entered, and an empty queue is distinct)
        (by simp) (by simp)
    -- Case: a head h and a tail t.
    | cons h t =>
      -- State "distinct" and "entered" for h :: t.
      rw [hq] at hqn hallq
      -- Split on whether the head has lost fewer than B races.
      by_cases hb : s.bypass h < B
      -- Below the bound: free, and wake the head. Either way exactly the head ends up woken: a
      -- woken request before was the head.
      ·
        -- Take the "below the bound" branch of the release rule.
        simp only [hb, ite_true]
        -- Every woken request is the head h:
        have hsub : ∀ x ∈ s.woken, x = h := by
          -- Take a woken x.
          intro x hx
          -- It is the head of the queue.
          obtain ⟨t', ht', -⟩ := hwk x hx
          -- The queue is h :: t, so x is h.
          rw [hq] at ht'; simp only [List.cons.injEq] at ht'; exact ht'.1.symm
        -- The head is below the bound; those behind it at 0; all entered.
        have hhead : ∀ h' t', h :: t = h' :: t' → s.bypass h' < B := by
          -- The head of h :: t is h, whose count is below B.
          intro h' t' e; simp only [List.cons.injEq] at e; obtain ⟨e1, -⟩ := e; rw [← e1]; exact hb
        -- Those behind the head have a count of 0:
        have htail : ∀ h' t', h :: t = h' :: t' → ∀ x ∈ t', s.bypass x = 0 := by
          -- A request behind the head of h :: t is in t,
          intro h' t' e x hx; simp only [List.cons.injEq] at e; obtain ⟨-, e2⟩ := e
          -- and those have a count of 0.
          rw [← e2] at hx; exact hs.tail_zero h t hq x hx
        -- Unfold "wake the head".
        unfold wakeHead
        -- Simplify the fields after freeing the lock.
        simp only
        -- Split on whether h was already woken.
        by_cases hhw : h ∈ s.woken
        -- Already woken: `s.woken` is exactly `[h]`.
        ·
          -- Take the "already woken" branch: the woken list is unchanged.
          simp only [hhw, ite_true]
          -- The woken list is exactly [h]:
          have hw1 : s.woken = [h] := by
            -- Split on the woken list.
            cases hw : s.woken with
            -- Empty: but h is woken. Impossible.
            | nil => rw [hw] at hhw; simp at hhw
            -- A first woken a and more, l.
            | cons a l =>
              -- a is h.
              have ha := hsub a (by rw [hw]; exact List.mem_cons_self)
              -- Write the list as h :: l.
              rw [ha] at hw
              -- Woken requests are distinct.
              have hnd := hs.woken_nodup
              -- So h is not in l.
              rw [hw, List.nodup_cons] at hnd
              -- Split on l.
              cases l with
              -- Empty: the list is [h].
              | nil => rw [ha]
              -- Another woken b:
              | cons b l' =>
                -- b is h too,
                have hb' := hsub b (by rw [hw]; simp)
                -- so h would be in l.
                rw [hb'] at hnd
                -- Against "distinct".
                exact absurd List.mem_cons_self hnd.1
          -- The free shape: exactly the head is woken.
          exact inv_free rfl howed rfl hhand (by simp [hw1]) hhead htail hs.enq_nodup hallq hqn
        -- Not woken: `s.woken` is empty, and `h` is woken now.
        ·
          -- Take the "not yet woken" branch: h joins the woken list.
          simp only [hhw, ite_false]
          -- Nobody was woken:
          have hw0 : s.woken = [] := by
            -- Split on the woken list.
            cases hw : s.woken with
            -- Empty: that is the claim.
            | nil => rfl
            -- Somebody woken, a:
            | cons a l =>
              -- a is h,
              have ha := hsub a (by rw [hw]; exact List.mem_cons_self)
              -- so h would be woken. It is not.
              exact absurd (by rw [hw, ha]; exact List.mem_cons_self) hhw
          -- The free shape: the woken list is now [h], the head.
          exact inv_free rfl howed rfl hhand (by simp [hw0]) hhead htail hs.enq_nodup hallq hqn
      -- At the bound: hand off to the head.
      ·
        -- Take the "at the bound" branch of the release rule.
        simp only [hb, ite_false]
        -- Nobody was woken: a woken request would be the head below the bound.
        have hwe : s.woken = [] := by
          -- Split on the woken list.
          cases hw : s.woken with
          -- Empty: that is the claim.
          | nil => rfl
          -- Somebody woken, x:
          | cons x l =>
            -- x is the head, with a count below B.
            obtain ⟨t', ht, hbx⟩ := hwk x (by rw [hw]; exact List.mem_cons_self)
            -- The queue is h :: t,
            rw [hq] at ht
            -- so x is h,
            simp only [List.cons.injEq] at ht
            -- replace x by h,
            obtain ⟨rfl, -⟩ := ht
            -- and h's count would be below B. It is not.
            exact absurd hbx hb
        -- "Distinct" for h :: t: h is not in t, and t is distinct.
        rw [List.nodup_cons] at hqn
        -- The handoff shape: the lock held by handoff to h, h alone woken,
        exact inv_handoff hfree rfl rfl (by simp [hhand]) (by simp [hwe])
          -- the waiters left at 0, h not among them, entries distinct,
          (fun x hx => hs.tail_zero h t hq x hx) hqn.1 hs.enq_nodup
          -- every waiter and h entered, and the queue distinct.
          (fun x hx => hallq x (List.mem_cons_of_mem _ hx)) (hallq h List.mem_cons_self) hqn.2
  -- Case: a woken request h that was handed the lock takes it.
  | pollHanded h hw hh =>
    -- The lock was handed to `h` alone, and only `h` is woken.
    have hho : s.owed = some h := by
      -- The "handed" list is the owed request, if any.
      have := hs.handed_owed
      -- h is in that list.
      rw [this] at hh
      -- Split on the owed bit.
      cases ho : s.owed with
      -- None owed: then nobody is handed. Impossible.
      | none => rw [ho] at hh; simp at hh
      -- Owed to w: then h is w.
      | some w => rw [ho] at hh; simp at hh; rw [hh]
    -- So h alone was handed the lock, there is no owner, and the lock is held.
    obtain ⟨hhand, hown, hfree⟩ := hs.owed_alone hho
    -- The woken list is exactly [h]:
    have hwk : s.woken = [h] := by
      -- Every woken request is h:
      have hsub : ∀ x ∈ s.woken, x = h := by
        -- take a woken x;
        intro x hx
        -- while a handoff is owed, a woken request is a handed one;
        have := hs.owed_woken (by simp [hho]) x hx
        -- and the only handed one is h.
        rw [hhand] at this; simpa using this
      -- Split on the woken list.
      cases hw' : s.woken with
      -- Empty: but h is woken. Impossible.
      | nil => rw [hw'] at hw; simp at hw
      -- A first woken a and more, l.
      | cons a l =>
        -- a is h.
        have ha := hsub a (by rw [hw']; exact List.mem_cons_self)
        -- Replace a by h.
        subst ha
        -- Woken requests are distinct.
        have hn := hs.woken_nodup
        -- So h is not in l.
        rw [hw', List.nodup_cons] at hn
        -- Split on l.
        cases l with
        -- Empty: the list is [h].
        | nil => rfl
        -- Another woken b:
        | cons b l' =>
          -- b is h too.
          have hb := hsub b (by rw [hw']; simp)
          -- Replace b by h.
          subst hb
          -- Then h would be in l, against "distinct".
          exact absurd List.mem_cons_self hn.1
    -- Thirteen facts. Settled at once: one holder (the new owner h); nothing handed and nothing
    -- owed; nobody handed needs waking; the counts and tail counts (unchanged);
    refine ⟨by simp [hown, hhand, hfree], by simp [hhand], ?_, by simp [hhand], hs.bypass_le,
      -- the lock is not free; nothing is owed; entries and the queue are distinct (unchanged);
      hs.tail_zero, by simp [hfree], by simp, hs.enq_nodup, ?_, hs.queue_nodup, ?_,
      -- and nobody is woken any more. Three are left.
      by simp [hwk]⟩
    -- A woken request: there is none after the step.
    · intro x hx; simp [hwk] at hx
    -- The new owner `h` was handed the lock; the rest shrank.
    ·
      -- Take a request x in one of the lock's lists after the step.
      intro x hx
      -- It is enough that x was in one of them before.
      apply hs.all_enq x
      -- Split on which list x is in now.
      rcases hx with hx | hx | hx | hx
      -- It waits: it waited before.
      · exact Or.inl hx
      -- It owns: it is h, or an old owner.
      · rcases List.mem_cons.1 hx with e | hx
        -- h: it was handed the lock before.
        · exact Or.inr (Or.inr (Or.inl (e ▸ hh)))
        -- An old owner: an owner before.
        · exact Or.inr (Or.inl hx)
      -- Handed now: handed before.
      · exact Or.inr (Or.inr (Or.inl (List.mem_of_mem_erase hx)))
      -- Woken now: woken before.
      · exact Or.inr (Or.inr (Or.inr (List.mem_of_mem_erase hx)))
    -- A waiter holds nothing: take a waiter x.
    · intro x hx
      -- Nobody is handed any more; "x is not an owner" is left.
      refine ⟨?_, by simp [hhand]⟩
      -- The owners are now [h], so "x is an owner" means "x is h".
      simp only [hown, List.mem_cons, List.not_mem_nil, or_false]
      -- Suppose x is h.
      intro e; subst e
      -- Then a waiter was handed the lock before, which the invariant forbids.
      exact (hs.queue_fresh x hx).2 (by rw [hhand]; exact List.mem_cons_self)
  -- Case: a woken request h wins the race.
  | pollWin h hw hh hf ho =>
    -- The lock was free: nobody held it. `h` is the head.
    obtain ⟨hown, hhand, -⟩ := hs.free_empty hf
    -- h is the head of the queue: the queue is h :: t.
    obtain ⟨t, hq, -⟩ := hs.woken_head hw hh
    -- The queue has no request twice.
    have hqn := hs.queue_nodup
    -- So h is not in t, and t is distinct.
    rw [hq, List.nodup_cons] at hqn
    -- Only `h` was woken (the free shape), so nobody is woken after.
    have hwk : s.woken = [h] := by rw [hs.free_woken hf, hq]; simp
    -- The head leaves the queue, and its woken bit with it.
    have hqe : s.queue.erase h = t := by rw [hq, List.erase_cons_head]
    -- And with h removed nobody is woken.
    have hwe : s.woken.erase h = [] := by rw [hwk, List.erase_cons_head]
    -- Use those two in the goal: the new queue is t, and nobody is woken.
    simp only [hqe, hwe]
    -- Thirteen facts. Settled at once: one holder (h); nothing handed, nothing owed; nobody woken;
    -- nobody handed;
    refine ⟨by simp [hown, hhand], by simp [hhand, ho], by simp, by simp [hhand], ?_, ?_,
      -- the lock is not free; nothing owed; entries distinct; the new queue t distinct; nobody
      -- woken. Four are left.
      by simp, by simp [ho], hs.enq_nodup, ?_, hqn.2, ?_, by simp⟩
    -- The counts: a waiter of t waited before, so its count is within the bound.
    · intro x hx; exact hs.bypass_le x (by rw [hq]; exact List.mem_cons_of_mem _ hx)
    -- The tail counts: take the new queue's head h', its tail t', and a request x in t'.
    · intro h' t' ht' x hx
      -- The new queue is `t`, the old tail.
      -- (the new queue t is h' :: t')
      have ht2 : t = h' :: t' := ht'
      -- x was behind the old head h, so its count is 0.
      exact hs.tail_zero h t hq x (by rw [ht2]; exact List.mem_cons_of_mem _ hx)
    -- The new owner `h` waited; the rest is drawn from before.
    ·
      -- Take a request x in one of the lock's lists after the step.
      intro x hx
      -- It is enough that x was in one of them before.
      apply hs.all_enq x
      -- Split on which list x is in now.
      rcases hx with hx | hx | hx | hx
      -- It waits (in t): it waited before.
      · exact Or.inl (by rw [hq]; exact List.mem_cons_of_mem _ hx)
      -- It owns: it is h, or an old owner.
      · rcases List.mem_cons.1 hx with e | hx
        -- h: it waited before, as the head.
        · exact Or.inl (by rw [hq, e]; exact List.mem_cons_self)
        -- An old owner: an owner before.
        · exact Or.inr (Or.inl hx)
      -- Handed: handed before.
      · exact Or.inr (Or.inr (Or.inl hx))
      -- Woken: nobody is. Impossible.
      · simp at hx
    -- A waiter holds nothing: take a waiter x (in t).
    · intro x hx
      -- Nobody is handed; "x is not an owner" is left.
      refine ⟨?_, by simp [hhand]⟩
      -- The owners are now [h], so "x is an owner" means "x is h".
      simp only [hown, List.mem_cons, List.not_mem_nil, or_false]
      -- Suppose x is h: then h would be in t. It is not.
      intro e; subst e; exact hqn.1 hx
  -- Case: a woken request h loses the race.
  | pollLose h hw hh hc =>
    -- `h` is the head, with a count below the bound.
    obtain ⟨t, hq, hb⟩ := hs.woken_head hw hh
    -- The queue has no request twice.
    have hqn := hs.queue_nodup
    -- So h is not in t, and t is distinct.
    rw [hq, List.nodup_cons] at hqn
    -- The lock is held: a handoff owed means someone holds it.
    have hfree : s.free = false := by
      -- Split on why the fast path was shut.
      rcases hc with h' | h'
      -- The lock is held: that is the claim.
      · exact h'
      -- A handoff is owed: split on whether the lock is free.
      · cases hf : s.free
        -- Not free: that is the claim.
        · rfl
        -- Free: then nothing would be owed. A contradiction.
        · exfalso; exact h' (hs.free_empty hf).2.2
    -- `upd` leaves every request but `h` alone.
    have hupd : ∀ x, x ≠ h → upd s.bypass h (s.bypass h + 1) x = s.bypass x := by
      -- Take a request other than h: the update is at h, so its count is untouched.
      intro x hx; simp [upd, hx]
    -- Thirteen facts. Unchanged ones are passed through; six are left,
    refine ⟨hs.excl, hs.handed_owed, ?_, ?_, ?_, ?_, ?_, ?_, hs.enq_nodup, ?_, hs.queue_nodup,
      -- and the woken list stays distinct with h removed.
      hs.queue_fresh, hs.woken_nodup.erase h⟩
    -- The others woken are as before (not `h`, which is no longer woken).
    ·
      -- Take a request x woken after the step.
      intro x hx
      -- It was woken before, and it is not h.
      have hx' := (List.Nodup.mem_erase_iff hs.woken_nodup).1 hx
      -- It was handed the lock, or it was the head.
      rcases hs.woken_ok x hx'.2 with h' | ⟨t', ht', -⟩
      -- Handed: as before.
      · exact Or.inl h'
      -- The head: the queue is h :: t, so x would be h.
      · rw [hq] at ht'; simp only [List.cons.injEq] at ht'
        -- But x is not h.
        exact absurd ht'.1.symm hx'.1
    -- `h` holds nothing, so it is not among those handed the lock.
    ·
      -- Take a handed request x.
      intro x hx
      -- x is not h, since h was not handed.
      have hxh : x ≠ h := fun e => hh (e ▸ hx)
      -- x was woken before, and is not h: it is still woken.
      exact (List.mem_erase_of_ne hxh).2 (hs.handed_woken x hx)
    -- `h`'s count was below the bound, so one more is within it.
    ·
      -- Take a waiter x.
      intro x hx
      -- Split on whether x is h.
      by_cases hxh : x = h
      -- It is h: its new count is the old one plus 1, and the old one was below B.
      · subst hxh; simp only [upd, ite_true]; omega
      -- It is not: its count is unchanged, and was within the bound.
      · dsimp only; rw [hupd x hxh]; exact hs.bypass_le x hx
    -- Those behind `h` are not `h`.
    ·
      -- Take the queue's head h', its tail t', and a request x in t'.
      intro h' t' ht' x hx
      -- The queue is h :: t.
      rw [hq] at ht'
      -- Compare the two shapes.
      simp only [List.cons.injEq] at ht'
      -- So t' is t.
      obtain ⟨-, e2⟩ := ht'
      -- x is in t.
      rw [← e2] at hx
      -- x is not h, since h is not in t.
      have hxh : x ≠ h := fun e => hqn.1 (e ▸ hx)
      -- So x's count is unchanged,
      dsimp only; rw [hupd x hxh]
      -- and it was 0.
      exact hs.tail_zero h t hq x hx
    -- The lock is held.
    ·
      -- "The lock is free" contradicts "the lock is held": nothing to show.
      intro h' t' _ hf; rw [hfree] at hf; simp at hf
    -- Fewer woken.
    ·
      -- Suppose a handoff is owed, and take a request x woken after the step.
      intro ho x hx
      -- It was woken before, so it was handed the lock.
      exact hs.owed_woken ho x (List.mem_of_mem_erase hx)
    -- Every request named entered: take one, x.
    · intro x hx
      -- Split on which list x is in.
      rcases hx with hx | hx | hx | hx
      -- It waits: as before.
      · exact hs.all_enq x (Or.inl hx)
      -- It owns: as before.
      · exact hs.all_enq x (Or.inr (Or.inl hx))
      -- Handed: as before.
      · exact hs.all_enq x (Or.inr (Or.inr (Or.inl hx)))
      -- Woken now: woken before.
      · exact hs.all_enq x (Or.inr (Or.inr (Or.inr (List.mem_of_mem_erase hx))))
  -- Case: a waiting request r is dropped.
  | cancelWaiting r hr =>
    -- The queue has no request twice.
    have hqn0 := hs.queue_nodup
    -- `r` holds nothing.
    have hrh : r ∉ s.handed := (hs.queue_fresh r hr).2
    -- The state with `r` gone, before any wake is passed on.
    generalize hX : ({ s with queue := s.queue.erase r, woken := s.woken.erase r } : M) = X
    -- Its fields.
    -- The lock is free in X exactly as in s.
    have hXf : X.free = s.free := by rw [← hX]
    -- The owed bit is the same.
    have hXo : X.owed = s.owed := by rw [← hX]
    -- The queue is the old one without r.
    have hXq : X.queue = s.queue.erase r := by rw [← hX]
    -- The woken list is the old one without r.
    have hXw : X.woken = s.woken.erase r := by rw [← hX]
    -- The owners are the same.
    have hXown : X.owners = s.owners := by rw [← hX]
    -- The handed list is the same.
    have hXh : X.handed = s.handed := by rw [← hX]
    -- The counts are the same.
    have hXb : X.bypass = s.bypass := by rw [← hX]
    -- The entries are the same.
    have hXe : X.enq = s.enq := by rw [← hX]
    -- The queue's head, before.
    obtain ⟨h0, t0, hq⟩ : ∃ h0 t0, s.queue = h0 :: t0 := by
      -- Split on the old queue.
      cases hq : s.queue with
      -- Empty: but r waits. Impossible.
      | nil => rw [hq] at hr; simp at hr
      -- A head h0 and a tail t0: these are the witnesses.
      | cons h0 t0 => exact ⟨h0, t0, rfl⟩
    -- Keep a copy of "the queue is distinct".
    have hqn := hqn0
    -- For h0 :: t0: h0 is not in t0, and t0 is distinct.
    rw [hq, List.nodup_cons] at hqn
    -- Every waiter of h0 :: t0 entered.
    have hall : ∀ x ∈ h0 :: t0, x ∈ s.enq := fun x hx => hs.all_enq x (Or.inl (hq ▸ hx))
    -- Split on whether the lock is free.
    by_cases hf : s.free = true
    -- The lock is free: nobody holds it, and exactly the head is woken.
    ·
      -- No owner, nobody handed, nothing owed.
      obtain ⟨hown, hhand, howed⟩ := hs.free_empty hf
      -- The woken list is the first element of the queue.
      have hwk := hs.free_woken hf
      -- The queue is h0 :: t0.
      rw [hq] at hwk
      -- So the woken list is [h0].
      simp only [List.take_succ_cons, List.take_zero] at hwk
      -- With the lock free and nothing owed, "wake if free" is "wake the head".
      rw [wakeIfFree_free (by rw [hXf, hf]) (by rw [hXo, howed])]
      -- Waking the head changes no field but the woken list: name the seven equalities.
      obtain ⟨wf, wo, wq, wown, wh, wb, we⟩ := wakeHead_fields X
      -- Split on whether the request that left is the head.
      by_cases hrh0 : r = h0
      -- The head left: the next waiter (count 0) is the new head, woken.
      ·
        -- The queue of X is the old tail t0.
        have hXq' : X.queue = t0 := by rw [hXq, hq, hrh0, List.erase_cons_head]
        -- Nobody is woken in X: the only woken one, the head, left.
        have hXw' : X.woken = [] := by rw [hXw, hwk, hrh0, List.erase_cons_head]
        -- Split on the old tail.
        cases ht0 : t0 with
        -- Case: it was empty.
        | nil =>
          -- Nobody is left to wake.
          -- Waking the head of an empty queue changes nothing.
          rw [wakeHead_nil (by rw [hXq', ht0])]
          -- The free shape with an empty queue: the lock is free, nothing owed, no owner,
          exact inv_free (by rw [hXf, hf]) (by rw [hXo, howed]) (by rw [hXown, hown])
            -- nobody handed, nobody woken, no head to bound,
            (by rw [hXh, hhand]) (by rw [hXw', hXq', ht0]; rfl) (by rw [hXq', ht0]; simp)
            -- no tail, entries distinct, no waiter to have entered,
            (by rw [hXq', ht0]; simp) (by rw [hXe]; exact hs.enq_nodup) (by rw [hXq', ht0]; simp)
            -- and an empty queue is distinct.
            (by rw [hXq', ht0]; simp)
        -- Case: the tail was h1 :: t1.
        | cons h1 t1 =>
          -- The next waiter becomes the head and is woken.
          -- The queue of X is h1 :: t1.
          have hXq'' : X.queue = h1 :: t1 := by rw [hXq', ht0]
          -- State "distinct" and "entered" for h0 :: h1 :: t1.
          rw [ht0] at hqn hall
          -- Waking the head adds h1 to the woken list unless it is there already.
          have hw1 := wakeHead_woken hXq''
          -- The woken list of X was empty, so afterwards it is [h1].
          rw [hXw'] at hw1
          -- The free shape, for the state after waking: free, nothing owed, no owner,
          apply inv_free (by rw [wf, hXf, hf]) (by rw [wo, hXo, howed]) (by rw [wown, hXown, hown])
            -- nobody handed; six conditions are left.
            (by rw [wh, hXh, hhand])
          -- Exactly the head is woken: the woken list is [h1] and the queue starts with h1.
          · rw [hw1, wq, hXq'']; simp
          -- The head is below the bound: take the head h' of the queue.
          · intro h' t' e
            -- The queue is h1 :: t1.
            rw [wq, hXq''] at e
            -- Compare the two shapes.
            simp only [List.cons.injEq] at e
            -- So h' is h1.
            obtain ⟨e1, -⟩ := e
            -- h1 was behind the old head, so its count is 0,
            rw [wb, hXb, ← e1, hs.tail_zero h0 t0 hq h1 (by rw [ht0]; exact List.mem_cons_self)]
            -- and 0 is below B because B is at least 1.
            exact hB
          -- Those behind the head are at 0: take a request x behind the new head.
          · intro h' t' e x hx
            -- The queue is h1 :: t1.
            rw [wq, hXq''] at e
            -- Compare the two shapes.
            simp only [List.cons.injEq] at e
            -- So the tail is t1.
            obtain ⟨-, e2⟩ := e
            -- x is in t1.
            rw [← e2] at hx
            -- The counts are the old ones.
            rw [wb, hXb]
            -- x was behind the old head h0, so its count is 0.
            exact hs.tail_zero h0 t0 hq x (by rw [ht0]; exact List.mem_cons_of_mem _ hx)
          -- The entries are the old ones, which are distinct.
          · rw [we, hXe]; exact hs.enq_nodup
          -- Every waiter entered: take a waiter x of h1 :: t1.
          · intro x hx; rw [wq, hXq''] at hx; rw [we, hXe]
            -- It was a waiter before.
            exact hall x (List.mem_cons_of_mem _ hx)
          -- The queue h1 :: t1 is distinct.
          · rw [wq, hXq'']; exact hqn.2
      -- A waiter behind the head left: the head stays, still woken.
      ·
        -- h0 is not r.
        have hne : (h0 == r) = false := by simp; exact fun e => hrh0 e.symm
        -- The queue of X is h0 followed by the old tail without r:
        have hXq' : X.queue = h0 :: t0.erase r := by
          -- erasing r from h0 :: t0 skips the head, which is not r.
          rw [hXq, hq]; exact List.erase_cons_tail (by simpa using hne)
        -- The woken list of X is still [h0]:
        have hXw' : X.woken = [h0] := by
          -- erasing r from [h0] removes nothing, since r is not h0.
          rw [hXw, hwk]; exact List.erase_of_not_mem (by simp; exact fun e => hrh0 e)
        -- Waking the head adds h0 to the woken list unless it is there already.
        have hw1 := wakeHead_woken hXq'
        -- The woken list of X is [h0],
        rw [hXw'] at hw1
        -- so h0 is there already and the list stays [h0].
        simp only [List.mem_singleton, ite_true] at hw1
        -- The free shape, for the state after waking: free, nothing owed, no owner,
        apply inv_free (by rw [wf, hXf, hf]) (by rw [wo, hXo, howed]) (by rw [wown, hXown, hown])
          -- nobody handed; six conditions are left.
          (by rw [wh, hXh, hhand])
        -- Exactly the head is woken: the woken list is [h0] and the queue starts with h0.
        · rw [hw1, wq, hXq']; simp
        -- The head is below the bound: take the head h' of the queue.
        · intro h' t' e
          -- The queue is h0 :: (t0 without r).
          rw [wq, hXq'] at e
          -- Compare the two shapes.
          simp only [List.cons.injEq] at e
          -- So h' is h0.
          obtain ⟨e1, -⟩ := e
          -- The counts are the old ones.
          rw [wb, hXb, ← e1]
          -- h0 was woken and not handed, so it was the head with a count below B.
          obtain ⟨-, -, hb⟩ := hs.woken_head (h := h0) (by rw [hwk]; simp) (by rw [hhand]; simp)
          -- That is the claim.
          exact hb
        -- Those behind the head are at 0: take a request x behind the head.
        · intro h' t' e x hx
          -- The queue is h0 :: (t0 without r).
          rw [wq, hXq'] at e
          -- Compare the two shapes.
          simp only [List.cons.injEq] at e
          -- So the tail is t0 without r.
          obtain ⟨-, e2⟩ := e
          -- x is in it.
          rw [← e2] at hx
          -- The counts are the old ones.
          rw [wb, hXb]
          -- x was in the old tail, so its count is 0.
          exact hs.tail_zero h0 t0 hq x (List.mem_of_mem_erase hx)
        -- The entries are the old ones, which are distinct.
        · rw [we, hXe]; exact hs.enq_nodup
        -- Every waiter entered: take a waiter x.
        · intro x hx
          -- It is in h0 :: (t0 without r).
          rw [wq, hXq'] at hx
          -- The entries are the old ones.
          rw [we, hXe]
          -- x is h0, or in the old tail without r.
          rcases List.mem_cons.1 hx with e | hx
          -- h0: it was a waiter before.
          · rw [e]; exact hall h0 List.mem_cons_self
          -- In the tail: it was a waiter before.
          · exact hall x (List.mem_cons_of_mem _ (List.mem_of_mem_erase hx))
        -- The queue is distinct: for h0 :: (t0 without r),
        · rw [wq, hXq', List.nodup_cons]
          -- h0 is not in the tail, and the tail without r is distinct.
          exact ⟨fun hm => hqn.1 (List.mem_of_mem_erase hm), hqn.2.erase r⟩
    -- The lock is held: no wake is passed on; `r` simply leaves.
    ·
      -- "Not free" as an equation: split on the flag; one case contradicts the assumption.
      have hf' : s.free = false := by cases h' : s.free <;> simp_all
      -- With the lock held, "wake if free" changes nothing.
      rw [wakeIfFree_held (by rw [hXf, hf'])]
      -- Thirteen facts. Settled at once: the holders and the free flag are unchanged; so are the
      -- handed list and the owed bit;
      refine ⟨by rw [hXown, hXh, hXf]; exact hs.excl, by rw [hXh, hXo]; exact hs.handed_owed,
        -- the entries are unchanged and distinct;
        ?_, ?_, ?_, ?_, ?_, ?_, by rw [hXe]; exact hs.enq_nodup, ?_,
        -- the queue without r is distinct; the woken list without r is distinct. Eight are left.
        by rw [hXq]; exact hqn0.erase r, ?_, by rw [hXw]; exact hs.woken_nodup.erase r⟩
      -- A woken request still holds by handoff, or is still the head.
      ·
        -- Take a request x woken in X.
        intro x hx
        -- It is in the old woken list without r.
        rw [hXw] at hx
        -- State the goal with the old fields.
        rw [hXh, hXq, hXb]
        -- So x was woken before, and x is not r.
        have hx' := (List.Nodup.mem_erase_iff hs.woken_nodup).1 hx
        -- x was handed the lock, or was the head below the bound.
        rcases hs.woken_ok x hx'.2 with h' | ⟨t', ht', hbx⟩
        -- Handed: as before.
        · exact Or.inl h'
        -- The head: the queue without r still starts with x; that equation is left.
        · refine Or.inr ⟨t'.erase r, ?_, hbx⟩
          -- The old queue is x :: t'.
          rw [ht']
          -- Erasing r skips the head x, which is not r.
          exact List.erase_cons_tail (by simpa using fun e => hx'.1 e)
      -- A handed request is not `r`, so it is still woken.
      ·
        -- Take a request x handed in X.
        intro x hx
        -- It was handed before.
        rw [hXh] at hx
        -- State the goal with the old woken list without r.
        rw [hXw]
        -- x is not r, since r was not handed.
        have hxr : x ≠ r := fun e => hrh (e ▸ hx)
        -- x was woken, and is not r: it is still woken.
        exact (List.mem_erase_of_ne hxr).2 (hs.handed_woken x hx)
      -- The counts: a waiter of X waited before, so its count is within the bound.
      · intro x hx; rw [hXq] at hx; rw [hXb]; exact hs.bypass_le x (List.mem_of_mem_erase hx)
      -- Behind the head: drawn from the old tail.
      ·
        -- Take the head h of X's queue, its tail t, and a request x in t.
        intro h t ht x hx
        -- X's queue is the old one without r.
        rw [hXq] at ht
        -- The counts are the old ones.
        rw [hXb]
        -- Split on whether r was the old head.
        by_cases hrh0 : r = h0
        -- It was: X's queue is the old tail t0, so h :: t is t0;
        · rw [hq, hrh0, List.erase_cons_head] at ht
          -- x is in t0, behind the old head: its count is 0.
          exact hs.tail_zero h0 t0 hq x (by rw [ht]; exact List.mem_cons_of_mem _ hx)
        -- It was not: X's queue is h0 :: (t0 without r).
        · rw [hq, List.erase_cons_tail (by simpa using fun e => hrh0 e.symm)] at ht
          -- Compare the two shapes.
          simp only [List.cons.injEq] at ht
          -- So t is t0 without r.
          obtain ⟨-, e2⟩ := ht
          -- x is in it.
          rw [← e2] at hx
          -- x was in the old tail: its count is 0.
          exact hs.tail_zero h0 t0 hq x (List.mem_of_mem_erase hx)
      -- "The lock is free" contradicts "the lock is held": nothing to show.
      · intro h t _ hfr; rw [hXf, hf'] at hfr; simp at hfr
      -- Suppose a handoff is owed, and take a request x woken in X.
      · intro ho x hx
        -- The owed bit, the woken list and the handed list are the old ones (the woken one without
        -- r).
        rw [hXo] at ho; rw [hXw] at hx; rw [hXh]
        -- x was woken before, so it was handed the lock.
        exact hs.owed_woken ho x (List.mem_of_mem_erase hx)
      -- Every request named entered: take one, x.
      · intro x hx
        -- State where x is with the old fields.
        rw [hXq, hXown, hXh, hXw] at hx
        -- The entries are the old ones.
        rw [hXe]
        -- Split on which list x is in.
        rcases hx with hx | hx | hx | hx
        -- It waits: it waited before.
        · exact hs.all_enq x (Or.inl (List.mem_of_mem_erase hx))
        -- It owns: as before.
        · exact hs.all_enq x (Or.inr (Or.inl hx))
        -- Handed: as before.
        · exact hs.all_enq x (Or.inr (Or.inr (Or.inl hx)))
        -- Woken: woken before.
        · exact hs.all_enq x (Or.inr (Or.inr (Or.inr (List.mem_of_mem_erase hx))))
      -- A waiter holds nothing: take a waiter x of X; the holders are the old ones.
      · intro x hx; rw [hXq] at hx; rw [hXown, hXh]
        -- x waited before, and held nothing then.
        exact hs.queue_fresh x (List.mem_of_mem_erase hx)
  -- Case: a request r that was handed the lock is dropped before it was polled.
  | cancelHanded r hr =>
    -- The lock was handed to `r` alone, and only `r` is woken.
    have hho : s.owed = some r := by
      -- The "handed" list is the owed request, if any.
      have := hs.handed_owed
      -- r is in that list.
      rw [this] at hr
      -- Split on the owed bit.
      cases ho : s.owed with
      -- None owed: then nobody is handed. Impossible.
      | none => rw [ho] at hr; simp at hr
      -- Owed to w: then r is w.
      | some w => rw [ho] at hr; simp at hr; rw [hr]
    -- So r alone was handed the lock, there is no owner, and the lock is held.
    obtain ⟨hhand, hown, hfree⟩ := hs.owed_alone hho
    -- The woken list is exactly [r]:
    have hwk : s.woken = [r] := by
      -- Every woken request is r:
      have hsub : ∀ x ∈ s.woken, x = r := by
        -- take a woken x;
        intro x hx
        -- while a handoff is owed, a woken request is a handed one;
        have := hs.owed_woken (by simp [hho]) x hx
        -- and the only handed one is r.
        rw [hhand] at this; simpa using this
      -- r, being handed, is woken.
      have hrw := hs.handed_woken r (by rw [hhand]; exact List.mem_cons_self)
      -- Split on the woken list.
      cases hw' : s.woken with
      -- Empty: but r is woken. Impossible.
      | nil => rw [hw'] at hrw; simp at hrw
      -- A first woken a and more, l.
      | cons a l =>
        -- a is r.
        have ha := hsub a (by rw [hw']; exact List.mem_cons_self)
        -- Replace a by r.
        subst ha
        -- Woken requests are distinct.
        have hn := hs.woken_nodup
        -- So r is not in l.
        rw [hw', List.nodup_cons] at hn
        -- Split on l.
        cases l with
        -- Empty: the list is [r].
        | nil => rfl
        -- Another woken b:
        | cons b l' =>
          -- b is r too.
          have hb := hsub b (by rw [hw']; simp)
          -- Replace b by r.
          subst hb
          -- Then r would be in l, against "distinct".
          exact absurd List.mem_cons_self hn.1
    -- The queue has no request twice.
    have hqn := hs.queue_nodup
    -- Every waiter entered.
    have hall : ∀ x ∈ s.queue, x ∈ s.enq := fun x hx => hs.all_enq x (Or.inl hx)
    -- Unfold "pass the handoff on".
    unfold passOn
    -- The handed list and the woken list were [r]; without r both are empty.
    simp only [hhand, hwk, List.erase_cons_head]
    -- Split on the queue.
    cases hq : s.queue with
    -- Case: nobody waits.
    | nil =>
      -- Nobody waits: the lock is freed.
      exact inv_free rfl rfl hown rfl (by simp) (by simp) (by simp) hs.enq_nodup (by simp)
        -- (the last condition: an empty queue is distinct)
        (by simp)
    -- Case: a head h and a tail t.
    | cons h t =>
      -- The next waiter is handed the lock.
      rw [hq] at hqn hall
      -- For h :: t: h is not in t, and t is distinct.
      rw [List.nodup_cons] at hqn
      -- The handoff shape: the lock held by handoff to h, which alone is woken;
      exact inv_handoff hfree rfl hown (by simp) (by simp)
        -- the waiters left at 0; h not among them; entries distinct;
        (fun x hx => hs.tail_zero h t hq x hx) hqn.1 hs.enq_nodup
        -- every waiter and h entered; the queue distinct.
        (fun x hx => hall x (List.mem_cons_of_mem _ hx)) (hall h List.mem_cons_self) hqn.2

/-- Several steps keep the invariant. -/
theorem steps_inv {B : Nat}
    -- The bound is at least 1.
    (hB : 0 < B) {s t : M}
    -- The invariant holds at the start.
    (hs : Inv B s)
    -- Any number of steps.
    (hsteps : Steps B s t) :
    -- The statement: the invariant holds at the end.
    Inv B t := by
  -- Go through the steps one at a time.
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
    -- The statement: the invariant holds in s.
    Inv B s :=
  -- The start satisfies it, and steps keep it.
  steps_inv hB (init_inv B) h

/-! ## The laws -/

/-- **Mutual exclusion.** At most one request holds the lock, and none
while it is free. TLA+: `MutualExclusion`. -/
theorem mutual_exclusion {B : Nat}
    -- The bound is at least 1.
    (hB : 0 < B) {s : M}
    -- `s` is reachable from the start.
    (h : Steps B init s) :
    -- The statement: at most one request holds the lock, and while the lock is free nobody does.
    (s.owners ++ s.handed).length ≤ 1 ∧ (s.free = true → s.owners ++ s.handed = []) := by
  -- The invariant says: holders plus one-if-free make exactly 1.
  have hx := (reachable_inv hB h).excl
  -- First part: whether the lock is free or not, the holders number at most 1. Second part: suppose
  -- the lock is free.
  refine ⟨by split at hx <;> omega, fun hf => ?_⟩
  -- Use "free" in the count.
  rw [hf] at hx
  -- The count says: holders plus 1 is 1.
  simp only [ite_true] at hx
  -- So there are no holders: the list is empty.
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
    -- The statement: x's count is at most B.
    s.bypass x ≤ B :=
  -- That is one fact of the invariant, which every reachable state has.
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
    -- The statement: x's count is below B.
    s.bypass x < B := by
  -- A woken request that was not handed the lock is the head, with a count below B.
  obtain ⟨-, -, hb⟩ := (reachable_inv hB h).woken_head hw hh
  -- That is the claim.
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
    -- The statement: the count went up by exactly one, and x had been woken and not handed the
    -- lock.
    t.bypass x = s.bypass x + 1 ∧ x ∈ s.woken ∧ x ∉ s.handed := by
  -- The invariant holds before the step.
  have hs := reachable_inv hB h
  -- The helpers leave every count alone.
  have hwh : ∀ u : M, (wakeHead u).bypass = u.bypass := by
    -- Take any state; unfold "wake the head"; split on its queue.
    intro u; unfold wakeHead; split
    -- Nobody waits: nothing changed.
    · rfl
    -- A head: woken already or not, the counts are untouched.
    · split <;> rfl
  -- Split on the kind of step.
  cases hstep with
  -- The fast path changes no count: against "the count changed".
  | fast => exact absurd rfl hne
  -- A fresh request r joins the queue.
  | enqueue r hr _ =>
    -- `r` is fresh, so not `x`, which entered before.
    have hxr : x ≠ r := fun e => hr (e ▸ hs.all_enq x (Or.inl hx))
    -- The update is at r, not at x, so x's count did not change: against the assumption.
    simp [upd, hxr] at hne
  -- A release.
  | release r _ =>
    -- We show the count did not change, against the assumption.
    exfalso; apply hne
    -- Unfold the release rule and split on the queue.
    unfold relFrom; split
    -- Nobody waits: the counts are untouched.
    · rfl
    -- A head: split on whether it is below the bound.
    · split
      -- Below: only "wake the head" ran, which leaves the counts alone.
      · rw [hwh]
      -- At the bound: the handoff leaves the counts alone.
      · rfl
  -- Taking a handoff changes no count: against the assumption.
  | pollHanded => exact absurd rfl hne
  -- Winning the race changes no count: against the assumption.
  | pollWin => exact absurd rfl hne
  -- A woken request h' loses the race.
  | pollLose h' hw hh _ =>
    -- Only the loser's count changes.
    by_cases hxh : x = h'
    -- x is h': its count went up by one, and it was woken and not handed, by the step's conditions.
    · subst hxh; simp only [upd, ite_true]; exact ⟨trivial, hw, hh⟩
    -- x is another request: its count did not change, against the assumption.
    · simp [upd, hxh] at hne
  -- A waiter is dropped.
  | cancelWaiting r _ =>
    -- We show the count did not change, against the assumption.
    exfalso; apply hne
    -- Unfold "wake if free" and split on its condition.
    unfold wakeIfFree; split
    -- It wakes the head, which leaves the counts alone.
    · rw [hwh]
    -- It does nothing.
    · rfl
  -- A handed request is dropped.
  | cancelHanded r _ =>
    -- We show the count did not change, against the assumption.
    exfalso; apply hne
    -- Unfold "pass on": in both branches the counts are untouched.
    unfold passOn; split <;> rfl

/-- **At the bound, the next release hands off.** If the head has lost
`B` races and the owner releases, the head is handed the lock: owed, held
by it, woken, and the lock is not free. -/
theorem release_hands_off_at_bound {B : Nat} {s : M} {h r : Nat} {t : List Nat}
    -- `h` is the head ...
    (hq : s.queue = h :: t)
    -- ... and has lost `B` races.
    (hb : B ≤ s.bypass h) :
    -- Name the state after the release u.
    let u := relFrom B { s with owners := s.owners.erase r }
    -- The statement: in u the handoff is owed to h, h was handed the lock and woken, and the lock
    -- is free only if it already was.
    u.owed = some h ∧ h ∈ u.handed ∧ h ∈ u.woken ∧ u.free = s.free := by
  -- "h has lost B races" means its count is not below B.
  have : ¬ s.bypass h < B := by omega
  -- Unfold the release rule: with that head, it takes the handoff branch.
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
    -- The statement: w alone was handed the lock, nobody owns it, and it is not free.
    s.handed = [w] ∧ s.owners = [] ∧ s.free = false :=
  -- That is `Inv.owed_alone` for a reachable state.
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
    -- The statement: every owner after the step was an owner before, or is w.
    ∀ x ∈ t.owners, x ∈ s.owners ∨ x = w := by
  -- The invariant holds before the step.
  have hs := reachable_inv hB h
  -- w alone was handed the lock; there is no owner; the lock is held.
  obtain ⟨hhand, hown, hfree⟩ := hs.owed_alone hw
  -- Take an owner x after the step.
  intro x hx
  -- Split on the kind of step.
  cases hstep with
  -- The fast path needs "nothing owed": but a handoff is owed. Impossible.
  | fast _ _ _ ho => rw [hw] at ho; simp at ho
  -- Joining the queue changes no owner.
  | enqueue => exact Or.inl hx
  -- A release needs an owner: there is none. Impossible.
  | release r hr => rw [hown] at hr; simp at hr
  -- A request h' takes a handoff.
  | pollHanded h' _ hh =>
    -- The new owner is the one handed the lock: `w`.
    rw [hhand] at hh
    -- h' is in [w], so h' is w.
    simp only [List.mem_singleton] at hh
    -- Replace h' by w.
    subst hh
    -- The owners are now w and the old ones.
    simp only [List.mem_cons] at hx
    -- x is w, or an old owner.
    rcases hx with rfl | hx
    -- w: the second alternative.
    · exact Or.inr rfl
    -- An old owner: the first alternative.
    · exact Or.inl hx
  -- Winning the race needs a free lock: the lock is held. Impossible.
  | pollWin _ _ _ hf => rw [hfree] at hf; simp at hf
  -- Losing the race changes no owner.
  | pollLose => exact Or.inl hx
  -- A waiter is dropped.
  | cancelWaiting r _ =>
    -- The lock is held: no wake, no owner change.
    have : (wakeIfFree { s with queue := s.queue.erase r, woken := s.woken.erase r }).owners =
        s.owners := by
      -- Unfold "wake if free": the lock is held, so nothing happens.
      unfold wakeIfFree; simp only [hfree, Bool.false_eq_true, false_and, ite_false]
    -- The owners are the old ones.
    rw [this] at hx; exact Or.inl hx
  -- A handed request is dropped.
  | cancelHanded r _ =>
    -- A passed-on handoff makes nobody an owner yet.
    have : (passOn { s with handed := s.handed.erase r, woken := s.woken.erase r,
                            owed := none }).owners = s.owners := by
      -- Unfold "pass on": in both branches the owners are untouched.
      unfold passOn; split <;> rfl
    -- The owners are the old ones.
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
    -- The statement: x has been woken.
    x ∈ s.woken :=
  -- That is one fact of the invariant, which every reachable state has.
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
    -- The statement: x has been woken.
    x ∈ s.woken :=
  -- That is one fact of the invariant, which every reachable state has.
  (reachable_inv hB h).handed_woken x hx

/-! ## The RED cases -/

/-- The unbounded-barging design: a release always frees the lock and
wakes the head; it never hands off. -/
inductive StepNoHand : M → M → Prop
  /-- As `Step.fast`. -/
  | fast (s : M) (r : Nat)
      -- `r` is fresh, the lock free, nothing owed.
      (hr : r ∉ s.enq) (hf : s.free = true) (ho : s.owed = none) :
      -- After the step: the lock is held, r is an owner, and r has entered.
      StepNoHand s { s with free := false, owners := r :: s.owners, enq := s.enq ++ [r] }
  /-- As `Step.enqueue`. -/
  | enqueue (s : M) (r : Nat)
      -- `r` is fresh, and the fast path is shut.
      (hr : r ∉ s.enq) (hc : s.free = false ∨ s.owed ≠ none) :
      -- After the step: r is at the tail of the queue, has entered,
      StepNoHand s { s with queue := s.queue ++ [r], enq := s.enq ++ [r],
                            -- and has a count of 0.
                            bypass := upd s.bypass r 0 }
  /-- The defect: free and wake the head, whatever its count. -/
  | release (s : M) (r : Nat)
      -- `r` holds the lock.
      (hr : r ∈ s.owners) :
      -- After the step: r is no longer an owner, the lock is free, and the head is woken.
      StepNoHand s (wakeHead { s with owners := s.owners.erase r, free := true })
  /-- As `Step.pollLose`. -/
  | pollLose (s : M) (h : Nat)
      -- `h` was woken, not handed, and the fast path is shut.
      (hw : h ∈ s.woken) (hh : h ∉ s.handed) (hc : s.free = false ∨ s.owed ≠ none) :
      -- After the step: h's count is one more, and h is no longer "woken".
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
    -- The statement: some state the defective steps reach has request 2 still waiting with a count
    -- of 2.
    ∃ s, StepsNoHand init s ∧ 2 ∈ s.queue ∧ s.bypass 2 = 2 := by
  -- The run, written from the inside out: eight steps from the start, then the two facts about the
  -- final state, each computed.
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
      -- After the step: the lock is held, r is an owner, and r has entered.
      StepNoWake s { s with free := false, owners := r :: s.owners, enq := s.enq ++ [r] }
  /-- As `Step.enqueue`. -/
  | enqueue (s : M) (r : Nat)
      -- `r` is fresh, and the fast path is shut.
      (hr : r ∉ s.enq) (hc : s.free = false ∨ s.owed ≠ none) :
      -- After the step: r is at the tail of the queue, has entered,
      StepNoWake s { s with queue := s.queue ++ [r], enq := s.enq ++ [r],
                            -- and has a count of 0.
                            bypass := upd s.bypass r 0 }
  /-- The defect: free the lock, wake nobody. -/
  | release (s : M) (r : Nat)
      -- `r` holds the lock.
      (hr : r ∈ s.owners) :
      -- After the step: r is no longer an owner and the lock is free. Nobody is woken.
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
    -- The statement: some state the defective steps reach has request 2 at the head of the queue,
    -- the lock free, and request 2 not woken.
    ∃ s, StepsNoWake init s ∧ s.queue = [2] ∧ s.free = true ∧ 2 ∉ s.woken := by
  -- The run, written from the inside out: three steps from the start, then the facts about the
  -- final state, each computed.
  refine ⟨_, .tail (.tail (.tail (.refl init)
    -- Request 1 takes the lock; request 2 waits.
    (.fast _ 1 (by decide) rfl rfl))
    (.enqueue _ 2 (by decide) (Or.inl rfl)))
    -- Request 1 releases and wakes nobody.
    (.release _ 1 (by decide)), by decide, rfl, by decide⟩

-- The end of this file's names.
end Regolith.Sync
