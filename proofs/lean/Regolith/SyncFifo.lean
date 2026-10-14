/-!
# SyncFifo: the FIFO waiter queue with handoff before wake (regolith::sync::Notify)

This file backs the TLA+ models of `regolith::sync` that keep FIFO
handoff in `proofs/tla`:

* `SyncNotify.tla`, invariants `FifoHandoff`, `NoLostWakeup` and
  `CancelPassesOn` (configurations `MC_SyncNotify_*`): Notify hands a
  notification to its oldest waiter before waking it;
* the waiter lists of `SyncLatch.tla` and `SyncOnce.tla`, which use the same
  registration and re-check.

Before D49 this file backed the locks too. D49 replaced FIFO handoff by
barging with a bypass bound for the lock-like primitives; their proofs are
`Regolith/Sync.lean`. Notify keeps its semantics, so the queue laws here
still back it: FIFO service, no waiter stranded beside a stored permit,
handoff before wake, and the RED cases. The model holds a fixed number of
permits, which Notify does not (notify_one creates one, notified() consumes
it), so the counting laws `permits_bounded` and `at_most_one_owner` are
about the fixed-permit queue only.

TLC checks those models step by atomic step for three tasks. Here the queue
is a sequential state machine: each step is one of the abstract actions
(fast acquire, enqueue, release, wake, poll, cancel), and a reachable state
is the result of any sequence of them, so every interleaving of the actions
is covered. The theorems hold for every number of permits, requests and
steps. The model has `n` permits and every request asks for one; Notify
is `n = 1`.

What is proved, in plain words:

1. `step_inv` and `reachable_inv`: the queue's invariant holds in every
   reachable state.
2. `permits_bounded` and `at_most_one_owner`: at most `n` requests hold a
   permit; with one permit, at most one owner exists at any time.
3. `fifo_served` and `served_in_order`: requests are served in the order
   they entered the line, and no request is ever served while one that
   entered before it still waits. Cancelled waiters are skipped.
4. `no_stranded_waiter`: while anyone waits, no permit is free; a release
   hands its permit to the oldest waiter instead of freeing it.
5. `handed_holds` and `no_lost_handoff`: a woken waiter always owns its
   permit (the handoff comes before the wake), and a waiter handed a permit
   is woken or owed a wake.
6. `position_never_grows` and `handoff_advances`: the waiters ahead of a
   waiter only ever leave, and every handoff removes one of them or serves
   it, so a waiter that is not cancelled is served after at most as many
   handoffs as there were waiters ahead of it, plus one.
7. Cancellation with pass-on is one of the steps, so all of the above hold
   with it. Three RED cases, as counterexamples:
   `barging_breaks_fifo` (a fast path that ignores the queue),
   `wake_before_handoff_strands` (waking before handing over loses the
   wake for good) and `cancel_without_pass_on_strands` (a cancelled waiter
   that keeps its permit leaves the next waiter unserved forever).

How to read the Lean: `def` defines a function or a property, `theorem`
states a fact and its proof follows `:= by`. Lines starting with `--` are
comments. `l.Sublist m` (written `<+` in some texts) says the elements of
`l` appear in `m` in the same order, possibly with others between them;
`[a, b].Sublist l` therefore says that `a` comes before `b` in `l`.
-/

namespace Regolith.SyncFifo

/-! ## The state -/

/-- The waiter queue's state. A request is named by a natural number,
fresh for every acquire. -/
structure Q where
  /-- Permits nobody holds. -/
  free : Nat
  /-- The waiting requests, oldest first. -/
  queue : List Nat
  /-- Requests that hold a permit and know it: they took it on the fast
  path, or were handed it and have been polled since. -/
  owners : List Nat
  /-- Requests a release handed a permit to, not yet polled. They hold
  the permit already. -/
  handed : List Nat
  /-- Requests whose Waker must still be called. -/
  owed : List Nat
  /-- Requests whose Waker was called, not yet polled. -/
  woken : List Nat
  /-- Ghost: every request that entered the line (took the fast path or
  enqueued), in order. -/
  enq : List Nat
  /-- Ghost: every request that was given a permit, in order. -/
  served : List Nat
  deriving DecidableEq

/-- The start: `n` free permits, nobody waiting or holding. -/
def init (n : Nat) : Q := ⟨n, [], [], [], [], [], [], []⟩

/-- A permit comes back (a release, or a cancelled waiter passing on what
it was handed). If someone waits, the oldest waiter is handed the permit
and owed a wake; only if nobody waits does the permit become free. -/
def handoff (s : Q) : Q :=
  match s.queue with
  -- Nobody waits: the permit is free.
  | [] => { s with free := s.free + 1 }
  -- The oldest waiter `h` is handed the permit, and only then owed a wake.
  | h :: t => { s with queue := t, handed := s.handed ++ [h], owed := s.owed ++ [h],
                       served := s.served ++ [h] }

/-! ## The steps -/

/-- The design's steps. -/
inductive Step : Q → Q → Prop
  /-- `try_acquire`, or `acquire` uncontended: a fresh request `r` takes a
  free permit, but only when nobody waits (it never jumps the queue). -/
  | fast (s : Q) (r : Nat)
      -- `r` is a fresh request.
      (hr : r ∉ s.enq)
      -- Nobody waits.
      (hq : s.queue = [])
      -- A permit is free.
      (hf : 0 < s.free) :
      Step s { s with free := s.free - 1, owners := r :: s.owners,
                      enq := s.enq ++ [r], served := s.served ++ [r] }
  /-- A contended `acquire`: a fresh request `r` joins the back of the
  queue. Contended means someone waits or no permit is free: the re-check
  after the push (SyncNotify.tla's drain) takes a free permit itself otherwise. -/
  | enqueue (s : Q) (r : Nat)
      -- `r` is a fresh request.
      (hr : r ∉ s.enq)
      -- The fast path is shut.
      (hc : s.queue ≠ [] ∨ s.free = 0) :
      Step s { s with queue := s.queue ++ [r], enq := s.enq ++ [r] }
  /-- An owner drops its guard: its permit goes through `handoff`. -/
  | release (s : Q) (r : Nat)
      -- `r` owns a permit.
      (hr : r ∈ s.owners) :
      Step s (handoff { s with owners := s.owners.erase r })
  /-- `Waker::wake` for a request owed a wake. -/
  | wake (s : Q) (r : Nat)
      -- `r` is owed a wake.
      (hr : r ∈ s.owed) :
      Step s { s with owed := s.owed.filter (· != r), woken := s.woken ++ [r] }
  /-- The executor polls a woken request, which finds its permit and
  becomes an owner. -/
  | poll (s : Q) (r : Nat)
      -- `r` was woken.
      (hw : r ∈ s.woken)
      -- `r` was handed a permit.
      (hh : r ∈ s.handed) :
      Step s { s with woken := s.woken.filter (· != r), handed := s.handed.erase r,
                      owners := r :: s.owners }
  /-- A waiting request's future is dropped: it leaves the queue. -/
  | cancelWaiting (s : Q) (r : Nat)
      -- `r` waits.
      (hr : r ∈ s.queue) :
      Step s { s with queue := s.queue.erase r }
  /-- A request's future is dropped after it was handed a permit but
  before it was polled: it passes the permit on through `handoff`. -/
  | cancelHanded (s : Q) (r : Nat)
      -- `r` was handed a permit.
      (hr : r ∈ s.handed) :
      Step s (handoff { s with handed := s.handed.erase r,
                               owed := s.owed.filter (· != r),
                               woken := s.woken.filter (· != r) })

/-- Any number of steps, one after another. -/
inductive Steps : Q → Q → Prop
  /-- No step at all. -/
  | refl (s : Q) : Steps s s
  /-- Some steps, then one more. -/
  | tail {s t u : Q} : Steps s t → Step t u → Steps s u

/-! ## The invariant -/

/-- An element of a filtered list is an element of the list. -/
theorem mem_of_mem_filter {l : List Nat} {p : Nat → Bool} {a : Nat}
    -- `a` survived the filter.
    (h : a ∈ l.filter p) :
    a ∈ l :=
  (List.mem_filter.1 h).1

/-- Everything about a state except the permit count. -/
structure Core (s : Q) : Prop where
  /-- While anyone waits, no permit is free. -/
  no_stranded : s.queue ≠ [] → s.free = 0
  /-- The served requests, then the waiting ones, appear in the line in
  this order: service follows entry order. -/
  line : (s.served ++ s.queue).Sublist s.enq
  /-- Every request entered the line once. -/
  enq_nodup : s.enq.Nodup
  /-- No request holds two permits. -/
  holders_nodup : (s.owners ++ s.handed).Nodup
  /-- Every holder was served. -/
  holders_served : ∀ r, r ∈ s.owners ∨ r ∈ s.handed → r ∈ s.served
  /-- A request owed a wake holds its permit already. -/
  owed_handed : ∀ r ∈ s.owed, r ∈ s.handed
  /-- A woken request holds its permit already. -/
  woken_handed : ∀ r ∈ s.woken, r ∈ s.handed
  /-- A request handed a permit is owed a wake or was woken. -/
  handed_woken : ∀ r ∈ s.handed, r ∈ s.owed ∨ r ∈ s.woken
  /-- No request is both owed a wake and woken. -/
  owed_not_woken : ∀ r ∈ s.owed, r ∉ s.woken

/-- The invariant for `n` permits: the core, and every permit is free or
held. -/
structure Inv (n : Nat) (s : Q) : Prop where
  /-- Everything but the count. -/
  core : Core s
  /-- Free permits plus held permits are `n`. -/
  conserve : s.free + s.owners.length + s.handed.length = n

/-- `[b, a]` appears in `served ++ queue` when `b` was served and `a`
waits: whoever is served sits before whoever waits. -/
theorem served_before_waiting {s : Q} {a b : Nat}
    -- `b` was served.
    (hb : b ∈ s.served)
    -- `a` waits.
    (ha : a ∈ s.queue) :
    [b, a].Sublist (s.served ++ s.queue) :=
  -- `[b]` sits inside `served` and `[a]` inside `queue`.
  (List.singleton_sublist.2 hb).append (List.singleton_sublist.2 ha)

/-- The served and waiting requests are all distinct. -/
theorem Core.line_nodup {s : Q}
    -- The core invariant holds.
    (h : Core s) : (s.served ++ s.queue).Nodup :=
  -- A sublist of a list without repeats has none.
  h.enq_nodup.sublist h.line

/-- A waiting request holds nothing and was never served. -/
theorem Core.waiting_fresh {s : Q}
    -- The core invariant holds.
    (h : Core s) {r : Nat}
    -- `r` waits.
    (hr : r ∈ s.queue) :
    r ∉ s.served ∧ r ∉ s.owners ∧ r ∉ s.handed := by
  -- `served ++ queue` has no repeats, so `r` is not in `served`.
  have hns : r ∉ s.served := by
    intro hs
    exact (List.nodup_append.1 h.line_nodup).2.2 r hs r hr rfl
  -- Every holder was served, so `r` holds nothing.
  exact ⟨hns, fun ho => hns (h.holders_served r (Or.inl ho)),
    fun hh => hns (h.holders_served r (Or.inr hh))⟩

/-- No request is both an owner and handed a permit. -/
theorem Core.not_owner_of_handed {s : Q}
    -- The core invariant holds.
    (h : Core s) {r : Nat}
    -- `r` was handed a permit.
    (hr : r ∈ s.handed) :
    r ∉ s.owners :=
  -- `owners ++ handed` has no repeats.
  fun ho => (List.nodup_append.1 h.holders_nodup).2.2 r ho r hr rfl

/-- The handed requests are distinct. -/
theorem Core.handed_nodup {s : Q}
    -- The core invariant holds.
    (h : Core s) : s.handed.Nodup :=
  (List.nodup_append.1 h.holders_nodup).2.1

/-! ## Every step keeps the invariant -/

/-- A permit coming back through `handoff` restores the count: if `s` is
one permit short, `handoff s` is not. And the core survives. -/
theorem handoff_inv {n : Nat} {s : Q}
    -- The core holds before the permit comes back.
    (hc : Core s)
    -- The count is one short.
    (hn : s.free + s.owners.length + s.handed.length + 1 = n) :
    Inv n (handoff s) := by
  unfold handoff
  -- Is anyone waiting?
  cases hq : s.queue with
  | nil =>
    -- Nobody waits: the permit becomes free, and nothing else changes.
    refine ⟨⟨fun h => absurd rfl h, ?_, hc.enq_nodup, hc.holders_nodup, hc.holders_served,
      hc.owed_handed, hc.woken_handed, hc.handed_woken, hc.owed_not_woken⟩, ?_⟩
    · -- The line still holds `served` in order.
      have := hc.line
      rw [hq] at this
      simpa using this
    · simp only; omega
  | cons h t =>
    -- `h` waited: it is fresh to every holder list.
    have hh : h ∈ s.queue := by rw [hq]; exact List.mem_cons_self
    obtain ⟨hns, hno, hnh⟩ := hc.waiting_fresh hh
    -- `h` was not woken either: woken requests hold permits.
    have hnw : h ∉ s.woken := fun hw => hnh (hc.woken_handed h hw)
    refine ⟨⟨?_, ?_, hc.enq_nodup, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · -- Others still wait only if the free count was already 0.
      intro _
      exact hc.no_stranded (by rw [hq]; exact List.cons_ne_nil h t)
    · -- `served ++ [h] ++ t` is `served ++ (h :: t)`, the old line.
      have := hc.line
      rw [hq] at this
      simpa [List.append_assoc] using this
    · -- `h` joins the holders, to which it is new.
      simp only
      rw [← List.append_assoc, List.nodup_append]
      refine ⟨hc.holders_nodup, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      intro hab
      subst hab
      rcases List.mem_append.1 ha with ho | hd
      · exact hno ho
      · exact hnh hd
    · -- Every holder was served; `h` now is.
      intro r hr
      simp only [List.mem_append, List.mem_singleton] at hr ⊢
      rcases hr with ho | hd | rfl
      · exact Or.inl (hc.holders_served r (Or.inl ho))
      · exact Or.inl (hc.holders_served r (Or.inr hd))
      · exact Or.inr rfl
    · -- `h` is owed a wake and holds its permit.
      intro r hr
      simp only [List.mem_append, List.mem_singleton] at hr ⊢
      rcases hr with hr | rfl
      · exact Or.inl (hc.owed_handed r hr)
      · exact Or.inr rfl
    · -- Woken requests are unchanged and still hold.
      intro r hr
      simp only [List.mem_append]
      exact Or.inl (hc.woken_handed r hr)
    · -- `h` is owed a wake; every other handed request as before.
      intro r hr
      simp only [List.mem_append, List.mem_singleton] at hr ⊢
      rcases hr with hr | rfl
      · rcases hc.handed_woken r hr with ho | hw
        · exact Or.inl (Or.inl ho)
        · exact Or.inr hw
      · exact Or.inl (Or.inr rfl)
    · -- `h` was not woken, so it is owed without being woken.
      intro r hr
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hc.owed_not_woken r hr
      · exact hnw
    · -- One more holder, one fewer missing permit.
      simp only [List.length_append, List.length_singleton]
      omega

/-- The start satisfies the invariant. -/
theorem init_inv (n : Nat) : Inv n (init n) := by
  -- Everything is empty, and every permit is free.
  refine ⟨⟨fun h => absurd rfl h, List.Sublist.slnil, List.nodup_nil, List.nodup_nil,
    ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [init]

/-- **Every step keeps the invariant.** -/
theorem step_inv {n : Nat} {s t : Q}
    -- The invariant holds before the step.
    (hinv : Inv n s)
    -- One step of the design.
    (hstep : Step s t) :
    Inv n t := by
  obtain ⟨hc, hn⟩ := hinv
  cases hstep with
  | fast r hr hq hf =>
    -- `r` is new to the line, so new to every list drawn from it.
    have hserved : r ∉ s.served := fun h =>
      hr ((List.sublist_append_left _ _).trans hc.line |>.subset h)
    refine ⟨⟨fun h => absurd hq h, ?_, ?_, ?_, ?_, hc.owed_handed, hc.woken_handed,
      hc.handed_woken, hc.owed_not_woken⟩, ?_⟩
    · -- Nobody waits, so the line is `served`, and `r` joins both ends.
      have := hc.line
      rw [hq] at this ⊢
      simpa using this.append (List.Sublist.refl [r])
    · -- `r` is fresh.
      rw [List.nodup_append]
      refine ⟨hc.enq_nodup, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      intro hab
      subst hab
      exact hr ha
    · -- `r` holds nothing yet: it was never served.
      simp only [List.cons_append, List.nodup_cons]
      refine ⟨?_, hc.holders_nodup⟩
      intro hm
      rcases List.mem_append.1 hm with ho | hd
      · exact hserved (hc.holders_served r (Or.inl ho))
      · exact hserved (hc.holders_served r (Or.inr hd))
    · -- `r` is served now; the others were before.
      intro x hx
      rw [List.mem_append, List.mem_singleton]
      simp only [List.mem_cons] at hx
      rcases hx with (rfl | ho) | hd
      · exact Or.inr rfl
      · exact Or.inl (hc.holders_served x (Or.inl ho))
      · exact Or.inl (hc.holders_served x (Or.inr hd))
    · -- One permit moves from free to `r`.
      simp only [List.length_cons]
      omega
  | enqueue r hr hcont =>
    refine ⟨⟨?_, ?_, ?_, hc.holders_nodup, hc.holders_served, hc.owed_handed,
      hc.woken_handed, hc.handed_woken, hc.owed_not_woken⟩, hn⟩
    · -- Someone waited already (so nothing was free), or nothing was free.
      intro _
      rcases hcont with hq | hf
      · exact hc.no_stranded hq
      · exact hf
    · -- `r` joins the back of the queue and of the line.
      have := hc.line.append (List.Sublist.refl [r])
      simpa [List.append_assoc] using this
    · -- `r` is fresh.
      rw [List.nodup_append]
      refine ⟨hc.enq_nodup, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      intro hab
      subst hab
      exact hr ha
  | release r hr =>
    -- Drop `r` from the owners; the permit comes back through `handoff`.
    apply handoff_inv
    · refine ⟨hc.no_stranded, hc.line, hc.enq_nodup, ?_, ?_, hc.owed_handed, hc.woken_handed,
        hc.handed_woken, hc.owed_not_woken⟩
      · -- Fewer owners: still no repeats.
        exact hc.holders_nodup.sublist (List.erase_sublist.append (List.Sublist.refl _))
      · -- Fewer owners: still all served.
        intro x hx
        rcases hx with ho | hd
        · exact hc.holders_served x (Or.inl (List.mem_of_mem_erase ho))
        · exact hc.holders_served x (Or.inr hd)
    · -- One owner fewer.
      simp only
      have := List.length_erase_of_mem hr
      have : 0 < s.owners.length := List.length_pos_of_mem hr
      omega
  | wake r hr =>
    refine ⟨⟨hc.no_stranded, hc.line, hc.enq_nodup, hc.holders_nodup, hc.holders_served,
      ?_, ?_, ?_, ?_⟩, hn⟩
    · -- Fewer owed requests: still holders.
      intro x hx
      exact hc.owed_handed x (mem_of_mem_filter hx)
    · -- `r` is woken, and holds its permit since it was owed.
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hc.woken_handed x hx
      · exact hc.owed_handed x hr
    · -- `r` moves from owed to woken; the rest stay where they were.
      intro x hx
      by_cases hxr : x = r
      · subst hxr
        exact Or.inr (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)))
      · rcases hc.handed_woken x hx with ho | hw
        · exact Or.inl (List.mem_filter.2 ⟨ho, by simpa using hxr⟩)
        · exact Or.inr (List.mem_append.2 (Or.inl hw))
    · -- An owed request other than `r` was not woken, and is not `r`.
      intro x hx
      have hx' := List.mem_filter.1 hx
      have hxr : x ≠ r := by simpa using hx'.2
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨hc.owed_not_woken x hx'.1, hxr⟩
  | poll r hw hh =>
    have hhn := hc.handed_nodup
    have hro := hc.not_owner_of_handed hh
    -- `r` is not owed: it is woken.
    have hnot_owed : r ∉ s.owed := fun ho => hc.owed_not_woken r ho hw
    refine ⟨⟨hc.no_stranded, hc.line, hc.enq_nodup, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · -- `r` moves from handed to owners: still no repeats.
      simp only [List.cons_append, List.nodup_cons]
      refine ⟨?_, ?_⟩
      · intro hm
        rcases List.mem_append.1 hm with ho | hd
        · exact hro ho
        · exact List.Nodup.not_mem_erase hhn hd
      · rw [List.nodup_append]
        obtain ⟨ho, hd, hdis⟩ := List.nodup_append.1 hc.holders_nodup
        exact ⟨ho, hd.erase r, fun a ha b hb => hdis a ha b (List.mem_of_mem_erase hb)⟩
    · -- Holders were served; `r` was a holder.
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with (rfl | ho) | hd
      · exact hc.holders_served x (Or.inr hh)
      · exact hc.holders_served x (Or.inl ho)
      · exact hc.holders_served x (Or.inr (List.mem_of_mem_erase hd))
    · -- Owed requests are not `r`, so still handed.
      intro x hx
      have hxr : x ≠ r := fun h => hnot_owed (h ▸ hx)
      exact (List.mem_erase_of_ne hxr).2 (hc.owed_handed x hx)
    · -- Woken requests other than `r` are still handed.
      intro x hx
      have hx' := List.mem_filter.1 hx
      have hxr : x ≠ r := by simpa using hx'.2
      exact (List.mem_erase_of_ne hxr).2 (hc.woken_handed x hx'.1)
    · -- A handed request other than `r` is still owed or still woken.
      intro x hx
      have hx' := (List.Nodup.mem_erase_iff hhn).1 hx
      rcases hc.handed_woken x hx'.2 with ho | hwx
      · exact Or.inl ho
      · exact Or.inr (List.mem_filter.2 ⟨hwx, by simpa using hx'.1⟩)
    · -- Fewer woken: the owed ones still are not woken.
      intro x hx hxw
      exact hc.owed_not_woken x hx (mem_of_mem_filter hxw)
    · -- `r` moves from handed to owners: the count is unchanged.
      simp only [List.length_cons]
      have := List.length_erase_of_mem hh
      have : 0 < s.handed.length := List.length_pos_of_mem hh
      omega
  | cancelWaiting r hr =>
    refine ⟨⟨?_, ?_, hc.enq_nodup, hc.holders_nodup, hc.holders_served, hc.owed_handed,
      hc.woken_handed, hc.handed_woken, hc.owed_not_woken⟩, hn⟩
    · -- `r` waited, so someone waited, so nothing was free.
      intro _
      exact hc.no_stranded (List.ne_nil_of_mem hr)
    · -- Removing a waiter keeps the order of the rest.
      exact ((List.Sublist.refl _).append List.erase_sublist).trans hc.line
  | cancelHanded r hr =>
    have hhn := hc.handed_nodup
    -- Drop `r` everywhere; its permit comes back through `handoff`.
    apply handoff_inv
    · refine ⟨hc.no_stranded, hc.line, hc.enq_nodup, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- Fewer handed: still no repeats.
        exact hc.holders_nodup.sublist ((List.Sublist.refl _).append List.erase_sublist)
      · -- Fewer handed: still all served.
        intro x hx
        rcases hx with ho | hd
        · exact hc.holders_served x (Or.inl ho)
        · exact hc.holders_served x (Or.inr (List.mem_of_mem_erase hd))
      · -- Owed requests other than `r` are still handed.
        intro x hx
        have hx' := List.mem_filter.1 hx
        have hxr : x ≠ r := by simpa using hx'.2
        exact (List.mem_erase_of_ne hxr).2 (hc.owed_handed x hx'.1)
      · -- Woken requests other than `r` are still handed.
        intro x hx
        have hx' := List.mem_filter.1 hx
        have hxr : x ≠ r := by simpa using hx'.2
        exact (List.mem_erase_of_ne hxr).2 (hc.woken_handed x hx'.1)
      · -- A handed request other than `r` is still owed or still woken.
        intro x hx
        have hx' := (List.Nodup.mem_erase_iff hhn).1 hx
        have hxr : (x != r) = true := by simpa using hx'.1
        rcases hc.handed_woken x hx'.2 with ho | hw
        · exact Or.inl (List.mem_filter.2 ⟨ho, hxr⟩)
        · exact Or.inr (List.mem_filter.2 ⟨hw, hxr⟩)
      · -- Fewer owed and woken: still disjoint.
        intro x hx hxw
        exact hc.owed_not_woken x (mem_of_mem_filter hx) (mem_of_mem_filter hxw)
    · -- One handed request fewer.
      simp only
      have := List.length_erase_of_mem hr
      have : 0 < s.handed.length := List.length_pos_of_mem hr
      omega

/-- Several steps keep the invariant. -/
theorem steps_inv {n : Nat} {s t : Q}
    -- The invariant holds at the start.
    (hinv : Inv n s)
    -- Any number of steps.
    (hsteps : Steps s t) :
    Inv n t := by
  induction hsteps with
  -- No step: nothing changed.
  | refl => exact hinv
  -- The steps so far, then one more.
  | tail _ hstep ih => exact step_inv ih hstep

/-- **Every state reachable from the start satisfies the invariant.** -/
theorem reachable_inv {n : Nat} {s : Q}
    -- `s` is reachable from the start.
    (h : Steps (init n) s) : Inv n s :=
  steps_inv (init_inv n) h

/-! ## The laws -/

/-- **At most `n` holders.** No more requests hold a permit than there
are permits. (A law of the fixed-permit queue. Notify creates and consumes
notifications, so SyncNotify.tla has no counterpart; the laws that back it
are the FIFO, stranding and handoff ones below.) -/
theorem permits_bounded {n : Nat} {s : Q}
    -- `s` is reachable from the start.
    (h : Steps (init n) s) :
    (s.owners ++ s.handed).length ≤ n := by
  have := (reachable_inv h).conserve
  simp only [List.length_append]
  omega

/-- **At most one owner.** With one permit, any two holders are the same
request. (A law of the fixed-permit queue, as above.) -/
theorem at_most_one_owner {s : Q}
    -- `s` is reachable from the start, with one permit.
    (h : Steps (init 1) s) {a b : Nat}
    -- `a` holds a permit.
    (ha : a ∈ s.owners ++ s.handed)
    -- `b` holds a permit.
    (hb : b ∈ s.owners ++ s.handed) :
    a = b := by
  -- The holders are at most one, so any two of them coincide.
  have hlen := permits_bounded h
  generalize s.owners ++ s.handed = l at ha hb hlen
  match l, ha, hb, hlen with
  | [x], ha, hb, _ =>
    simp only [List.mem_singleton] at ha hb
    rw [ha, hb]

/-- No list without repeats has two elements in both orders. -/
theorem no_two_orders {l : List Nat} {a b : Nat}
    -- `l` has no repeats.
    (hl : l.Nodup)
    -- `a` comes before `b` in `l`.
    (hab : [a, b].Sublist l)
    -- `b` comes before `a` in `l`.
    (hba : [b, a].Sublist l) :
    False := by
  induction l with
  | nil =>
    -- The empty list holds neither.
    exact absurd (hab.subset (List.mem_cons_self)) (by simp)
  | cons c l ih =>
    obtain ⟨hc, hl'⟩ := List.nodup_cons.1 hl
    rcases List.sublist_cons_iff.1 hab with hab' | ⟨r, hr, hr'⟩
    · rcases List.sublist_cons_iff.1 hba with hba' | ⟨r', hr2, hr2'⟩
      · -- Both orders inside the tail: the tail is the smaller case.
        exact ih hl' hab' hba'
      · -- `b = c` heads the list, yet `b` also sits in the tail after `a`.
        simp only [List.cons.injEq] at hr2
        obtain ⟨rfl, rfl⟩ := hr2
        exact hc (hab'.subset (List.mem_cons_of_mem _ List.mem_cons_self))
    · -- `a = c` heads the list.
      simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      rcases List.sublist_cons_iff.1 hba with hba' | ⟨r', hr2, hr2'⟩
      · -- `a` also sits in the tail, after `b`: a repeat.
        exact hc (hba'.subset (List.mem_cons_of_mem _ List.mem_cons_self))
      · -- Then `b = c = a` too, and `b` sits in the tail: a repeat.
        simp only [List.cons.injEq] at hr2
        obtain ⟨rfl, rfl⟩ := hr2
        exact hc (hr'.subset List.mem_cons_self)

/-- **FIFO handoff, no barging.** If request `a` entered the line before
request `b`, and `b` has been served, then `a` no longer waits: nobody is
served ahead of an earlier request still in the queue. TLA+: `FifoHandoff`. -/
theorem fifo_served {n : Nat} {s : Q}
    -- `s` is reachable from the start.
    (h : Steps (init n) s) {a b : Nat}
    -- `a` entered the line before `b`.
    (hab : [a, b].Sublist s.enq)
    -- `b` was served.
    (hb : b ∈ s.served) :
    a ∉ s.queue := by
  intro ha
  have hc := (reachable_inv h).core
  -- In `served ++ queue` the served `b` precedes the waiting `a`, and that
  -- order carries into the line, against `a` before `b` there.
  exact no_two_orders hc.enq_nodup hab ((served_before_waiting hb ha).trans hc.line)

/-- **Served in order.** The served requests appear in the order they
entered the line. -/
theorem served_in_order {n : Nat} {s : Q}
    -- `s` is reachable from the start.
    (h : Steps (init n) s) :
    s.served.Sublist s.enq :=
  (List.sublist_append_left _ _).trans (reachable_inv h).core.line

/-- **No stranded waiter.** While anyone waits, no permit is free: a free
permit always goes to the oldest waiter. TLA+: `NoLostWakeup` (Stranded). -/
theorem no_stranded_waiter {n : Nat} {s : Q}
    -- `s` is reachable from the start.
    (h : Steps (init n) s)
    -- Someone waits.
    (hq : s.queue ≠ []) :
    s.free = 0 :=
  (reachable_inv h).core.no_stranded hq

/-- **Handoff before wake.** A woken request already owns its permit, so
the poll the wake causes always finds it. TLA+: `NoLostWakeup`
(GrantedWoken). -/
theorem handed_holds {n : Nat} {s : Q}
    -- `s` is reachable from the start.
    (h : Steps (init n) s) {r : Nat}
    -- `r` was woken.
    (hr : r ∈ s.woken) :
    r ∈ s.handed :=
  (reachable_inv h).core.woken_handed r hr

/-- **No lost handoff.** A request handed a permit is woken or owed a
wake. TLA+: `NoLostWakeup` (GrantedWoken). -/
theorem no_lost_handoff {n : Nat} {s : Q}
    -- `s` is reachable from the start.
    (h : Steps (init n) s) {r : Nat}
    -- `r` was handed a permit.
    (hr : r ∈ s.handed) :
    r ∈ s.owed ∨ r ∈ s.woken :=
  (reachable_inv h).core.handed_woken r hr

/-- **A release serves the head.** When someone waits, a release hands the
oldest waiter the permit and owes it a wake. -/
theorem release_serves_head {s : Q} {h r : Nat} {t : List Nat}
    -- `h` is the oldest waiter.
    (hq : s.queue = h :: t) :
    let s' := handoff { s with owners := s.owners.erase r }
    h ∈ s'.handed ∧ h ∈ s'.owed ∧ h ∈ s'.served ∧ s'.queue = t := by
  simp [handoff, hq]

/-- **Waiters ahead only leave.** If `r` waits behind the requests `pre`,
then after any step `r` was served, or left the queue (cancelled), or still
waits behind requests `pre'` drawn from `pre`, in order. -/
theorem position_never_grows {n : Nat} {s t : Q}
    -- The invariant holds before the step.
    (hinv : Inv n s)
    -- One step.
    (hstep : Step s t)
    {pre post : List Nat} {r : Nat}
    -- `r` waits behind `pre`.
    (hq : s.queue = pre ++ r :: post) :
    r ∈ t.served ∨ r ∉ t.queue ∨
      ∃ pre' post', t.queue = pre' ++ r :: post' ∧ pre'.Sublist pre := by
  -- What a handoff does to the queue: it serves the head, which is `r`
  -- itself when nobody is ahead, or else one of those ahead.
  have hand : ∀ u : Q, u.queue = pre ++ r :: post →
      r ∈ (handoff u).served ∨ ∃ pre' post', (handoff u).queue = pre' ++ r :: post' ∧
        pre'.Sublist pre := by
    intro u hu
    cases pre with
    | nil => left; simp [handoff, hu]
    | cons p pre'' =>
      right
      exact ⟨pre'', post, by simp [handoff, hu], List.sublist_cons_self p pre''⟩
  cases hstep with
  | fast x _ hq0 _ =>
    -- Nobody waits on the fast path, yet `r` waits: impossible.
    simp [hq0] at hq
  | enqueue x _ _ =>
    -- `x` joins behind `r`: nobody new ahead.
    right; right
    exact ⟨pre, post ++ [x], by simp [hq], List.Sublist.refl _⟩
  | release x _ =>
    -- The owner's permit comes back through a handoff.
    rcases hand { s with owners := s.owners.erase x } hq with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  | wake x _ =>
    right; right; exact ⟨pre, post, hq, List.Sublist.refl _⟩
  | poll x _ _ =>
    right; right; exact ⟨pre, post, hq, List.Sublist.refl _⟩
  | cancelWaiting x hx =>
    -- The queue has no repeats.
    have hqn : s.queue.Nodup := (List.nodup_append.1 hinv.core.line_nodup).2.1
    by_cases hxr : x = r
    · -- `r` itself left.
      subst hxr
      right; left
      exact List.Nodup.not_mem_erase hqn
    · right; right
      by_cases hxp : x ∈ pre
      · -- One of those ahead left.
        refine ⟨pre.erase x, post, ?_, List.erase_sublist⟩
        simp only [hq]
        exact List.erase_append_left _ hxp
      · -- Someone behind left.
        refine ⟨pre, post.erase x, ?_, List.Sublist.refl _⟩
        simp only [hq]
        rw [List.erase_append_right _ hxp, List.erase_cons_tail (by simpa using Ne.symm hxr)]
  | cancelHanded x _ =>
    -- The dropped waiter's permit comes back through a handoff.
    rcases hand { s with handed := s.handed.erase x, owed := s.owed.filter (· != x),
                         woken := s.woken.filter (· != x) } hq with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-- **Every handoff advances a waiter.** A permit coming back while `r`
waits behind `pre` serves `r`, or removes one of those ahead of it. So a
waiter that is not cancelled is served within `pre.length + 1` handoffs. -/
theorem handoff_advances {s : Q} {pre post : List Nat} {r : Nat}
    -- `r` waits behind `pre`.
    (hq : s.queue = pre ++ r :: post) :
    r ∈ (handoff s).served ∨
      ∃ pre' post', (handoff s).queue = pre' ++ r :: post' ∧ pre'.length < pre.length := by
  cases pre with
  -- Nobody ahead: `r` is the head, and is served.
  | nil => left; simp [handoff, hq]
  -- Someone ahead: the head is served, and one fewer is ahead.
  | cons p pre'' => right; exact ⟨pre'', post, by simp [handoff, hq], by simp⟩

/-! ## The RED cases -/

/-- The barging design: a release frees the permit and wakes the oldest
waiter (which stays queued and must retry), and the fast path ignores the
queue. -/
inductive StepBarge : Q → Q → Prop
  /-- The fast path takes a free permit even while others wait. -/
  | fast (s : Q) (r : Nat)
      -- `r` is a fresh request.
      (hr : r ∉ s.enq)
      -- A permit is free; nobody checks the queue.
      (hf : 0 < s.free) :
      StepBarge s { s with free := s.free - 1, owners := r :: s.owners,
                           enq := s.enq ++ [r], served := s.served ++ [r] }
  /-- As `Step.enqueue`. -/
  | enqueue (s : Q) (r : Nat)
      -- `r` is a fresh request.
      (hr : r ∉ s.enq)
      -- The fast path is shut.
      (hc : s.queue ≠ [] ∨ s.free = 0) :
      StepBarge s { s with queue := s.queue ++ [r], enq := s.enq ++ [r] }
  /-- The defect: the permit is freed, the head is only woken. -/
  | release (s : Q) (r : Nat) (h : Nat) (t : List Nat)
      -- `r` owns a permit.
      (hr : r ∈ s.owners)
      -- `h` is the oldest waiter.
      (hq : s.queue = h :: t) :
      StepBarge s { s with owners := s.owners.erase r, free := s.free + 1,
                           woken := s.woken ++ [h] }

/-- Request 1 owns the lock; request 2 waits. -/
def bargeWait : Q := ⟨0, [2], [1], [], [], [], [1, 2], [1]⟩
/-- Request 1 released: the lock is free and request 2 is woken but still
queued. -/
def bargeFreed : Q := ⟨1, [2], [], [], [], [2], [1, 2], [1]⟩
/-- Request 3 took the lock on the fast path ahead of request 2. -/
def barged : Q := ⟨0, [2], [3], [], [], [2], [1, 2, 3], [1, 3]⟩

/-- **`barging_breaks_fifo`.** Under the barging design, request 3, which
entered the line after request 2, is served while request 2 still waits:
the FIFO law of `fifo_served` fails. -/
theorem barging_breaks_fifo :
    StepBarge (init 1) ⟨0, [], [1], [], [], [], [1], [1]⟩ ∧
    StepBarge ⟨0, [], [1], [], [], [], [1], [1]⟩ bargeWait ∧
    StepBarge bargeWait bargeFreed ∧
    StepBarge bargeFreed barged ∧
    [2, 3].Sublist barged.enq ∧ 3 ∈ barged.served ∧ 2 ∈ barged.queue := by
  -- Request 1 takes the lock, 2 queues, 1 releases (freeing the lock), and
  -- 3 takes it on the fast path; each fact is checked by computation.
  refine ⟨StepBarge.fast (init 1) 1 (by decide) (by decide),
    StepBarge.enqueue _ 2 (by decide) (by decide),
    StepBarge.release bargeWait 1 2 [] (by decide) (by decide),
    StepBarge.fast bargeFreed 3 (by decide) (by decide),
    by decide, by decide, by decide⟩

/-- The wake-before-handoff design: a release wakes the oldest waiter
first and hands it the permit in a later step; a woken waiter that finds no
permit registers its waker again. -/
inductive StepWake : Q → Q → Prop
  /-- As `Step.fast`. -/
  | fast (s : Q) (r : Nat)
      -- `r` is a fresh request.
      (hr : r ∉ s.enq)
      -- Nobody waits.
      (hq : s.queue = [])
      -- A permit is free.
      (hf : 0 < s.free) :
      StepWake s { s with free := s.free - 1, owners := r :: s.owners,
                          enq := s.enq ++ [r], served := s.served ++ [r] }
  /-- As `Step.enqueue`. -/
  | enqueue (s : Q) (r : Nat)
      -- `r` is a fresh request.
      (hr : r ∉ s.enq)
      -- The fast path is shut.
      (hc : s.queue ≠ [] ∨ s.free = 0) :
      StepWake s { s with queue := s.queue ++ [r], enq := s.enq ++ [r] }
  /-- The defect: the owner's guard drops and the oldest waiter is woken;
  the permit is in transit, not yet handed. -/
  | release (s : Q) (r h : Nat) (t : List Nat)
      -- `r` owns a permit.
      (hr : r ∈ s.owners)
      -- `h` is the oldest waiter.
      (hq : s.queue = h :: t) :
      StepWake s { s with owners := s.owners.erase r, woken := s.woken ++ [h] }
  /-- A permit in transit reaches the oldest waiter, with no wake. (The
  step is not tied to an earlier release; that only gives this defective
  design more behaviours, and the stranding below holds in all of them.) -/
  | grant (s : Q) (h : Nat) (t : List Nat)
      -- `h` is the oldest waiter.
      (hq : s.queue = h :: t) :
      StepWake s { s with queue := t, handed := s.handed ++ [h], served := s.served ++ [h] }
  /-- A woken waiter is polled, finds no permit, and registers its waker
  again: it is no longer woken. -/
  | repark (s : Q) (r : Nat)
      -- `r` was woken ...
      (hw : r ∈ s.woken)
      -- ... but holds no permit.
      (hh : r ∉ s.handed) :
      StepWake s { s with woken := s.woken.filter (· != r) }
  /-- As `Step.wake`. -/
  | wake (s : Q) (r : Nat)
      -- `r` is owed a wake.
      (hr : r ∈ s.owed) :
      StepWake s { s with owed := s.owed.filter (· != r), woken := s.woken ++ [r] }
  /-- As `Step.poll`. -/
  | poll (s : Q) (r : Nat)
      -- `r` was woken ...
      (hw : r ∈ s.woken)
      -- ... and holds its permit.
      (hh : r ∈ s.handed) :
      StepWake s { s with woken := s.woken.filter (· != r), handed := s.handed.erase r,
                          owners := r :: s.owners }
  /-- As `Step.cancelWaiting`. -/
  | cancelWaiting (s : Q) (r : Nat)
      -- `r` waits.
      (hr : r ∈ s.queue) :
      StepWake s { s with queue := s.queue.erase r }

/-- Any number of `StepWake` steps. -/
inductive StepsWake : Q → Q → Prop
  /-- No step at all. -/
  | refl (s : Q) : StepsWake s s
  /-- Some steps, then one more. -/
  | tail {s t u : Q} : StepsWake s t → StepWake t u → StepsWake s u

/-- Request 1 owns the lock; request 2 waits. -/
def wakeWait : Q := ⟨0, [2], [1], [], [], [], [1, 2], [1]⟩
/-- Request 1 released; request 2 is woken, the permit in transit. -/
def wakeEarly : Q := ⟨0, [2], [], [], [], [2], [1, 2], [1]⟩
/-- Request 2 was polled, found nothing, and registered its waker again. -/
def wakeReparked : Q := ⟨0, [2], [], [], [], [], [1, 2], [1]⟩
/-- The permit reaches request 2, with nobody left to wake it. -/
def wakeLost : Q := ⟨0, [], [], [2], [], [], [1, 2], [1, 2]⟩

/-- Request 2 is stuck: it holds the permit, left the queue, is not woken,
is owed no wake and is not an owner. -/
abbrev Stuck2 (s : Q) : Prop :=
  2 ∈ s.enq ∧ 2 ∉ s.queue ∧ 2 ∉ s.woken ∧ 2 ∉ s.owed ∧ 2 ∉ s.owners

/-- Under the wake-before-handoff design nothing ever wakes a stuck request
2: wakes only ever go to the head of the queue or to owed requests. -/
theorem stuck2_step {s t : Q}
    -- Request 2 is stuck before the step.
    (hs : Stuck2 s)
    -- One step of the wake-before-handoff design.
    (hstep : StepWake s t) : Stuck2 t := by
  obtain ⟨he, hq, hw, ho, hown⟩ := hs
  cases hstep with
  | fast r hr _ _ =>
    -- The fresh request is not 2, which entered the line already.
    have : r ≠ 2 := fun h => hr (h ▸ he)
    refine ⟨List.mem_append.2 (Or.inl he), hq, hw, ho, ?_⟩
    simp only [List.mem_cons, not_or]
    exact ⟨Ne.symm this, hown⟩
  | enqueue r hr _ =>
    have : r ≠ 2 := fun h => hr (h ▸ he)
    refine ⟨List.mem_append.2 (Or.inl he), ?_, hw, ho, hown⟩
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hq, Ne.symm this⟩
  | release r h t _ hq0 =>
    -- The woken head is not 2, which is not queued.
    have : h ≠ 2 := fun e => hq (by rw [hq0, e]; exact List.mem_cons_self)
    refine ⟨he, hq, ?_, ho, fun hm => hown (List.mem_of_mem_erase hm)⟩
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hw, Ne.symm this⟩
  | grant h t hq0 =>
    refine ⟨he, fun hm => hq (by rw [hq0]; exact List.mem_cons_of_mem _ hm), hw, ho, hown⟩
  | repark r _ _ =>
    exact ⟨he, hq, fun hm => hw (mem_of_mem_filter hm), ho, hown⟩
  | wake r hr =>
    -- The woken request was owed, so it is not 2.
    have : r ≠ 2 := fun e => ho (e ▸ hr)
    refine ⟨he, hq, ?_, fun hm => ho (mem_of_mem_filter hm), hown⟩
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hw, Ne.symm this⟩
  | poll r hwr _ =>
    -- The polled request was woken, so it is not 2.
    have : r ≠ 2 := fun e => hw (e ▸ hwr)
    refine ⟨he, hq, fun hm => hw (mem_of_mem_filter hm), ho, ?_⟩
    simp only [List.mem_cons, not_or]
    exact ⟨Ne.symm this, hown⟩
  | cancelWaiting r _ =>
    exact ⟨he, fun hm => hq (List.mem_of_mem_erase hm), hw, ho, hown⟩

/-- **`wake_before_handoff_strands`.** Under the wake-before-handoff
design, request 2 is woken before the permit reaches it, polled in between,
and then handed the permit with no wake: it holds the permit and, whatever
steps follow, is never woken and never becomes an owner. The design's
`no_lost_handoff` fails. -/
theorem wake_before_handoff_strands :
    StepWake wakeWait wakeEarly ∧ StepWake wakeEarly wakeReparked ∧
    StepWake wakeReparked wakeLost ∧
    2 ∈ wakeLost.handed ∧ 2 ∉ wakeLost.owed ∧ 2 ∉ wakeLost.woken ∧
    ∀ t, StepsWake wakeLost t → 2 ∉ t.woken ∧ 2 ∉ t.owners := by
  refine ⟨StepWake.release wakeWait 1 2 [] (by decide) (by decide),
    StepWake.repark wakeEarly 2 (by decide) (by decide),
    StepWake.grant wakeReparked 2 [] (by decide),
    by decide, by decide, by decide, ?_⟩
  intro t ht
  -- Stuck at the start, stuck after every step.
  have : Stuck2 t := by
    induction ht with
    | refl => exact ⟨by decide, by decide, by decide, by decide, by decide⟩
    | tail _ hstep ih => exact stuck2_step ih hstep
  exact ⟨this.2.2.1, this.2.2.2.2⟩

/-- The design, plus the defect: a waiter dropped after it was handed a
permit leaves without passing the permit on. -/
inductive StepNoPass : Q → Q → Prop
  /-- Every step of the design. -/
  | step {s t : Q}
      -- A step of the design.
      (h : Step s t) : StepNoPass s t
  /-- The defect: the handed permit leaves with the dropped waiter. -/
  | cancelDrop (s : Q) (r : Nat)
      -- `r` was handed a permit.
      (hr : r ∈ s.handed) :
      StepNoPass s { s with handed := s.handed.erase r, owed := s.owed.filter (· != r),
                            woken := s.woken.filter (· != r) }

/-- Request 1 owns the lock; requests 2 and 3 wait. -/
def passWait : Q := ⟨0, [2, 3], [1], [], [], [], [1, 2, 3], [1]⟩
/-- Request 1 released: request 2 is handed the lock and owed a wake. -/
def passHanded : Q := ⟨0, [3], [], [2], [2], [], [1, 2, 3], [1, 2]⟩
/-- Request 2 was dropped and kept the lock: nobody holds it, nothing is
free, and request 3 waits. -/
def passLost : Q := ⟨0, [3], [], [], [], [], [1, 2, 3], [1, 2]⟩

/-- Nobody holds, nothing is free or owed, and the served list is fixed. -/
abbrev Dead (s : Q) : Prop :=
  s.free = 0 ∧ s.owners = [] ∧ s.handed = [] ∧ s.owed = [] ∧ s.woken = [] ∧ s.served = [1, 2]

/-- No step of the design leaves a dead state: there is no permit to hand
to anyone. -/
theorem dead_step {s t : Q}
    -- The state is dead before the step.
    (hd : Dead s)
    -- One step of the design.
    (hstep : Step s t) : Dead t := by
  obtain ⟨hf, ho, hh, hw, hk, hs⟩ := hd
  cases hstep with
  -- Each step that would serve anyone needs a free permit or a holder.
  | fast _ _ _ hf' => omega
  | enqueue => exact ⟨hf, ho, hh, hw, hk, hs⟩
  | release r hr => simp [ho] at hr
  | wake r hr => simp [hw] at hr
  | poll r hwr _ => simp [hk] at hwr
  | cancelWaiting => exact ⟨hf, ho, hh, hw, hk, hs⟩
  | cancelHanded r hr => simp [hh] at hr

/-- **`cancel_without_pass_on_strands`.** When request 2 is dropped after
being handed the lock and does not pass it on, the lock is lost (the count
of `Inv` fails: nothing free, nobody holding), and request 3 is never
served, whatever steps of the design follow. -/
theorem cancel_without_pass_on_strands :
    StepNoPass passWait passHanded ∧ StepNoPass passHanded passLost ∧
    passLost.free + passLost.owners.length + passLost.handed.length = 0 ∧
    ∀ t, Steps passLost t → 3 ∉ t.served := by
  refine ⟨StepNoPass.step (Step.release passWait 1 (by decide)),
    StepNoPass.cancelDrop passHanded 2 (by decide), by decide, ?_⟩
  intro t ht
  -- Dead at the start, dead after every step; 3 is not among [1, 2].
  have : Dead t := by
    induction ht with
    | refl => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    | tail _ hstep ih => exact dead_step ih hstep
  rw [this.2.2.2.2.2]
  decide

end Regolith.SyncFifo
