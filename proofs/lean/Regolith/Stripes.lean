/-!
# Stripes: compaction under live snapshots (plan 4.8, E5)

This file backs the TLA+ model `proofs/tla/StripeCompaction.tla`,
invariants `SnapshotReadsKept`, `HeadKept` and `NewestKept`
(configurations `MC_StripeCompaction_*`).

Compaction reduces the versions of each key while snapshots are live. The
live snapshots cut the sequence line into stripes: two neighbouring
versions share a stripe when no live snapshot sits at or above the older
one and below the newer one. Inside a stripe only the newest state is
visible to any reader, so the engine (`Stripes::reduce_group` in
`src/engine/compaction/stripes.rs`) drops what is beneath the stripe's
newest value or deletion, folds the operands over it into one value, and
folds an operand-only stripe into one operand when the merge operator has
an exact `partial_merge`.

What is proved, in plain words:

1. `combine_reads`: replacing two neighbours of one stripe by the one
   entry they reduce to changes no read at a live snapshot or at the head,
   on top of whatever the older versions resolve to.
2. `reduce_reads`: so the whole reduction changes no such read.
   `live_snapshot_reads_kept`, `head_reads_kept` and `window_reads_kept`
   specialise it: a compaction of any window of a key's versions, with
   newer versions above it and older ones below, changes no read at a
   live snapshot, nor at the head.
3. `reduce_keeps_newest`: the newest version keeps its sequence, so commit
   validation sees the same newest write.
4. `inexact_fold_breaks_reads`: folding an operand-only stripe with a
   `partial_merge` that is not exact (a rounding sum, as with floating
   point) changes a read. This is the RED configuration
   `MC_StripeCompaction_Red_InexactFold`.
5. `unlisted_snapshot_breaks_reads`: a snapshot missing from the list the
   stripes are cut at loses the version it reads. That is what the E5
   capture window (`MC_StripeCompaction_Red_CaptureEarly`) and a
   stripe-blind reduction (`MC_StripeCompaction_Red_IgnoreStripes`) do.

The compaction filter (TLA+ `Filter = "Expire"`) is not a separate case
here: the reduction with a filter is the reduction without one applied to
the versions with the filter's decisions made in place, so `reduce_reads`
applies to that list.

How to read the Lean: `def` defines a function or a property, `theorem`
states a fact and its proof follows `:= by`. Lines starting with `--` are
comments.
-/

namespace Regolith.Stripes

/-! ## Versions and reads -/

/-- What one version of a key does. Values and operands are natural
numbers; only how they combine matters. -/
inductive Op where
  /-- A put of a value. -/
  | put (v : Nat)
  /-- A deletion. -/
  | del
  /-- A merge operand. -/
  | merge (x : Nat)
  deriving DecidableEq, Repr

/-- One version of one key: the sequence it was written at and what it
does. A key's versions are listed newest first. -/
structure Entry where
  /-- The sequence the version was written at. -/
  seq : Nat
  /-- What it does. -/
  op : Op
  deriving DecidableEq, Repr

/-- A merge operator. -/
structure MergeOp where
  /-- `step base x`: apply operand `x` to the value beneath it, `none`
  when there is none (a deletion or nothing). `full_merge` is this applied
  to the operands one at a time, oldest first. -/
  step : Option Nat → Nat → Nat
  /-- `partial_merge`, when the operator has one: combine an older operand
  `x` and a newer operand `y` into one. -/
  pm : Option (Nat → Nat → Nat)

/-- `Exact m`: the operator's `partial_merge`, if it has one, agrees with
applying the two operands one at a time, on top of every base. An
operator that is not exact must omit it (plan 3.3). -/
def Exact (m : MergeOp) : Prop :=
  ∀ p, m.pm = some p → ∀ (b : Option Nat) (x y : Nat), m.step b (p x y) = m.step (some (m.step b x)) y

/-- `applyOn m es r`: what a read gets from the versions `es` (newest
first) on top of the base `r` that older versions resolve to. A put or a
deletion ends the read; an operand applies to what lies beneath it. -/
def applyOn (m : MergeOp) : List Entry → Option Nat → Option Nat
  -- No version: the base.
  | [], r => r
  -- A put answers its value, whatever lies beneath.
  | ⟨_, .put v⟩ :: _, _ => some v
  -- A deletion answers "absent", whatever lies beneath.
  | ⟨_, .del⟩ :: _, _ => none
  -- An operand applies to what the older versions resolve to.
  | ⟨_, .merge x⟩ :: rest, r => some (m.step (applyOn m rest r) x)

/-- The versions a snapshot at `s` sees: those written at or below it. -/
def vis (s : Nat) (es : List Entry) : List Entry := es.filter fun e => decide (e.seq ≤ s)

/-- A point read at snapshot `s` of a key whose versions are `es`. -/
def read (m : MergeOp) (s : Nat) (es : List Entry) : Option Nat := applyOn m (vis s es) none

/-- A read of `xs ++ ys` is a read of `xs` on top of the read of `ys`:
older versions matter only through what they resolve to. -/
theorem applyOn_append (m : MergeOp) :
    ∀ (xs ys : List Entry) (r : Option Nat), applyOn m (xs ++ ys) r = applyOn m xs (applyOn m ys r)
  | [], _, _ => rfl
  | ⟨_, .put _⟩ :: _, _, _ => rfl
  | ⟨_, .del⟩ :: _, _, _ => rfl
  | ⟨_, .merge x⟩ :: rest, ys, r => by
    -- The operand applies to the same thing on both sides, by induction.
    simp only [List.cons_append, applyOn]
    rw [applyOn_append m rest ys r]

/-- Two lists of versions that resolve alike on every base still do after
the same version is put in front of both. -/
theorem applyOn_cons_congr (m : MergeOp) (a : Entry) {xs ys : List Entry}
    -- `xs` and `ys` resolve alike on every base.
    (h : ∀ r, applyOn m xs r = applyOn m ys r) (r : Option Nat) :
    applyOn m (a :: xs) r = applyOn m (a :: ys) r := by
  obtain ⟨s, o⟩ := a
  cases o with
  | put v => rfl
  | del => rfl
  | merge x =>
    -- The operand applies to what each side resolves to, which agree.
    simp only [applyOn]
    rw [h r]

/-! ## Stripes and the reduction -/

/-- `sameStripe L a b`: the newer version `a` and the older version `b`
share a stripe under the live snapshots `L`: `b` is older, and no live
snapshot is at or above `b`'s sequence and below `a`'s. -/
def sameStripe (L : List Nat) (a b : Entry) : Bool :=
  decide (b.seq < a.seq) && L.all fun l => !(decide (b.seq ≤ l) && decide (l < a.seq))

/-- What `sameStripe` says, as two facts. -/
theorem sameStripe_spec {L : List Nat} {a b : Entry} (h : sameStripe L a b = true) :
    b.seq < a.seq ∧ ∀ l ∈ L, ¬ (b.seq ≤ l ∧ l < a.seq) := by
  simp only [sameStripe, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
  obtain ⟨hlt, hall⟩ := h
  refine ⟨hlt, fun l hl ⟨h1, h2⟩ => ?_⟩
  -- Each live snapshot fails one of the two comparisons.
  rcases hall l hl with h | h
  · exact h h1
  · exact h h2

/-- `combine m a b`: the one version that replaces the newer `a` and the
older `b` of one stripe, when the reduction folds them; `none` when it
keeps both.

* A put or deletion on top hides `b`: it stays, `b` goes.
* An operand on a put or a deletion folds into a put of the result, at
  the operand's sequence (`full_merge` with a base).
* Two operands fold into one through `partial_merge`, when the operator
  has one; otherwise both stay. -/
def combine (m : MergeOp) (a b : Entry) : Option Entry :=
  match a with
  | ⟨_, .put _⟩ => some a
  | ⟨_, .del⟩ => some a
  | ⟨s, .merge y⟩ =>
    match b with
    | ⟨_, .put v⟩ => some ⟨s, .put (m.step (some v) y)⟩
    | ⟨_, .del⟩ => some ⟨s, .put (m.step none y)⟩
    | ⟨_, .merge x⟩ =>
      match m.pm with
      | some p => some ⟨s, .merge (p x y)⟩
      | none => none

/-- The folded version keeps the newer version's sequence. -/
theorem combine_seq {m : MergeOp} {a b c : Entry} (h : combine m a b = some c) : c.seq = a.seq := by
  obtain ⟨sa, oa⟩ := a
  obtain ⟨sb, ob⟩ := b
  cases oa <;> cases ob <;> simp only [combine, Option.some.injEq] at h
  all_goals first
    | (subst h; rfl)
    | (cases hp : m.pm <;> simp only [hp, reduceCtorEq, Option.some.injEq] at h
       subst h; rfl)

/-- **One fold changes no read.** Let `a` and `b` share a stripe and fold
into `c`, with an exact operator. A read at a live snapshot `s`, or at any
`s` at or above `a`'s sequence (the head), gets the same from `c` as from
`a` then `b`, whatever follows and whatever base lies beneath. -/
theorem combine_reads {m : MergeOp} (hm : Exact m) {L : List Nat} {a b c : Entry} {s : Nat}
    -- `a` and `b` share a stripe.
    (hss : sameStripe L a b = true)
    -- They fold into `c`.
    (hc : combine m a b = some c)
    -- The read is at a live snapshot, or at or above `a`.
    (hs : s ∈ L ∨ a.seq ≤ s) (rest : List Entry) (r : Option Nat) :
    applyOn m (vis s (c :: rest)) r = applyOn m (vis s (a :: b :: rest)) r := by
  obtain ⟨hba, hno⟩ := sameStripe_spec hss
  have hcs := combine_seq hc
  -- No live snapshot falls between `b` and `a`, so the read sees both or
  -- neither.
  have hcase : s < b.seq ∨ a.seq ≤ s := by
    rcases hs with hsL | hle
    · have := hno s hsL
      omega
    · exact Or.inr hle
  rcases hcase with hlt | hle
  · -- Neither is visible, nor is `c`, which has `a`'s sequence.
    have h1 : ¬ c.seq ≤ s := by omega
    have h2 : ¬ a.seq ≤ s := by omega
    have h3 : ¬ b.seq ≤ s := by omega
    simp only [vis, List.filter_cons, h1, h2, h3, decide_false, Bool.false_eq_true, ite_false]
  · -- All three are visible: compare what each side resolves to.
    have h1 : c.seq ≤ s := by omega
    have h3 : b.seq ≤ s := by omega
    simp only [vis, List.filter_cons, h1, hle, h3, decide_true, ite_true]
    generalize List.filter (fun e => decide (e.seq ≤ s)) rest = R
    obtain ⟨sa, oa⟩ := a
    obtain ⟨sb, ob⟩ := b
    cases oa with
    | put v =>
      -- A put on top: `c` is `a`, and both read its value.
      simp only [combine, Option.some.injEq] at hc
      subst hc
      rfl
    | del =>
      -- A deletion on top: `c` is `a`, and both read "absent".
      simp only [combine, Option.some.injEq] at hc
      subst hc
      rfl
    | merge y =>
      cases ob with
      | put v =>
        -- The operand folded onto the put: both read `step (some v) y`.
        simp only [combine, Option.some.injEq] at hc
        subst hc
        rfl
      | del =>
        -- The operand folded onto the deletion: both read `step none y`.
        simp only [combine, Option.some.injEq] at hc
        subst hc
        rfl
      | merge x =>
        -- Two operands folded by `partial_merge`: exactness says applying
        -- `p x y` equals applying `x` then `y`, on the same base.
        cases hp : m.pm with
        | none => simp only [combine, hp, reduceCtorEq] at hc
        | some p =>
          simp only [combine, hp, Option.some.injEq] at hc
          subst hc
          simp only [applyOn]
          rw [hm p hp]

/-- `push m L a out`: put the newer version `a` on top of the already
reduced older versions `out`, folding it into the first of them while
they share a stripe and fold. -/
def push (m : MergeOp) (L : List Nat) (a : Entry) : List Entry → List Entry
  | [] => [a]
  | b :: out =>
    if sameStripe L a b then
      match combine m a b with
      | some c => push m L c out
      | none => a :: b :: out
    else a :: b :: out

/-- `reduce m L es`: the reduction of a key's versions `es` (newest
first), built from the oldest up. Within each stripe this drops what lies
beneath the newest put or deletion, folds the operands over it into one
put, and folds an operand-only stripe into one operand when `partial_merge`
exists, which is what `Stripes::reduce_stripe` does. -/
def reduce (m : MergeOp) (L : List Nat) : List Entry → List Entry
  | [] => []
  | a :: rest => push m L a (reduce m L rest)

/-- Pushing a version changes no read at a live snapshot or at or above
that version, whatever base lies beneath. -/
theorem push_reads {m : MergeOp} (hm : Exact m) {L : List Nat} {s : Nat} :
    ∀ (out : List Entry) (a : Entry), (s ∈ L ∨ a.seq ≤ s) →
      ∀ r, applyOn m (vis s (push m L a out)) r = applyOn m (vis s (a :: out)) r
  | [], _, _, _ => rfl
  | b :: out, a, hs, r => by
    simp only [push]
    split
    · rename_i hss
      split
      · -- `a` and `b` fold into `c`: push `c` on, then undo the fold.
        rename_i c hc
        have hcs := combine_seq hc
        have hs' : s ∈ L ∨ c.seq ≤ s := by rw [hcs]; exact hs
        rw [push_reads hm out c hs' r]
        exact combine_reads hm hss hc hs out r
      · -- No fold: the lists are the same.
        rfl
    · -- Different stripes: the lists are the same.
      rfl

/-- **The reduction changes no read at a live snapshot or at the head.**
For every snapshot `s` in the live list `L`, and every `s` at or above
every version, the reduced versions read on top of any base exactly as
the versions did. -/
theorem reduce_reads {m : MergeOp} (hm : Exact m) {L : List Nat} {s : Nat} :
    ∀ (es : List Entry), (s ∈ L ∨ ∀ e ∈ es, e.seq ≤ s) →
      ∀ r, applyOn m (vis s (reduce m L es)) r = applyOn m (vis s es) r
  | [], _, _ => rfl
  | a :: rest, hs, r => by
    -- The condition holds for `a` and for the older versions.
    have ha : s ∈ L ∨ a.seq ≤ s := by
      rcases hs with h | h
      · exact Or.inl h
      · exact Or.inr (h a List.mem_cons_self)
    have hrest : s ∈ L ∨ ∀ e ∈ rest, e.seq ≤ s := by
      rcases hs with h | h
      · exact Or.inl h
      · exact Or.inr fun e he => h e (List.mem_cons_of_mem _ he)
    -- The older versions reduce without changing a read, by induction.
    have ih := reduce_reads hm rest hrest
    -- Pushing `a` changes no read either.
    simp only [reduce]
    rw [push_reads hm _ a ha r]
    -- With `a` in front of both, what follows reads alike, so the whole does.
    by_cases hv : a.seq ≤ s
    · simp only [vis, List.filter_cons, hv, decide_true, ite_true]
      exact applyOn_cons_congr m a ih r
    · simp only [vis, List.filter_cons, hv, decide_false, Bool.false_eq_true, ite_false]
      exact ih r

/-- At a live snapshot, a read of the reduced versions answers what it
answered before. -/
theorem live_snapshot_reads_kept {m : MergeOp} (hm : Exact m) {L : List Nat} {s : Nat}
    -- `s` is a live snapshot.
    (hs : s ∈ L) (es : List Entry) :
    read m s (reduce m L es) = read m s es :=
  reduce_reads hm es (Or.inl hs) none

/-- At the head (any `s` at or above every version), a read of the
reduced versions answers what it answered before. -/
theorem head_reads_kept {m : MergeOp} (hm : Exact m) (L : List Nat) {s : Nat} {es : List Entry}
    -- `s` is at or above every version.
    (hs : ∀ e ∈ es, e.seq ≤ s) :
    read m s (reduce m L es) = read m s es :=
  reduce_reads hm es (Or.inr hs) none

/-- **A compaction window.** The inputs of a compaction hold a run `mid`
of a key's versions; newer versions `above` (memtable, newer files) and
older ones `below` (deeper files) lie outside it. Reducing `mid` changes
no read at a live snapshot, nor at any `s` at or above every input. This
covers an operand-only stripe whose base lies below the window. -/
theorem window_reads_kept {m : MergeOp} (hm : Exact m) {L : List Nat} {s : Nat}
    (above mid below : List Entry)
    -- A live snapshot, or a read at or above every input.
    (hs : s ∈ L ∨ ∀ e ∈ mid, e.seq ≤ s) :
    read m s (above ++ reduce m L mid ++ below) = read m s (above ++ mid ++ below) := by
  -- A read of the three parts is a read of `above` on top of a read of
  -- the window on top of a read of `below`; only the middle changed.
  have h := reduce_reads hm mid hs (applyOn m (vis s below) none)
  simp only [read, vis, List.filter_append, applyOn_append] at h ⊢
  rw [h]

/-- Pushing a version leaves a list headed by a version of the same
sequence. -/
theorem push_head (m : MergeOp) (L : List Nat) :
    ∀ (out : List Entry) (a : Entry), ∃ e tl, push m L a out = e :: tl ∧ e.seq = a.seq
  | [], a => ⟨a, [], rfl, rfl⟩
  | b :: out, a => by
    simp only [push]
    split
    · split
      · -- Folded into `c`, which keeps `a`'s sequence.
        rename_i c hc
        obtain ⟨e, tl, he, hseq⟩ := push_head m L out c
        exact ⟨e, tl, he, hseq.trans (combine_seq hc)⟩
      · exact ⟨a, b :: out, rfl, rfl⟩
    · exact ⟨a, b :: out, rfl, rfl⟩

/-- **The newest version keeps its sequence.** The reduction of a key's
versions, newest first, starts with a version at the newest one's
sequence. -/
theorem reduce_keeps_newest (m : MergeOp) (L : List Nat) (a : Entry) (rest : List Entry) :
    ∃ e tl, reduce m L (a :: rest) = e :: tl ∧ e.seq = a.seq :=
  push_head m L _ a

/-! ## The RED cases -/

/-- A sum that rounds to an even number after every addition, as a
floating-point sum rounds: adding 1 to an even total is lost. Its
`partial_merge` adds the operands first, which is not exact. -/
def roundingSum : MergeOp where
  step b x := 2 * ((b.getD 0 + x) / 2)
  pm := some fun x y => x + y

/-- The rounding sum's `partial_merge` is not exact: on nothing, `1` then
`1` gives `0`, but `1 + 1` gives `2`. -/
theorem roundingSum_not_exact : ¬ Exact roundingSum := by
  intro h
  have := h (fun x y => x + y) rfl none 1 1
  simp [roundingSum] at this

/-- **`inexact_fold_breaks_reads`.** Two operands of 1 over nothing, with
no live snapshot between them: the head reads `0` (each addition rounds
away). Folding the operand-only stripe with the inexact `partial_merge`
leaves one operand of `2`, and the head reads `2`. -/
theorem inexact_fold_breaks_reads :
    read roundingSum 2 [⟨2, .merge 1⟩, ⟨1, .merge 1⟩] = some 0 ∧
    reduce roundingSum [] [⟨2, .merge 1⟩, ⟨1, .merge 1⟩] = [⟨2, .merge 2⟩] ∧
    read roundingSum 2 (reduce roundingSum [] [⟨2, .merge 1⟩, ⟨1, .merge 1⟩]) = some 2 := by
  decide

/-- The same operator with no `partial_merge` (plan 3.3: an operator that
is not exact omits it) is exact vacuously, and its operand-only stripe
stays as written. -/
theorem roundingSum_without_pm :
    Exact { roundingSum with pm := none } ∧
    reduce { roundingSum with pm := none } [] [⟨2, .merge 1⟩, ⟨1, .merge 1⟩] =
      [⟨2, .merge 1⟩, ⟨1, .merge 1⟩] := by
  refine ⟨fun p hp => ?_, by decide⟩
  -- There is no `partial_merge` to be inexact.
  cases hp

/-- A plain sum whose `partial_merge` adds the operands: exact. -/
def plainSum : MergeOp where
  step b x := b.getD 0 + x
  pm := some fun x y => x + y

/-- The plain sum's `partial_merge` is exact. -/
theorem plainSum_exact : Exact plainSum := by
  intro p hp b x y
  simp only [plainSum, Option.some.injEq] at hp
  subst hp
  simp [plainSum, Nat.add_assoc]

/-- **`unlisted_snapshot_breaks_reads`.** A snapshot at 1 reads the put of
5. Reduced under a list that misses it (the E5 window, or a reduction
blind to stripes), the put of 7 hides the put of 5 and the snapshot reads
"absent". Under a list that holds it, the put of 5 stays. -/
theorem unlisted_snapshot_breaks_reads :
    read plainSum 1 [⟨2, .put 7⟩, ⟨1, .put 5⟩] = some 5 ∧
    read plainSum 1 (reduce plainSum [] [⟨2, .put 7⟩, ⟨1, .put 5⟩]) = none ∧
    read plainSum 1 (reduce plainSum [1] [⟨2, .put 7⟩, ⟨1, .put 5⟩]) = some 5 := by
  decide

end Regolith.Stripes
