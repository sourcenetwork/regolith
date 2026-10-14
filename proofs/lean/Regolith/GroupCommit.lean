/-!
# GroupCommit: a group decides as committing its members one at a time

This file backs the TLA+ model `proofs/tla/GroupCommit.tla`, invariant
`SerialEquivalent` (configurations `MC_GroupCommit_Green` and
`MC_GroupCommit_Red_ViewOnly`). The same law is the decide stage of
`proofs/tla/CommitPipeline.tla` (invariant `NoLostUpdate`), where slot `i`
is validated against the slots below it decided to commit.

Group commit for optimistic transactions (plan 4.4, E10): a leader takes a
group of queued transactions and validates each, in queue order, against
the view it loaded plus the keys written by the members it accepted earlier
in the group. It never applies a member before deciding the next, so the
earlier members' versions are not in the view; the keys they write stand
for them.

TLC checks the protocol around this for a few transactions. The theorems
here hold for every group size, every view and every read and write set.

What is proved, in plain words:

1. `group_eq_serial`: if every member began at or before the last sequence
   drawn before the group, the group's verdicts equal those of committing
   the members one at a time, each validated against everything committed
   before it, earlier members included.
2. `early_check_split`: validating outside the mutex up to a horizon `h`,
   then under the mutex only the versions above `h`, decides exactly as
   validating everything at once.
3. `view_only_breaks_serial`: a leader that validates each member against
   the view alone lets two members write one key from one snapshot, where
   committing them one at a time aborts the second. This is the RED
   configuration as a concrete counterexample.

How to read the Lean: `def` defines a function or a property, `theorem`
states a fact and its proof follows `:= by`. Lines starting with `--` are
comments. Inside a proof, each step is commented with what it establishes.
-/

namespace Regolith.GroupCommit

/-! ## The objects -/

/-
Keys and sequence numbers are plain natural numbers (`Nat`), kept as `Nat`
rather than named aliases so that `omega` sees them as numbers. A version
is a pair `(key, sequence)`.
-/

/-- A transaction, as its commit sees it. -/
structure Txn where
  /-- The sequence its snapshot reads at. -/
  snap : Nat
  /-- The keys it read or writes: a newer version of any of them aborts it. -/
  touched : List Nat
  /-- The keys it writes. -/
  writes : List Nat

/-- `conflicts vs t`: the versions `vs` hold a version of a key `t` touched
at a sequence its snapshot does not see. -/
def conflicts (vs : List (Nat × Nat)) (t : Txn) : Bool :=
  vs.any fun v => t.touched.contains v.1 && decide (t.snap < v.2)

/-- One at a time: each transaction is validated against every version
committed before it, and an accepted one's writes land at the next
sequence before the next transaction is validated. `true` is a commit,
`false` an abort. -/
def serial : List (Nat × Nat) → Nat → List Txn → List Bool
  -- No transaction, no verdict.
  | _, _, [] => []
  | store, s, t :: rest =>
    if conflicts store t then
      -- An abort writes nothing.
      false :: serial store s rest
    else
      -- A commit's writes land at `s + 1`, ahead of the next transaction.
      true :: serial (t.writes.map (fun k => (k, s + 1)) ++ store) (s + 1) rest

/-- The leader's group: each member validated against the view plus the
keys `acc` written by members accepted earlier in the group. -/
def group (view : List (Nat × Nat)) : List Nat → List Txn → List Bool
  -- No member, no verdict.
  | _, [] => []
  | acc, t :: rest =>
    if conflicts view t || t.touched.any (fun k => acc.contains k) then
      -- A conflict with the view or with an earlier member: an abort.
      false :: group view acc rest
    else
      -- Accepted: its written keys join those later members check.
      true :: group view (t.writes ++ acc) rest

/-! ## The law -/

/-- Versions all newer than a member's snapshot conflict with it exactly
when they hold a key it touched: the snapshot test always passes. With
`acc` the keys those versions hold, that is the group's test of the
earlier members. -/
theorem conflicts_newer {extra : List (Nat × Nat)} {acc : List Nat} {t : Txn} {s0 : Nat}
    -- Every version in `extra` is above `s0`.
    (hseq : ∀ v ∈ extra, s0 < v.2)
    -- `acc` holds exactly the keys of the versions in `extra`.
    (hkeys : ∀ k, k ∈ acc ↔ ∃ v ∈ extra, v.1 = k)
    -- The member's snapshot is at or below `s0`.
    (hsnap : t.snap ≤ s0) :
    conflicts extra t = t.touched.any (fun k => acc.contains k) := by
  -- Two booleans are equal when each is true exactly when the other is.
  apply Bool.eq_iff_iff.mpr
  simp only [conflicts, List.any_eq_true, Bool.and_eq_true, List.contains_iff_mem,
    decide_eq_true_eq]
  constructor
  · -- A version of a touched key in `extra` puts that key in `acc`.
    rintro ⟨v, hv, hk, -⟩
    exact ⟨v.1, hk, (hkeys v.1).mpr ⟨v, hv, rfl⟩⟩
  · -- A touched key in `acc` has a version in `extra`, above the snapshot.
    rintro ⟨k, hk, hacc⟩
    obtain ⟨v, hv, rfl⟩ := (hkeys k).mp hacc
    have := hseq v hv
    exact ⟨v, hv, hk, by omega⟩

/-- The induction behind `group_eq_serial`. The one-at-a-time store is the
view plus the versions `extra` of the members accepted so far, all above
`s0` and holding exactly the keys `acc`; every member began at or below
`s0`; and the next sequence comes after `s`, which is at least `s0`. Then
the group and the one-at-a-time run give every remaining member the same
verdict. -/
theorem group_eq_serial_from (view : List (Nat × Nat)) (s0 : Nat) :
    ∀ (ts : List Txn) (extra : List (Nat × Nat)) (acc : List Nat) (s : Nat),
      -- The sequences drawn so far are at or above `s0`.
      s0 ≤ s →
      -- The accepted members' versions are above `s0`.
      (∀ v ∈ extra, s0 < v.2) →
      -- `acc` holds exactly the keys those versions hold.
      (∀ k, k ∈ acc ↔ ∃ v ∈ extra, v.1 = k) →
      -- Every remaining member began at or below `s0`.
      (∀ t ∈ ts, t.snap ≤ s0) →
      group view acc ts = serial (extra ++ view) s ts := by
  intro ts
  -- By induction on the remaining members.
  induction ts with
  | nil =>
    -- No member left: no verdict on either side.
    intro extra acc s _ _ _ _
    simp [group, serial]
  | cons t rest ih =>
    intro extra acc s hs hseq hkeys hsnaps
    -- The one-at-a-time test of `t` splits into the accepted members'
    -- versions, which `conflicts_newer` turns into the group's key test,
    -- and the view, which both sides test alike.
    have htest : conflicts (extra ++ view) t =
        (conflicts view t || t.touched.any (fun k => acc.contains k)) := by
      rw [← conflicts_newer hseq hkeys (hsnaps t List.mem_cons_self)]
      simp [conflicts, List.any_append, Bool.or_comm]
    -- The remaining members still began at or below `s0`.
    have hrest : ∀ u ∈ rest, u.snap ≤ s0 := fun u hu => hsnaps u (List.mem_cons_of_mem _ hu)
    simp only [group, serial, htest]
    by_cases hc : (conflicts view t || t.touched.any (fun k => acc.contains k)) = true
    · -- `t` aborts on both sides and writes nothing: the rest follow by
      -- induction from the same store and keys.
      simp only [hc, ite_true]
      exact congrArg (false :: ·) (ih extra acc s hs hseq hkeys hrest)
    · -- `t` commits on both sides. Its versions at `s + 1`, above `s0`,
      -- join `extra`, and its written keys join `acc`.
      simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ite_false]
      refine congrArg (true :: ·) ?_
      rw [← List.append_assoc]
      apply ih _ _ (s + 1) (by omega)
      · -- Every version is above `s0`: the new ones are at `s + 1`.
        intro v hv
        rcases List.mem_append.mp hv with hnew | hold
        · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hnew
          simp only
          omega
        · exact hseq v hold
      · -- The new keys are `t`'s writes, held by the new versions.
        intro k
        constructor
        · intro hk
          rcases List.mem_append.mp hk with hw | ha
          · exact ⟨(k, s + 1), List.mem_append_left _ (List.mem_map.mpr ⟨k, hw, rfl⟩), rfl⟩
          · obtain ⟨v, hv, hvk⟩ := (hkeys k).mp ha
            exact ⟨v, List.mem_append_right _ hv, hvk⟩
        · rintro ⟨v, hv, rfl⟩
          rcases List.mem_append.mp hv with hnew | hold
          · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hnew
            exact List.mem_append_left _ hk'
          · exact List.mem_append_right _ ((hkeys v.1).mpr ⟨v, hold, rfl⟩)
      · exact hrest

/-- **A group commit equals committing its members one at a time.** Take
any view, any group of members that all began at or before `s`, the last
sequence drawn before the group. Validating each member against the view
plus the keys written by members accepted earlier in the group gives every
member the verdict that committing them one at a time, in queue order,
gives it. -/
theorem group_eq_serial (view : List (Nat × Nat)) (ts : List Txn) (s : Nat)
    -- Every member began at or before the group's sequences.
    (hsnaps : ∀ t ∈ ts, t.snap ≤ s) :
    group view [] ts = serial view s ts := by
  -- The start of the induction: no accepted member, no versions, no keys.
  have := group_eq_serial_from view s ts [] [] s (Nat.le_refl s)
    (fun _ h => absurd h List.not_mem_nil) (fun k => by simp) hsnaps
  simpa using this

/-- **Validation outside the mutex.** For a member whose snapshot is at or
below `h`, the versions above its snapshot conflict exactly when those up
to `h` (checked before the mutex) or those above `h` (checked under it)
do. Splitting the check at `h` decides as checking everything at once. -/
theorem early_check_split (vs : List (Nat × Nat)) (t : Txn) (h : Nat)
    -- The horizon is sampled after the snapshot.
    (hsh : t.snap ≤ h) :
    conflicts vs t =
      (vs.any (fun v => t.touched.contains v.1 && decide (t.snap < v.2 ∧ v.2 ≤ h)) ||
        vs.any (fun v => t.touched.contains v.1 && decide (h < v.2))) := by
  -- Compare the two as statements: a version of a touched key above the
  -- snapshot is either at or below `h`, or above it (and then above the
  -- snapshot too, since the snapshot is at or below `h`).
  apply Bool.eq_iff_iff.mpr
  simp only [conflicts, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨v, hv, hk, hlt⟩
    by_cases hle : v.2 ≤ h
    · exact Or.inl ⟨v, hv, hk, hlt, hle⟩
    · exact Or.inr ⟨v, hv, hk, by omega⟩
  · rintro (⟨v, hv, hk, hlt, -⟩ | ⟨v, hv, hk, hgt⟩)
    · exact ⟨v, hv, hk, hlt⟩
    · exact ⟨v, hv, hk, by omega⟩

/-! ## The RED case: validating against the view alone -/

/-- Mutant ViewOnly: each member validated against the view alone, never
against the members accepted earlier in its group. -/
def viewOnly (view : List (Nat × Nat)) : List Txn → List Bool
  -- No member, no verdict.
  | [] => []
  -- The verdict ignores every other member.
  | t :: rest => (!conflicts view t) :: viewOnly view rest

/-- Two transactions that both began at sequence 0 and write key 1. -/
def twoWriters : List Txn := [⟨0, [1], [1]⟩, ⟨0, [1], [1]⟩]

/-- **`view_only_breaks_serial`.** Against an empty view, the view-only
leader commits both writers of key 1, a lost update; committing them one
at a time aborts the second, and so does the fixed group. -/
theorem view_only_breaks_serial :
    viewOnly [] twoWriters = [true, true] ∧
      serial [] 0 twoWriters = [true, false] ∧
      group [] [] twoWriters = [true, false] := by
  decide

end Regolith.GroupCommit
