/-!
# GroupCommit: a group decides as committing its members one at a time

## The story

Two threads commit at the same moment. Both read key 1 at snapshot 0, both
write key 1. If they commit one after the other, the second one notices that
key 1 changed after its snapshot and aborts, so the first one's write is not
lost. regolith commits them in one "group" to share one fsync, and the
leader checks the members one by one before writing anything. The first
member's write is not in the memtable yet when the second is checked (nothing
is applied until the whole group's log write is done), so a leader that looked
only at the memtable would let both commit and lose an update.

The code (`src/engine/commit/group.rs`) checks each member against the
memtable PLUS the writes of the members it accepted earlier in the same
group, and a plain write (`Db::put`, which is never checked) counts as an
accepted member. This file proves, for every group size, every view and every
read and write set, that this gives every member the verdict committing them
one at a time would give (`group_eq_serial`), and shows the leader that
forgets the earlier members breaking it (`view_only_breaks_serial`).

The check is also split in two (`src/engine/commit/early.rs`): before it
queues, a transaction checks itself on its own thread against the versions
up to a horizon `h` it sampled (and any newer ones the view already holds),
and the leader then checks only the versions above `h`. `early_check_split`
and `early_check_cover` prove the split decides as one check of every version,
and `early_conflict_final` that a conflict found early stays a conflict
however many versions land afterwards, which is why the early check may abort
at once.

This backs `proofs/tla/GroupCommit.tla`, invariant `SerialEquivalent`
(configurations `MC_GroupCommit_Green`, `MC_GroupCommit_Red_ViewOnly`,
`MC_GroupCommit_Red_TrustEarly`). TLC checks the concurrent protocol around
these laws for a few transactions; the theorems here hold for every size.

## How to read the Lean

`def` defines a function or a property. `theorem` states a fact; its proof
follows `:= by` as a list of tactic steps, each of which changes the goal (what
is left to prove). Every line carries a `--` comment saying what it does.
-/

-- Everything below lives in this namespace, so its names start with
-- `Regolith.GroupCommit`.
namespace Regolith.GroupCommit

/-! ## The objects -/

/-
Keys and sequence numbers are plain natural numbers (`Nat`). A version is a
pair `(key, sequence)`: "key k was written at sequence s".
-/

/-- One commit as the leader sees it (`TxnRequest` or a plain `WriteRequest`
in `src/engine/commit`). -/
structure Txn where
  -- The sequence its snapshot reads at (`Transaction::snapshot_seq`).
  snap : Nat
  -- The keys it read or writes: a newer version of any of them aborts it.
  touched : List Nat
  -- The keys it writes.
  writes : List Nat
  -- A plain write: never checked, always lands.
  plain : Bool

/-- `conflicts vs t`: among the versions `vs`, one is of a key `t` touched,
at a sequence `t`'s snapshot did not see. This is the commit check. -/
def conflicts (vs : List (Nat × Nat)) (t : Txn) : Bool :=
  -- Some version `v` is of a touched key and newer than the snapshot.
  vs.any fun v => t.touched.contains v.1 && decide (t.snap < v.2)

/-- One at a time: each commit is checked against every version committed
before it, earlier commits included, and an accepted one's writes land at
the next sequence before the next commit is checked. `true` means it
committed, `false` that it aborted. `s` is the last sequence handed out. -/
def serial : List (Nat × Nat) → Nat → List Txn → List Bool
  -- No commit left: no verdict.
  | _, _, [] => []
  -- The next commit `t`, then the `rest`.
  | store, s, t :: rest =>
    -- A transaction that conflicts aborts and writes nothing.
    if !t.plain && conflicts store t then
      -- Its verdict is false; the rest are checked against the same store.
      false :: serial store s rest
    else
      -- It lands: its writes go in at `s + 1`, ahead of the next commit.
      true :: serial (t.writes.map (fun k => (k, s + 1)) ++ store) (s + 1) rest

/-- The leader's group (`RegolithEngine::decide`): each member checked
against the `view` plus the keys `acc` written by members accepted earlier
in the group (the overlay). A plain member is accepted unchecked. -/
def group (view : List (Nat × Nat)) : List Nat → List Txn → List Bool
  -- No member left: no verdict.
  | _, [] => []
  -- The next member `t`, then the `rest`.
  | acc, t :: rest =>
    -- A transaction that conflicts with the view or with an earlier member.
    if !t.plain && (conflicts view t || t.touched.any (fun k => acc.contains k)) then
      -- Aborted: its keys do not join `acc`.
      false :: group view acc rest
    else
      -- Accepted: the keys it writes join those later members are checked
      -- against.
      true :: group view (t.writes ++ acc) rest

/-! ## The law -/

/-- Versions that are all newer than a member's snapshot conflict with it
exactly when they hold a key it touched: their sequences pass the snapshot
test always. With `acc` the keys those versions hold, that is the group's
test of the earlier members. -/
theorem conflicts_newer {extra : List (Nat × Nat)} {acc : List Nat} {t : Txn} {s0 : Nat}
    -- Every version in `extra` is above `s0`.
    (hseq : ∀ v ∈ extra, s0 < v.2)
    -- `acc` holds exactly the keys of the versions in `extra`.
    (hkeys : ∀ k, k ∈ acc ↔ ∃ v ∈ extra, v.1 = k)
    -- The member's snapshot is at or below `s0`.
    (hsnap : t.snap ≤ s0) :
    -- The version test equals the key test.
    conflicts extra t = t.touched.any (fun k => acc.contains k) := by
  -- Two booleans are equal when each is true exactly when the other is.
  apply Bool.eq_iff_iff.mpr
  -- Unfold both sides into "there is an element such that ...".
  simp only [conflicts, List.any_eq_true, Bool.and_eq_true, List.contains_iff_mem,
    decide_eq_true_eq]
  -- Prove the two directions.
  constructor
  · -- A version of a touched key in `extra` puts that key in `acc`.
    rintro ⟨v, hv, hk, -⟩
    -- The key is the witness, found in `acc` through `hkeys`.
    exact ⟨v.1, hk, (hkeys v.1).mpr ⟨v, hv, rfl⟩⟩
  · -- A touched key in `acc` has a version in `extra`.
    rintro ⟨k, hk, hacc⟩
    -- `hkeys` gives the version `v` of key `k` in `extra`.
    obtain ⟨v, hv, rfl⟩ := (hkeys k).mp hacc
    -- That version is above `s0`, so above the snapshot too.
    have := hseq v hv
    -- So `v` is the witness, and arithmetic closes the sequence test.
    exact ⟨v, hv, hk, by omega⟩

/-- The induction behind `group_eq_serial`. The one-at-a-time store is the
view plus the versions `extra` of the members accepted so far, all above
`s0` and holding exactly the keys `acc`; every transaction left began at or
below `s0`; and the next sequence comes after `s`, which is at least `s0`.
Then the group and the one-at-a-time run give every remaining member the same
verdict. -/
theorem group_eq_serial_from (view : List (Nat × Nat)) (s0 : Nat) :
    ∀ (ts : List Txn) (extra : List (Nat × Nat)) (acc : List Nat) (s : Nat),
      -- The sequences drawn so far are at or above `s0`.
      s0 ≤ s →
      -- The accepted members' versions are above `s0`.
      (∀ v ∈ extra, s0 < v.2) →
      -- `acc` holds exactly the keys those versions hold.
      (∀ k, k ∈ acc ↔ ∃ v ∈ extra, v.1 = k) →
      -- Every transaction left began at or below `s0`.
      (∀ t ∈ ts, t.plain = false → t.snap ≤ s0) →
      -- Then both runs give the same verdicts.
      group view acc ts = serial (extra ++ view) s ts := by
  -- Take the list of members first.
  intro ts
  -- Induction on it: the empty list, then one member in front of the rest.
  induction ts with
  | nil =>
    -- No member left: introduce the hypotheses we will not need.
    intro extra acc s _ _ _ _
    -- Both runs give the empty list of verdicts.
    simp [group, serial]
  | cons t rest ih =>
    -- Introduce the store, the keys, the sequence and the hypotheses.
    intro extra acc s hs hseq hkeys hsnaps
    -- The members after `t` still began at or below `s0`.
    have hrest : ∀ u ∈ rest, u.plain = false → u.snap ≤ s0 :=
      -- Each of them is also in `t :: rest`.
      fun u hu => hsnaps u (List.mem_cons_of_mem _ hu)
    -- What `t` accepted does to the store and the keys, for both runs: its
    -- versions at `s + 1`, above `s0`, join `extra`, and its keys join `acc`.
    have hstep : group view (t.writes ++ acc) rest =
        serial (t.writes.map (fun k => (k, s + 1)) ++ extra ++ view) (s + 1) rest := by
      -- Apply the induction hypothesis to the bigger store and key list.
      apply ih _ _ (s + 1) (by omega)
      · -- Every version is above `s0`: the new ones are at `s + 1`.
        intro v hv
        -- A version is new or was there before.
        rcases List.mem_append.mp hv with hnew | hold
        · -- A new one is `(k, s + 1)` for a key `k` that `t` writes.
          obtain ⟨k, -, rfl⟩ := List.mem_map.mp hnew
          -- Its sequence is `s + 1`.
          simp only
          -- And `s0 ≤ s < s + 1`.
          omega
        · -- An old one is above `s0` already.
          exact hseq v hold
      · -- The keys of the new list are `t`'s writes plus the old keys.
        intro k
        -- Prove both directions.
        constructor
        · -- A key in the new `acc` has a version in the new `extra`.
          intro hk
          -- It is one of `t`'s writes, or an old key.
          rcases List.mem_append.mp hk with hw | ha
          · -- `t` writes it: its version at `s + 1` is new.
            exact ⟨(k, s + 1), List.mem_append_left _ (List.mem_map.mpr ⟨k, hw, rfl⟩), rfl⟩
          · -- An old key has an old version.
            obtain ⟨v, hv, hvk⟩ := (hkeys k).mp ha
            -- That version is still in the list.
            exact ⟨v, List.mem_append_right _ hv, hvk⟩
        · -- A version in the new `extra` has its key in the new `acc`.
          rintro ⟨v, hv, rfl⟩
          -- It is new, or old.
          rcases List.mem_append.mp hv with hnew | hold
          · -- A new version's key is one of `t`'s writes.
            obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hnew
            -- So it is in the front part of the new `acc`.
            exact List.mem_append_left _ hk'
          · -- An old version's key was in the old `acc`.
            exact List.mem_append_right _ ((hkeys v.1).mpr ⟨v, hold, rfl⟩)
      · -- The rest began at or below `s0`.
        exact hrest
    -- Now split on whether `t` is a plain write.
    cases hp : t.plain with
    | true =>
      -- A plain write is accepted by both runs: unfold one step of each.
      simp only [group, serial, hp, Bool.not_true, Bool.false_and, Bool.false_eq_true,
        ite_false]
      -- Regroup `hstep`'s store as `new ++ (extra ++ view)`, the goal's shape.
      rw [List.append_assoc] at hstep
      -- The heads match and the tails are `hstep`.
      exact congrArg (true :: ·) hstep
    | false =>
      -- A transaction: its snapshot is at or below `s0`.
      have htsnap : t.snap ≤ s0 := hsnaps t List.mem_cons_self hp
      -- The one-at-a-time test of `t` splits into the accepted members'
      -- versions, which `conflicts_newer` turns into the group's key test,
      -- and the view, which both runs test alike.
      have htest : conflicts (extra ++ view) t =
          (conflicts view t || t.touched.any (fun k => acc.contains k)) := by
        -- Replace the key test by the version test over `extra`.
        rw [← conflicts_newer hseq hkeys htsnap]
        -- A check over a joined list is the check over each part.
        simp [conflicts, List.any_append, Bool.or_comm]
      -- Unfold one step of each run, with the test rewritten.
      simp only [group, serial, hp, htest, Bool.not_false, Bool.true_and]
      -- Split on whether the test says conflict.
      by_cases hc : (conflicts view t || t.touched.any (fun k => acc.contains k)) = true
      · -- Both runs abort `t`; the rest follow by induction, unchanged.
        simp only [hc, ite_true]
        -- Heads are false; tails come from the induction hypothesis.
        exact congrArg (false :: ·) (ih extra acc s hs hseq hkeys hrest)
      · -- Both runs accept `t`: turn "not true" into "false".
        simp only [Bool.not_eq_true] at hc
        -- Take the accepting branch on both sides.
        simp only [hc, Bool.false_eq_true, ite_false]
        -- Regroup `hstep`'s store as `new ++ (extra ++ view)`, the goal's shape.
        rw [List.append_assoc] at hstep
        -- Heads are true; tails are `hstep`.
        exact congrArg (true :: ·) hstep

/-- **A group commit equals committing its members one at a time.** Take
any view, and any group whose transactions all began at or before `s`, the
last sequence drawn before the group. Checking each member against the view
plus the keys written by members accepted earlier in the group (plain writes
accepted unchecked) gives every member the verdict that committing them one
at a time, in group order, gives it. -/
theorem group_eq_serial (view : List (Nat × Nat)) (ts : List Txn) (s : Nat)
    -- Every transaction began at or before the group's sequences.
    (hsnaps : ∀ t ∈ ts, t.plain = false → t.snap ≤ s) :
    -- The group's verdicts are the one-at-a-time verdicts.
    group view [] ts = serial view s ts := by
  -- Start the induction with no accepted member, no versions, no keys.
  have := group_eq_serial_from view s ts [] [] s (Nat.le_refl s)
    -- No version is in the empty list, so the sequence claim is vacuous.
    (fun _ h => absurd h List.not_mem_nil)
    -- No key is in the empty list, and no version either.
    (fun k => by simp) hsnaps
  -- `[] ++ view` is `view`, so this is the statement.
  simpa using this

/-! ## The check split at a horizon -/

/-- **Validation outside the mutex.** For a member whose snapshot is at or
below `h`, the versions above its snapshot conflict exactly when those up to
`h` (checked before the mutex) or those above `h` (checked under it) do. -/
theorem early_check_split (vs : List (Nat × Nat)) (t : Txn) (h : Nat)
    -- The horizon is sampled after the snapshot.
    (hsh : t.snap ≤ h) :
    -- One check equals the two halves.
    conflicts vs t =
      (vs.any (fun v => t.touched.contains v.1 && decide (t.snap < v.2 ∧ v.2 ≤ h)) ||
        vs.any (fun v => t.touched.contains v.1 && decide (h < v.2))) := by
  -- Two booleans are equal when each is true exactly when the other is.
  apply Bool.eq_iff_iff.mpr
  -- Unfold into "there is a version such that ...".
  simp only [conflicts, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  -- Prove the two directions.
  constructor
  · -- A conflicting version is at or below `h`, or above it.
    rintro ⟨v, hv, hk, hlt⟩
    -- Look at which.
    by_cases hle : v.2 ≤ h
    · -- At or below: the first half finds it.
      exact Or.inl ⟨v, hv, hk, hlt, hle⟩
    · -- Above: the second half finds it.
      exact Or.inr ⟨v, hv, hk, by omega⟩
  · -- Either half's version conflicts in the one check.
    rintro (⟨v, hv, hk, hlt, -⟩ | ⟨v, hv, hk, hgt⟩)
    · -- From the first half: it is above the snapshot.
      exact ⟨v, hv, hk, hlt⟩
    · -- From the second: above `h`, so above the snapshot.
      exact ⟨v, hv, hk, by omega⟩

/-- **The early check as the code runs it.** The early check does not look
at exactly the versions up to `h`: it looks at the view it loads after
sampling `h`, which holds every version up to `h` that is newer than the
snapshot, and may hold newer ones too (applied, not yet visible). Then the
leader looks at every version above `h`. Together they decide as one check
of every version. When nothing was made visible since the snapshot (`h` is
the snapshot), the code loads no view at all: `early` is empty, and the
covering hypothesis holds vacuously. -/
theorem early_check_cover (vs early : List (Nat × Nat)) (t : Txn) (h : Nat)
    -- The early view holds only real versions.
    (hsub : ∀ v ∈ early, v ∈ vs)
    -- It holds every version newer than the snapshot up to `h`.
    (hcov : ∀ v ∈ vs, t.snap < v.2 → v.2 ≤ h → v ∈ early)
    -- The horizon is sampled after the snapshot.
    (hsh : t.snap ≤ h) :
    -- One check equals the early check plus the check above `h`.
    conflicts vs t =
      (conflicts early t || vs.any (fun v => t.touched.contains v.1 && decide (h < v.2))) := by
  -- Two booleans are equal when each is true exactly when the other is.
  apply Bool.eq_iff_iff.mpr
  -- Unfold into "there is a version such that ...".
  simp only [conflicts, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  -- Prove the two directions.
  constructor
  · -- A conflicting version is at or below `h`, or above it.
    rintro ⟨v, hv, hk, hlt⟩
    -- Look at which.
    by_cases hle : v.2 ≤ h
    · -- At or below: the early view holds it, and it conflicts there.
      exact Or.inl ⟨v, hcov v hv hlt hle, hk, hlt⟩
    · -- Above: the leader's check finds it.
      exact Or.inr ⟨v, hv, hk, by omega⟩
  · -- Either check's version conflicts in the one check.
    rintro (⟨v, hv, hk, hlt⟩ | ⟨v, hv, hk, hgt⟩)
    · -- The early view's version is a real one, above the snapshot.
      exact ⟨v, hsub v hv, hk, hlt⟩
    · -- Above `h`, so above the snapshot.
      exact ⟨v, hv, hk, by omega⟩

/-- **An early conflict is final.** A conflict found among some versions is
still a conflict once more versions land: versions are only ever added, so
the version that conflicted is still there. This is why a transaction whose
early check fails aborts at once instead of queueing. -/
theorem early_conflict_final {xs ys : List (Nat × Nat)} {t : Txn}
    -- Every version seen early is still there later.
    (hsub : ∀ v ∈ xs, v ∈ ys)
    -- The early check found a conflict.
    (hc : conflicts xs t = true) :
    -- The later check finds one too.
    conflicts ys t = true := by
  -- Unfold into "there is a version such that ...".
  simp only [conflicts, List.any_eq_true] at hc ⊢
  -- Take the conflicting version.
  obtain ⟨v, hv, hk⟩ := hc
  -- It is still there, and still conflicts.
  exact ⟨v, hsub v hv, hk⟩

/-! ## The RED case: validating against the view alone -/

/-- Mutant ViewOnly: each member checked against the view alone, never
against the members accepted earlier in its group. -/
def viewOnly (view : List (Nat × Nat)) : List Txn → List Bool
  -- No member left: no verdict.
  | [] => []
  -- The verdict ignores every other member.
  | t :: rest => (t.plain || !conflicts view t) :: viewOnly view rest

/-- Two transactions that both began at sequence 0 and write key 1. -/
def twoWriters : List Txn :=
  -- Snapshot 0, touching key 1, writing key 1, not plain; twice.
  [⟨0, [1], [1], false⟩, ⟨0, [1], [1], false⟩]

/-- **`view_only_breaks_serial`.** Against an empty view, the view-only
leader commits both writers of key 1, a lost update; committing them one at
a time aborts the second, and so does the fixed group. -/
theorem view_only_breaks_serial :
    -- The bug commits both,
    viewOnly [] twoWriters = [true, true] ∧
      -- one at a time aborts the second,
      serial [] 0 twoWriters = [true, false] ∧
      -- and the fixed group does too.
      group [] [] twoWriters = [true, false] := by
  -- Every side is a computation on concrete lists: evaluate it.
  decide

/-- A plain write of key 1 ahead of a transaction that wrote key 1 from
snapshot 0: the plain write counts as accepted, so the transaction aborts in
the group as it would committing after it. -/
theorem plain_write_counts_in_group :
    -- The group aborts the transaction behind the plain write,
    group [] [] [⟨0, [], [1], true⟩, ⟨0, [1], [1], false⟩] = [true, false] ∧
      -- as committing them one at a time does.
      serial [] 0 [⟨0, [], [1], true⟩, ⟨0, [1], [1], false⟩] = [true, false] := by
  -- Concrete lists: evaluate.
  decide

-- The namespace ends here.
end Regolith.GroupCommit
