/-!
# Pipeline: decide in ring order, publish the longest publishable prefix

This file backs the TLA+ model `proofs/tla/CommitPipeline.tla`, invariants
`NoHole`, `SeqInRingOrder`, `PublishedPrefix` and `ReadersSeePrefix`
(configurations `MC_CommitPipeline_Green`, `MC_CommitPipeline_Red_AbortHole`
and `MC_CommitPipeline_Red_OutOfOrder`). The sequence numbering it proves is
also the one `proofs/tla/GroupCommit.tla` checks as
`SeqFollowsDecisionOrder`.

The lock-free commit pipeline (plan 4.7) keeps commits in a ring of slots.
Slots are decided in ring order: a commit takes the next sequence, an abort
or a slot a helper voided takes none. The visible horizon then advances
over the longest prefix of slots that may be published: aborts and void
slots at once, a commit once it is applied (and durable, at Immediate).

TLC checks the interleavings for a few slots. The theorems here hold for
every number of slots and every pattern of verdicts and readiness.

What is proved, in plain words:

1. `seqs_dense`: deciding in ring order hands the committed slots the
   sequences `base+1, base+2, ...` with no gap. An abort or a void slot
   takes nothing, so it never leaves a hole.
2. `seqs_strictly_increasing`: in ring order the sequences only grow, so
   sequence order is ring order.
3. `seqs_take` and `publication_order`: the published prefix keeps the
   sequences its decisions gave it, and publishing the longest publishable
   prefix publishes exactly `base+1, ..., horizon`, in ring order. The
   publication order is the sequence order.
4. `reader_sees_published`: a reader at the published horizon sees, among
   the applied versions, exactly the committed slots below the frontier:
   the sequences `base+1, ..., horizon`, and nothing from a later slot,
   applied or not.
5. `abort_with_seq_leaves_hole` and `fetch_max_breaks_prefix`: the RED
   configurations as concrete counterexamples. An abort that takes a
   sequence leaves a hole; a horizon raised by `fetch_max` over a later
   applied slot shows a reader that slot without an earlier one.

Lock-freedom and helping are about interleavings and stay in TLA+. The
validation the decide stage runs is `Regolith/GroupCommit.lean`.

How to read the Lean: `def` defines a function or a property, `theorem`
states a fact and its proof follows `:= by`. Lines starting with `--` are
comments. Inside a proof, each step is commented with what it establishes.
-/

namespace Regolith.Pipeline

/-! ## The objects -/

/-
Sequence numbers are plain natural numbers (`Nat`), kept as `Nat` rather
than a named alias so that `omega` sees them as numbers. `s` is the last
sequence handed out before the slots under discussion: the base.
-/

/-- What a decided slot became. -/
inductive Dec where
  /-- The slot passed validation: it takes the next sequence. -/
  | commit
  /-- The slot failed validation: it takes nothing. -/
  | abort
  /-- A helper voided the slot, reserved but never filled: it takes nothing. -/
  | void
  deriving DecidableEq

/-- A decided slot of the ring, in ring order. -/
structure Slot where
  /-- The verdict. -/
  dec : Dec
  /-- Its versions are in the memtable (meaningful for a commit). -/
  applied : Bool
  /-- Its durability allows publication: it is durable, or it did not ask
  for Immediate (meaningful for a commit). -/
  durableOk : Bool
  deriving DecidableEq

/-! ## Deciding in ring order -/

/-- `seqs s slots`: the sequence each slot takes when the slots are decided
one after another in ring order, after base `s`. A commit takes the next
sequence; an abort or a void slot takes none (`none`). -/
def seqs : Nat → List Slot → List (Option Nat)
  -- No slot, no sequence.
  | _, [] => []
  -- A commit takes `s + 1`, and the slots after it continue from there.
  | s, ⟨.commit, _, _⟩ :: rest => some (s + 1) :: seqs (s + 1) rest
  -- An abort takes nothing, and the slots after it continue from `s`.
  | s, ⟨.abort, _, _⟩ :: rest => none :: seqs s rest
  -- A void slot takes nothing either.
  | s, ⟨.void, _, _⟩ :: rest => none :: seqs s rest

/-- How many slots in the list commit. -/
def commits : List Slot → Nat
  -- No slot, no commit.
  | [] => 0
  -- A commit counts one.
  | ⟨.commit, _, _⟩ :: rest => commits rest + 1
  -- An abort counts nothing.
  | ⟨.abort, _, _⟩ :: rest => commits rest
  -- A void slot counts nothing.
  | ⟨.void, _, _⟩ :: rest => commits rest

/-- **No hole.** The sequences the slots take, read in ring order with the
non-committing slots skipped, are exactly `s+1, s+2, ..., s+n` for the `n`
commits: consecutive, from the base, with no gap where an abort or a void
slot sits. -/
theorem seqs_dense (s : Nat) (l : List Slot) :
    (seqs s l).filterMap id = List.range' (s + 1) (commits l) := by
  -- By induction on the slots, for every base `s`.
  induction l generalizing s with
  | nil =>
    -- No slot: no sequence, and an empty range.
    simp [seqs, commits]
  | cons sl rest ih =>
    -- Name the first slot's verdict and look at each case.
    obtain ⟨d, a, o⟩ := sl
    cases d with
    | commit =>
      -- The commit takes `s + 1`; the rest take `s+2, ...` by induction.
      -- `range' (s+1) (n+1)` is `s+1` followed by `range' (s+2) n`.
      simp [seqs, commits, ih (s + 1), List.range'_succ]
    | abort =>
      -- The abort takes nothing: the rest give the whole answer.
      simp [seqs, commits, ih s]
    | void =>
      -- The void slot takes nothing: the rest give the whole answer.
      simp [seqs, commits, ih s]

/-- A range of consecutive naturals is strictly increasing. -/
theorem range'_strictly_increasing (a n : Nat) : (List.range' a n).Pairwise (· < ·) := by
  -- By induction on the length, for every start `a`.
  induction n generalizing a with
  | zero =>
    -- The empty range is trivially increasing.
    simp
  | succ n ih =>
    -- `a` comes first, and every later element is at least `a + 1`.
    rw [List.range'_succ, List.pairwise_cons]
    refine ⟨?_, ih (a + 1)⟩
    intro x hx
    -- An element of `range' (a+1) n` lies in `[a+1, a+1+n)`.
    have := (List.mem_range'_1.mp hx).1
    omega

/-- **Sequence order is ring order.** Read in ring order, the sequences the
committed slots take strictly increase. -/
theorem seqs_strictly_increasing (s : Nat) (l : List Slot) :
    ((seqs s l).filterMap id).Pairwise (· < ·) := by
  -- They are a range of consecutive naturals.
  rw [seqs_dense]
  exact range'_strictly_increasing _ _

/-- Deciding a prefix of the ring gives the prefix of the decisions: a
slot's sequence depends only on the slots before it. -/
theorem seqs_take (s n : Nat) (l : List Slot) :
    seqs s (l.take n) = (seqs s l).take n := by
  -- By induction on the slots, for every base and every prefix length.
  induction l generalizing s n with
  | nil =>
    -- No slot: both sides are empty.
    simp [seqs]
  | cons sl rest ih =>
    -- A prefix of length zero is empty on both sides; otherwise the first
    -- slot is decided the same way and the rest follow by induction.
    cases n with
    | zero => simp [seqs]
    | succ n =>
      obtain ⟨d, a, o⟩ := sl
      cases d <;> simp [seqs, ih]

/-! ## Publishing the longest publishable prefix -/

/-- `frontier slots`: how many leading slots may be published. An abort or
a void slot never stops it; a commit stops it until the commit is applied
and its durability allows publication. -/
def frontier : List Slot → Nat
  -- No slot, nothing to publish.
  | [] => 0
  -- A commit: past it only when applied and durable enough.
  | ⟨.commit, a, o⟩ :: rest => if a && o then frontier rest + 1 else 0
  -- An abort is published at once.
  | ⟨.abort, _, _⟩ :: rest => frontier rest + 1
  -- A void slot is published at once.
  | ⟨.void, _, _⟩ :: rest => frontier rest + 1

/-- The visible horizon after publishing the frontier: the base plus the
number of commits the frontier passed. -/
def horizon (s : Nat) (l : List Slot) : Nat := s + commits (l.take (frontier l))

/-- **Publication order is sequence order.** Publishing the longest
publishable prefix publishes, in ring order, exactly the sequences
`s+1, ..., horizon`: each publication is the next sequence. -/
theorem publication_order (s : Nat) (l : List Slot) :
    (seqs s (l.take (frontier l))).filterMap id = List.range' (s + 1) (horizon s l - s) := by
  -- The published prefix is a list of slots like any other, so its
  -- sequences are dense; and `horizon s l - s` is its commit count.
  rw [seqs_dense]
  simp [horizon]

/-! ## What a reader at the horizon sees -/

/-- `seen s v slots`: what a reader at horizon `v` sees of the slots, in
ring order: the sequence of every committed slot whose versions are
applied and whose sequence is at most `v`. Visibility asks only that the
versions be in the memtable and old enough; it does not ask whether the
slot was published. -/
def seen (s v : Nat) : List Slot → List Nat
  -- No slot, nothing seen.
  | [] => []
  -- A commit at `s + 1` is seen when applied and at or below `v`.
  | ⟨.commit, a, _⟩ :: rest =>
    (if a && decide (s + 1 ≤ v) then [s + 1] else []) ++ seen (s + 1) v rest
  -- An abort holds no version.
  | ⟨.abort, _, _⟩ :: rest => seen s v rest
  -- A void slot holds no version.
  | ⟨.void, _, _⟩ :: rest => seen s v rest

/-- A reader at a horizon `v` no later than the base sees nothing: every
sequence after the base is above it. -/
theorem seen_at_or_below_base {t v : Nat} (l : List Slot)
    -- The horizon is at or below the base.
    (hv : v ≤ t) : seen t v l = [] := by
  -- By induction on the slots, for every base at or above `v`.
  induction l generalizing t with
  | nil => simp [seen]
  | cons sl rest ih =>
    obtain ⟨d, a, o⟩ := sl
    cases d with
    | commit =>
      -- `t + 1` is above `v`, and so is every later sequence.
      have h1 : ¬ (t + 1 ≤ v) := by omega
      simp [seen, h1, ih (Nat.le_succ_of_le hv)]
    | abort => simp [seen, ih hv]
    | void => simp [seen, ih hv]

/-- The core of `reader_sees_published`, by induction: a reader at the
horizon sees the consecutive sequences of the published commits. -/
theorem seen_horizon (s : Nat) (l : List Slot) :
    seen s (horizon s l) l = List.range' (s + 1) (commits (l.take (frontier l))) := by
  -- By induction on the slots, for every base `s`.
  induction l generalizing s with
  | nil =>
    -- No slot: nothing seen, an empty range.
    simp [seen, frontier, commits]
  | cons sl rest ih =>
    obtain ⟨d, a, o⟩ := sl
    cases d with
    | commit =>
      by_cases hr : (a && o) = true
      · -- The commit is published. It takes `s + 1`, the horizon is the
        -- rest's horizon from base `s + 1`, and the reader sees `s + 1`
        -- followed by what the rest shows by induction.
        obtain ⟨rfl, rfl⟩ : a = true ∧ o = true := by simpa using hr
        have hh : horizon s (⟨.commit, true, true⟩ :: rest) = horizon (s + 1) rest := by
          simp [horizon, frontier, commits]
          omega
        rw [hh]
        have hle : s + 1 ≤ horizon (s + 1) rest := by
          simp [horizon]
        simp [seen, hle, ih (s + 1), frontier, commits, List.range'_succ]
      · -- The commit is not published, so the frontier is 0 and the
        -- horizon is the base: the reader sees nothing, the range is empty.
        have hf : frontier (⟨.commit, a, o⟩ :: rest) = 0 := by
          simp [frontier, hr]
        have hh : horizon s (⟨.commit, a, o⟩ :: rest) = s := by
          simp [horizon, hf, commits]
        rw [hh, hf]
        have h1 : ¬ (s + 1 ≤ s) := by omega
        simp [seen, h1, seen_at_or_below_base rest (Nat.le_succ s), commits]
    | abort =>
      -- The abort is published at once and takes nothing: the answer is
      -- the rest's, from the same base.
      have hh : horizon s (⟨.abort, a, o⟩ :: rest) = horizon s rest := by
        simp [horizon, frontier, commits]
      rw [hh]
      simp [seen, ih s, frontier, commits]
    | void =>
      -- The same for a void slot.
      have hh : horizon s (⟨.void, a, o⟩ :: rest) = horizon s rest := by
        simp [horizon, frontier, commits]
      rw [hh]
      simp [seen, ih s, frontier, commits]

/-- **A reader at the published horizon sees exactly the committed slots
below the frontier.** What it sees is the list of sequences the published
prefix took, `s+1, ..., horizon` in ring order: every published commit,
and nothing from a later slot, even one already applied. -/
theorem reader_sees_published (s : Nat) (l : List Slot) :
    seen s (horizon s l) l = (seqs s (l.take (frontier l))).filterMap id ∧
      seen s (horizon s l) l = List.range' (s + 1) (horizon s l - s) := by
  -- Both sides are the same consecutive range.
  refine ⟨?_, ?_⟩
  · rw [seen_horizon, seqs_dense]
  · rw [seen_horizon]
    simp [horizon]

/-! ## The RED cases -/

/-- Mutant AbortHole: an aborted slot takes a sequence too. The sequences
of the committed slots, in ring order. -/
def committedSeqsAbortTakes : Nat → List Slot → List Nat
  -- No slot, no sequence.
  | _, [] => []
  -- A commit takes `s + 1`.
  | s, ⟨.commit, _, _⟩ :: rest => (s + 1) :: committedSeqsAbortTakes (s + 1) rest
  -- The defect: an abort burns `s + 1`, which no record will carry.
  | s, ⟨.abort, _, _⟩ :: rest => committedSeqsAbortTakes (s + 1) rest
  -- A void slot takes nothing.
  | s, ⟨.void, _, _⟩ :: rest => committedSeqsAbortTakes s rest

/-- A commit, an abort, a commit, all applied and durable. -/
def commitAbortCommit : List Slot :=
  [⟨.commit, true, true⟩, ⟨.abort, true, true⟩, ⟨.commit, true, true⟩]

/-- **`abort_with_seq_leaves_hole`.** With aborts taking sequences, the two
commits of `commitAbortCommit` hold 1 and 3: sequence 2 is a hole, where
the fixed pipeline gives them 1 and 2. -/
theorem abort_with_seq_leaves_hole :
    committedSeqsAbortTakes 0 commitAbortCommit = [1, 3] ∧
      (seqs 0 commitAbortCommit).filterMap id = [1, 2] ∧
      committedSeqsAbortTakes 0 commitAbortCommit ≠ List.range' 1 (commits commitAbortCommit) := by
  decide

/-- Two commits: the first not yet applied, the second applied and
durable. -/
def laterApplied : List Slot := [⟨.commit, false, true⟩, ⟨.commit, true, true⟩]

/-- **`fetch_max_breaks_prefix`.** The slots of `laterApplied` take
sequences 1 and 2, and the frontier is stuck at the first. A `fetch_max`
horizon raised to 2 by the second slot's thread shows a reader sequence 2
without sequence 1. -/
theorem fetch_max_breaks_prefix :
    seqs 0 laterApplied = [some 1, some 2] ∧ frontier laterApplied = 0 ∧
      horizon 0 laterApplied = 0 ∧
      seen 0 2 laterApplied = [2] ∧ seen 0 2 laterApplied ≠ List.range' 1 2 := by
  decide

end Regolith.Pipeline
