/-!
# Append: commit-ordered positions are dense, once per key, in commit order (plan 3.6)

This file backs two TLA+ models in `proofs/tla`:

* `CommitOrderedAppend.tla`, invariants `INV_Dense`, `INV_UniqueCursors`,
  `INV_AtMostOnce`, `INV_CommitOrder` and `INV_NoSkip` (configurations
  `MC_CommitOrderedAppend_Green_*`), and the REDs
  `MC_CommitOrderedAppend_Red_ViewOnlyHead`,
  `MC_CommitOrderedAppend_Red_AssignBeforeValidation` and
  `MC_CommitOrderedAppend_Red_Stamps`;
* `CommitOrderedAppendCrash.tla`, invariants `INV_Dense`,
  `INV_UniqueCursors` and `INV_AtMostOnce` after a crash, since recovery
  keeps a prefix of the commit order.

`Transaction::append(log, entry, once_key)` queues an append. In the
ordered step of the commit, after the transaction's reads are validated,
each append gets the log's next position, head + 1, unless its once key
already holds a position. TLC checks the interleavings for a few writers;
the theorems here hold for any number of commits, appends and once keys.

What is proved, in plain words:

1. `reachable_inv`: the ordered step keeps four facts about the log,
   whatever commits it decides and whichever of them fail validation.
2. `dense_from_one`: the positions, in the order they were assigned, are
   exactly 1, 2, ..., head.
3. `unique_positions`: no two rows share a position.
4. `at_most_once`: no two rows carry one once key, whether the two appends
   came from two transactions or from one.
5. `commit_order`: a smaller position belongs to an earlier commit, or to
   an earlier append of the same commit.
6. `snapshot_sees_prefix`: a snapshot sees the commits up to some point in
   commit order (visibility follows sequence order). With H the head it
   reads, it sees exactly the rows of the whole log at positions 1..H, and
   every one of them. A crash that keeps a prefix of the commit order
   leaves the same kind of state.
7. `view_only_head_duplicates`, `assign_before_validation_leaves_hole` and
   `stamps_leave_hole`: three REDs as concrete counterexamples.

Group commit needs no separate statement. A group's members are decided
one after another, each reading the head and the once keys the earlier
members left, which is exactly folding the ordered step over them; the
first counterexample shows what goes wrong when a member does not.

How to read the Lean: `def` defines a function or a property, `theorem`
states a fact and its proof follows `:= by`. Lines starting with `--` are
comments. A once key and a position are plain natural numbers.
-/

namespace Regolith.Append

/-! ## The objects -/

/-- One row of the log: an append that the ordered step gave a position. -/
structure Row where
  /-- The position assigned, starting at 1. -/
  pos : Nat
  /-- The commit it belongs to: commits are numbered 0, 1, 2, ... in the
  order the ordered step decided them, which is commit order. -/
  commit : Nat
  /-- Which of its commit's appends it is: 0, 1, 2, ... in the order the
  transaction called `append`. -/
  idx : Nat
  /-- The once key the append passed, or `none`. -/
  once : Option Nat
  deriving DecidableEq

/-- The log as the ordered step leaves it. -/
structure Log where
  /-- The head key: the newest position, 0 while the log is empty. -/
  head : Nat
  /-- The number the next committed transaction takes. -/
  seq : Nat
  /-- The rows, in the order they were assigned. -/
  rows : List Row
  deriving DecidableEq

/-- The empty log, before any commit. -/
def init : Log := ⟨0, 0, []⟩

/-- `fresh rows o`: an append passing once key `o` gets a row. It does when
it passes no once key, or when no row carries that key yet. The rows
include those of earlier members of the same group and earlier appends of
the same transaction, because they were assigned first. -/
def fresh (rows : List Row) : Option Nat → Bool
  -- No once key: always a new row.
  | none => true
  -- Once key `k`: a new row only if no row carries `k`.
  | some k => !(rows.any (fun r => r.once == some k))

/-- The `i`-th append of commit `c`, passing once key `o`. If it is fresh,
it takes position head + 1, and the head moves there (the commit writes
`head_key = p`); otherwise the log is unchanged. -/
def assignOne (c i : Nat) (s : Log) (o : Option Nat) : Log :=
  if fresh s.rows o then
    { s with head := s.head + 1, rows := s.rows ++ [⟨s.head + 1, c, i, o⟩] }
  else s

/-- The appends of commit `c` from the `i`-th on, in append order. -/
def assignFrom (c : Nat) : Nat → List (Option Nat) → Log → Log
  -- No append left.
  | _, [], s => s
  -- Number the next append, then the rest.
  | i, o :: os, s => assignFrom c (i + 1) os (assignOne c i s o)

/-- One decision of the ordered step. `d.1` says whether the transaction
passed validation, and `d.2` lists the once keys of its appends. Only a
transaction that passed takes a commit number and positions; one that
failed takes nothing, so it leaves no hole. -/
def orderedStep (s : Log) (d : Bool × List (Option Nat)) : Log :=
  if d.1 then assignFrom s.seq 0 d.2 { s with seq := s.seq + 1 } else s

/-- The log after the ordered step decides the transactions `ds`, in
order, from the empty log. -/
def process (ds : List (Bool × List (Option Nat))) : Log := ds.foldl orderedStep init

/-! ## The invariant -/

/-- `Before a b`: row `a` comes before row `b` in commit order: an earlier
commit, or the same commit and an earlier append. -/
def Before (a b : Row) : Prop := a.commit < b.commit ∨ (a.commit = b.commit ∧ a.idx < b.idx)

/-- `Ordered a b`, for a row `a` assigned before row `b`: `a` has the
smaller position and comes first in commit order. -/
def Ordered (a b : Row) : Prop := a.pos < b.pos ∧ Before a b

/-- `OnceApart a b`: rows `a` and `b` do not share a once key. -/
def OnceApart (a b : Row) : Prop := a.once = none ∨ a.once ≠ b.once

/-- The ordered step's invariant. `List.Pairwise R l` means `R x y` for
every `x` that comes before `y` in `l`. -/
structure Inv (s : Log) : Prop where
  /-- The positions in assignment order are 1, 2, ..., head. -/
  dense : s.rows.map Row.pos = List.range' 1 s.head
  /-- A row assigned earlier has a smaller position and an earlier place
  in commit order. -/
  ordered : s.rows.Pairwise Ordered
  /-- No two rows share a once key. -/
  once_apart : s.rows.Pairwise OnceApart
  /-- Every row belongs to a commit already numbered. -/
  below_seq : ∀ r ∈ s.rows, r.commit < s.seq

/-- The invariant while commit `c` is having its appends numbered, with
`i` the next append index: every row so far belongs to an earlier commit,
or to an earlier append of `c`. -/
structure Mid (c i : Nat) (s : Log) : Prop where
  /-- As `Inv.dense`. -/
  dense : s.rows.map Row.pos = List.range' 1 s.head
  /-- As `Inv.ordered`. -/
  ordered : s.rows.Pairwise Ordered
  /-- As `Inv.once_apart`. -/
  once_apart : s.rows.Pairwise OnceApart
  /-- Every row so far comes before `c`'s `i`-th append. -/
  before : ∀ r ∈ s.rows, r.commit < c ∨ (r.commit = c ∧ r.idx < i)

/-- In a dense log, every row's position is between 1 and the head. -/
theorem pos_le_head {s : Log}
    -- The positions are 1, ..., head.
    (hdense : s.rows.map Row.pos = List.range' 1 s.head)
    {r : Row}
    -- `r` is a row of the log.
    (hr : r ∈ s.rows) :
    1 ≤ r.pos ∧ r.pos ≤ s.head := by
  -- `r.pos` is in the list of positions, which is `1, ..., head`.
  have hmem : r.pos ∈ s.rows.map Row.pos := List.mem_map_of_mem hr
  rw [hdense, List.mem_range'_1] at hmem
  omega

/-- **Numbering one append keeps the invariant.** It moves on to the next
append index. -/
theorem assignOne_mid {c i : Nat} {s : Log} {o : Option Nat}
    -- The invariant holds before the `i`-th append of `c`.
    (h : Mid c i s) :
    Mid c (i + 1) (assignOne c i s o) := by
  unfold assignOne
  split
  · -- The append is fresh: a new row at head + 1.
    rename_i hfresh
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- The positions were 1, ..., head; now head + 1 follows.
      simp only [List.map_append, List.map_cons, List.map_nil, h.dense, List.range'_concat]
      congr 2
      omega
    · -- Every earlier row has a smaller position (at most head) and comes
      -- before the new row in commit order (`Mid.before`).
      rw [List.pairwise_append]
      refine ⟨h.ordered, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      have hpos := pos_le_head h.dense ha
      refine ⟨by simp only; omega, ?_⟩
      exact h.before a ha
    · -- No earlier row carries the new row's once key: it was fresh.
      rw [List.pairwise_append]
      refine ⟨h.once_apart, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      cases o with
      | none =>
        -- The new row has no once key, so it shares none with `a`.
        show a.once = none ∨ a.once ≠ none
        cases hao : a.once with
        | none => exact Or.inl rfl
        | some j => exact Or.inr (by simp)
      | some k =>
        -- `fresh` says no row carries `k`, `a` included.
        right
        simp only [fresh, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false,
          beq_iff_eq] at hfresh
        exact hfresh a ha
    · -- The new row is `c`'s `i`-th append; the earlier rows came before
      -- its `i`-th, so before its `(i + 1)`-th too.
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · rcases h.before r hr with h1 | ⟨h1, h2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, by omega⟩
      · rw [List.mem_singleton] at hr
        subst hr
        exact Or.inr ⟨rfl, by simp only; omega⟩
  · -- The once key is taken: nothing changes, and the bound on append
    -- indices only loosens.
    refine ⟨h.dense, h.ordered, h.once_apart, ?_⟩
    intro r hr
    rcases h.before r hr with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h1, by omega⟩

/-- Numbering the rest of a commit's appends keeps the invariant. -/
theorem assignFrom_mid {c : Nat} :
    ∀ (os : List (Option Nat)) {i : Nat} {s : Log},
      -- The invariant holds before the `i`-th append.
      Mid c i s →
      Mid c (i + os.length) (assignFrom c i os s)
  | [], i, s, h => by
    -- No append: nothing changes.
    simpa [assignFrom] using h
  | o :: os, i, s, h => by
    -- One append, then the rest by induction.
    have := assignFrom_mid os (assignOne_mid (o := o) h)
    simp only [assignFrom, List.length_cons]
    rw [show i + (os.length + 1) = i + 1 + os.length by omega]
    exact this

/-- Numbering appends never changes the next commit number. -/
theorem assignFrom_seq {c : Nat} :
    ∀ (os : List (Option Nat)) (i : Nat) (s : Log), (assignFrom c i os s).seq = s.seq
  | [], _, _ => rfl
  | o :: os, i, s => by
    -- `assignOne` leaves `seq` alone, either way.
    simp only [assignFrom]
    rw [assignFrom_seq os (i + 1) (assignOne c i s o)]
    unfold assignOne
    split <;> rfl

/-- **Every decision of the ordered step keeps the invariant**, whether the
transaction passed validation or not. -/
theorem orderedStep_inv {s : Log} (d : Bool × List (Option Nat))
    -- The invariant holds before the decision.
    (h : Inv s) :
    Inv (orderedStep s d) := by
  unfold orderedStep
  split
  · -- Passed: it takes commit number `seq` and its appends are numbered.
    -- Before that, every row belongs to an earlier commit.
    have hmid : Mid s.seq 0 { s with seq := s.seq + 1 } :=
      ⟨h.dense, h.ordered, h.once_apart, fun r hr => Or.inl (h.below_seq r hr)⟩
    have hend := assignFrom_mid d.2 hmid
    have hseq := assignFrom_seq (c := s.seq) d.2 0 { s with seq := s.seq + 1 }
    refine ⟨hend.dense, hend.ordered, hend.once_apart, ?_⟩
    -- Afterwards every row belongs to commit `seq` or an earlier one, and
    -- the next number is `seq + 1`.
    intro r hr
    rw [hseq]
    rcases hend.before r hr with h1 | ⟨h1, -⟩
    · simp only
      omega
    · simp only
      omega
  · -- Failed validation: nothing changes.
    exact h

/-- The empty log satisfies the invariant. -/
theorem init_inv : Inv init :=
  -- No rows, head 0: the positions are the empty list `range' 1 0`.
  ⟨rfl, List.Pairwise.nil, List.Pairwise.nil, fun _ h => absurd h List.not_mem_nil⟩

/-- Any number of decisions keeps the invariant. -/
theorem foldl_inv :
    ∀ (ds : List (Bool × List (Option Nat))) {s : Log}, Inv s → Inv (ds.foldl orderedStep s)
  | [], _, h => h
  | d :: ds, _, h => foldl_inv ds (orderedStep_inv d h)

/-- **Every log the ordered step reaches satisfies the invariant.** -/
theorem reachable_inv (ds : List (Bool × List (Option Nat))) : Inv (process ds) :=
  foldl_inv ds init_inv

/-! ## The laws -/

/-- Two members of a list with a pairwise relation are equal, or related
one way or the other. -/
theorem pairwise_mem {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a = b ∨ R a b ∨ R b a
  | [], _, _, _, ha, _ => absurd ha List.not_mem_nil
  | x :: xs, hp, a, b, ha, hb => by
    rw [List.pairwise_cons] at hp
    -- Each of `a` and `b` is the head `x` or in the tail.
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (hp.1 b hb'))
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr (Or.inr (hp.1 a ha'))
      · exact pairwise_mem hp.2 ha' hb'

/-- **Dense from 1.** The positions of any reachable log, in the order they
were assigned, are exactly 1, 2, ..., head. TLA+: `INV_Dense`. -/
theorem dense_from_one (ds : List (Bool × List (Option Nat))) :
    (process ds).rows.map Row.pos = List.range' 1 (process ds).head :=
  (reachable_inv ds).dense

/-- **Unique positions.** Two rows of a reachable log at one position are
the same row. TLA+: `INV_UniqueCursors`. -/
theorem unique_positions (ds : List (Bool × List (Option Nat))) {a b : Row}
    -- Both are rows of the log ...
    (ha : a ∈ (process ds).rows) (hb : b ∈ (process ds).rows)
    -- ... at one position.
    (hpos : a.pos = b.pos) :
    a = b := by
  -- Otherwise one was assigned first and has the smaller position.
  rcases pairwise_mem (reachable_inv ds).ordered ha hb with h | h | h
  · exact h
  · exact absurd h.1 (by omega)
  · exact absurd h.1 (by omega)

/-- **At most once per once key.** Two rows of a reachable log carrying
once key `k` are the same row: whether the appends came from two
transactions, two members of one group, or one transaction twice, only the
first got a row. TLA+: `INV_AtMostOnce`. -/
theorem at_most_once (ds : List (Bool × List (Option Nat))) {a b : Row} {k : Nat}
    -- Both are rows of the log ...
    (ha : a ∈ (process ds).rows) (hb : b ∈ (process ds).rows)
    -- ... carrying once key `k`.
    (hak : a.once = some k) (hbk : b.once = some k) :
    a = b := by
  -- Otherwise the one assigned first would be `OnceApart` from the other.
  rcases pairwise_mem (reachable_inv ds).once_apart ha hb with h | h | h
  · exact h
  · rcases h with h | h
    · rw [hak] at h
      cases h
    · exact absurd (hak.trans hbk.symm) h
  · rcases h with h | h
    · rw [hbk] at h
      cases h
    · exact absurd (hbk.trans hak.symm) h

/-- **Commit order.** In a reachable log, a row at a smaller position
belongs to an earlier commit, or to an earlier append of the same commit.
TLA+: `INV_CommitOrder`. -/
theorem commit_order (ds : List (Bool × List (Option Nat))) {a b : Row}
    -- Both are rows of the log ...
    (ha : a ∈ (process ds).rows) (hb : b ∈ (process ds).rows)
    -- ... and `a` has the smaller position.
    (hlt : a.pos < b.pos) :
    Before a b := by
  -- The one assigned first has the smaller position, so it is `a`.
  rcases pairwise_mem (reachable_inv ds).ordered ha hb with h | h | h
  · subst h
    exact absurd hlt (Nat.lt_irrefl _)
  · exact h.2
  · exact absurd h.1 (by omega)

/-- The ordered step only appends rows above the head it started from,
and never lowers the head. -/
theorem assignFrom_extends {c : Nat} :
    ∀ (os : List (Option Nat)) (i : Nat) (s : Log),
      ∃ extra, (assignFrom c i os s).rows = s.rows ++ extra ∧
        (∀ r ∈ extra, s.head < r.pos) ∧ s.head ≤ (assignFrom c i os s).head
  | [], _, s => ⟨[], by simp [assignFrom], by simp, by simp [assignFrom]⟩
  | o :: os, i, s => by
    -- First the `i`-th append, which adds at most one row at head + 1.
    have h1 : ∃ e1, (assignOne c i s o).rows = s.rows ++ e1 ∧
        (∀ r ∈ e1, s.head < r.pos) ∧ s.head ≤ (assignOne c i s o).head := by
      unfold assignOne
      split
      · refine ⟨[⟨s.head + 1, c, i, o⟩], rfl, ?_, by simp only; omega⟩
        intro r hr
        rw [List.mem_singleton] at hr
        subst hr
        simp only
        omega
      · exact ⟨[], by simp, by simp, Nat.le_refl _⟩
    obtain ⟨e1, hr1, hp1, hh1⟩ := h1
    -- Then the rest, above the new head, which is at least the old one.
    obtain ⟨e2, hr2, hp2, hh2⟩ := assignFrom_extends os (i + 1) (assignOne c i s o)
    refine ⟨e1 ++ e2, ?_, ?_, ?_⟩
    · simp only [assignFrom]
      rw [hr2, hr1, List.append_assoc]
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hp1 r hr
      · have := hp2 r hr
        omega
    · simp only [assignFrom]
      omega

/-- Any number of decisions only appends rows above the head they started
from. -/
theorem foldl_extends :
    ∀ (ds : List (Bool × List (Option Nat))) (s : Log),
      ∃ extra, (ds.foldl orderedStep s).rows = s.rows ++ extra ∧
        ∀ r ∈ extra, s.head < r.pos
  | [], s => ⟨[], by simp, by simp⟩
  | d :: ds, s => by
    -- The first decision adds rows above `s.head` and does not lower it ...
    have h1 : ∃ e1, (orderedStep s d).rows = s.rows ++ e1 ∧
        (∀ r ∈ e1, s.head < r.pos) ∧ s.head ≤ (orderedStep s d).head := by
      unfold orderedStep
      split
      · exact assignFrom_extends d.2 0 { s with seq := s.seq + 1 }
      · exact ⟨[], by simp, by simp, Nat.le_refl _⟩
    obtain ⟨e1, hr1, hp1, hh1⟩ := h1
    -- ... and the rest add rows above the head after it.
    obtain ⟨e2, hr2, hp2⟩ := foldl_extends ds (orderedStep s d)
    refine ⟨e1 ++ e2, ?_, ?_⟩
    · simp only [List.foldl_cons]
      rw [hr2, hr1, List.append_assoc]
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hp1 r hr
      · have := hp2 r hr
        omega

/-- **A snapshot sees exactly rows 1..H.** Visibility follows sequence
order, so a snapshot sees the first `k` decisions' commits and no later
one; let H be the head in it. Then, among all the rows the log will ever
hold, those at positions up to H are exactly the snapshot's rows, and the
snapshot's rows sit at positions 1, ..., H, every one of them. A reader
bounded by its snapshot's head therefore never skips a row: no later
commit adds one at or below H. A crash that keeps a prefix of the commit
order leaves such a state. TLA+: `INV_Dense` and `INV_NoSkip`. -/
theorem snapshot_sees_prefix (ds : List (Bool × List (Option Nat))) (k : Nat) :
    (process ds).rows.filter (fun r => decide (r.pos ≤ (process (ds.take k)).head)) =
        (process (ds.take k)).rows ∧
      (process (ds.take k)).rows.map Row.pos = List.range' 1 (process (ds.take k)).head := by
  refine ⟨?_, dense_from_one (ds.take k)⟩
  -- Name the snapshot's log `p`.
  generalize hp : process (ds.take k) = p
  -- The whole log is `p` followed by the later decisions.
  have hsplit : process ds = (ds.drop k).foldl orderedStep p := by
    rw [← hp]
    unfold process
    rw [← List.foldl_append, List.take_append_drop]
  -- Those only add rows above `p.head`.
  obtain ⟨extra, hrows, habove⟩ := foldl_extends (ds.drop k) p
  rw [hsplit, hrows, List.filter_append]
  -- Every row of `p` is at or below its head (it is dense) ...
  have hdense : p.rows.map Row.pos = List.range' 1 p.head := by
    rw [← hp]
    exact dense_from_one (ds.take k)
  have hkeep : p.rows.filter (fun r => decide (r.pos ≤ p.head)) = p.rows := by
    rw [List.filter_eq_self]
    intro r hr
    have := pos_le_head hdense hr
    simp only [decide_eq_true_eq]
    omega
  -- ... and every later row is above it.
  have hdrop : extra.filter (fun r => decide (r.pos ≤ p.head)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro r hr
    have := habove r hr
    simp only [decide_eq_true_eq]
    omega
  rw [hkeep, hdrop, List.append_nil]

/-! ## The RED cases, as counterexamples -/

/-- The RED ViewOnlyHead: a group whose every member numbers its appends
from the head the group started with, not the head the earlier members
left. -/
def groupViewOnly (start : Log) : Log → List (List (Option Nat)) → Log
  -- No member left.
  | s, [] => s
  -- The next member takes a commit number, resets the head, and numbers.
  | s, apps :: rest =>
    groupViewOnly start (assignFrom s.seq 0 apps { s with seq := s.seq + 1, head := start.head }) rest

/-- **`view_only_head_duplicates`.** Two members appending once each, in
one group: read from the view only, both take position 1. The ordered step
of the design, folding over the members, gives them 1 and 2. -/
theorem view_only_head_duplicates :
    (groupViewOnly init init [[none], [none]]).rows.map Row.pos = [1, 1] ∧
      (process [(true, [none]), (true, [none])]).rows.map Row.pos = [1, 2] := by
  decide

/-- The RED AssignBeforeValidation: positions are counted before
validation, so a transaction that then fails still moves the head past the
positions it would have taken. -/
def orderedStepEarly (s : Log) (d : Bool × List (Option Nat)) : Log :=
  if d.1 then orderedStep s d else { s with head := (assignFrom s.seq 0 d.2 s).head }

/-- One transaction fails validation after taking position 1, then one
commits. -/
def earlyLog : Log := [(false, [none]), (true, [none])].foldl orderedStepEarly init

/-- **`assign_before_validation_leaves_hole`.** The committed append sits
at position 2 under head 2, and no row holds position 1: the log is not
dense. -/
theorem assign_before_validation_leaves_hole :
    earlyLog.head = 2 ∧ earlyLog.rows.map Row.pos = [2] ∧
      earlyLog.rows.map Row.pos ≠ List.range' 1 earlyLog.head := by
  decide

/-- The RED Stamps (plan D1): an appended row's position is its commit's
sequence number, 1, 2, 3, ..., and every commit takes one, appending or
not. A reader's bound is the newest visible sequence, kept in `head`.
(At most one append per commit, as stamps had.) -/
def stampStep (s : Log) (d : Bool × List (Option Nat)) : Log :=
  if d.1 then
    { head := s.seq + 1, seq := s.seq + 1,
      rows := s.rows ++ (d.2.take 1).map (fun o => ⟨s.seq + 1, s.seq, 0, o⟩) }
  else s

/-- A commit that appends nothing, then a commit that appends once. -/
def stamped : Log := [(true, []), (true, [none])].foldl stampStep init

/-- **`stamps_leave_hole`.** Under a bound of 2 the log holds position 2
only: the commit that appended nothing consumed position 1. -/
theorem stamps_leave_hole :
    stamped.head = 2 ∧ stamped.rows.map Row.pos = [2] ∧
      stamped.rows.map Row.pos ≠ List.range' 1 stamped.head := by
  decide

end Regolith.Append
