/-!
# MergeOperator: the merge-operator contract (plan 3.3)

This file backs the TLA+ model `proofs/tla/RepeatableRead.tla` (with its
commit rule in `RepeatableReadCommit.tla`). Two of its rules rest on the
laws proved here:

* the blind-merge rule (`MergeDecider`; configurations
  `MC_DefraLevel_Green_Counters`, `MC_DefraLevel_Red_MergeIgnoresReplacement`
  and the other counter Reds, invariant `INV_CounterExact`): operands are
  folded onto the key's value in commit order, and compaction may combine
  adjacent operands with `partial_merge` without changing what a read
  returns;
* the projected-read rule (`Decisive`; configurations
  `MC_DefraLevel_Green_Parts` and its Reds, invariant `INV_PartsCurrent`):
  an operand for which `touches` answers false leaves the named parts as
  they were.

TLC checks those rules for a few operands. The theorems here hold for every
operator that keeps the contract, every number of operands and every way of
grouping them. `Regolith/Validation.lean` uses `TouchesSound` from here for
its projected-read theorem.

What is proved, in plain words:

1. `fold_eq_grouping` and `fold_eq_any_grouping`: when `partial_merge` is
   exact (applying two adjacent operands one after the other equals applying
   their partial merge, from every value), folding the operands one by one
   (`full_merge`) gives the same value as first combining them in any
   grouping. `steps_preserve_fold` says the same for compaction seen as a
   sequence of steps, each combining two adjacent operands.
2. `groupings_agree`: when `partial_merge` is also associative, any two
   groupings of the same operands combine to the same operand.
3. `touches_law`: an operand that touches no part in a set leaves those
   parts' values unchanged, and so does any run of such operands.
   `touches_grouping` and `touches_survives_compaction`: when `touches` of a
   partial merge is the `or` of its two inputs, the law holds for a combined
   operand too.
4. `inexact_breaks_fold`: the RED case. An operator that rounds after every
   step, like a floating-point sum, with "add the operands" as its partial
   merge: one rounding differs from two, so compaction would change what a
   read returns. Such an operator must not declare `partial_merge`.
5. `part_operator_exact`, `part_operator_assoc`, `part_operator_touches_sound`
   and `part_operator_touches_partial`: the operand RepeatableRead.tla puts on
   its part key (one more on each part it touches) keeps the whole contract.

How to read the Lean: `def` defines a function or a property, `structure`
groups named fields, `theorem` states a fact and its proof follows `:= by`.
Lines starting with `--` are comments; each proof step is commented.
-/

namespace Regolith.MergeOperator

/-! ## The operator and full_merge -/

/-- A merge operator over values `V` and operands `O`. In the engine both are
bytes; here they are any types. `apply v o` folds one operand onto a value:
what the engine's `full_merge` does for each operand in turn. -/
structure Operator (V O : Type) where
  /-- Fold one operand onto a value. -/
  apply : V → O → V

/-- `full_merge(base, operands)`: the operands folded onto the base, oldest
first. This is the value a read returns for a key whose newest replacement
left `base` and whose operands since are `os`. -/
def fullMerge {V O : Type} (M : Operator V O) (base : V) (os : List O) : V :=
  os.foldl M.apply base

/-- `partial_merge` is exact: from every value, applying `a` then `b` equals
applying their partial merge. This is the law that relates two adjacent
operands to the one compaction replaces them with; the plan calls it
"agrees with full_merge for every grouping". -/
def Exact {V O : Type} (M : Operator V O) (pm : O → O → O) : Prop :=
  ∀ v a b, M.apply (M.apply v a) b = M.apply v (pm a b)

/-- `partial_merge` is associative on adjacent operands: combining `a` with
`b` first, or `b` with `c` first, gives the same operand. -/
def Assoc {O : Type} (pm : O → O → O) : Prop :=
  ∀ a b c, pm (pm a b) c = pm a (pm b c)

/-! ## Groupings -/

/-- A grouping of operands: a binary tree whose leaves, left to right, are
the operands in order, and whose inner nodes are partial merges. Every way
compaction can combine a run of adjacent operands into one is such a
tree. -/
inductive Group (O : Type) where
  /-- One operand, not combined with anything. -/
  | leaf (o : O)
  /-- The partial merge of everything on the left with everything on the
  right. -/
  | node (l r : Group O)

/-- The operands of a grouping, oldest first. -/
def Group.leaves {O : Type} : Group O → List O
  | .leaf o => [o]
  | .node l r => l.leaves ++ r.leaves

/-- The single operand a grouping combines its leaves into. -/
def Group.eval {O : Type} (pm : O → O → O) : Group O → O
  | .leaf o => o
  | .node l r => pm (l.eval pm) (r.eval pm)

/-- **One grouping.** With an exact `partial_merge`, applying the operand a
grouping combines into gives the same value as folding its leaves one by
one, from every value. -/
theorem fold_eq_grouping {V O : Type} {M : Operator V O} {pm : O → O → O}
    -- `partial_merge` is exact.
    (hx : Exact M pm) :
    ∀ (g : Group O) (v : V), M.apply v (g.eval pm) = fullMerge M v g.leaves
  | .leaf o, v => by
    -- One operand: both sides apply it once.
    simp [Group.eval, Group.leaves, fullMerge]
  | .node l r, v => by
    -- Apply the left part, then the right part (exactness, read right to
    -- left); each part is a fold of its leaves (the claim for the smaller
    -- trees); and two folds in a row are one fold of the joined list.
    have hl := fold_eq_grouping hx l v
    have hr := fold_eq_grouping hx r (fullMerge M v l.leaves)
    simp only [Group.eval, Group.leaves, fullMerge, List.foldl_append] at *
    rw [← hx, hl, hr]

/-- **Any grouping.** Compaction turns a run of operands into a shorter run,
each output operand combining a group of adjacent inputs. With an exact
`partial_merge`, folding the output gives the value folding the input
gives, from every base. -/
theorem fold_eq_any_grouping {V O : Type} {M : Operator V O} {pm : O → O → O}
    -- `partial_merge` is exact.
    (hx : Exact M pm) :
    ∀ (gs : List (Group O)) (v : V),
      fullMerge M v (gs.map (·.eval pm)) = fullMerge M v (gs.flatMap (·.leaves))
  | [], v => rfl
  | g :: gs, v => by
    -- The first group's operand equals the fold of its leaves; the rest is
    -- the claim for the shorter list, started from that value.
    have h1 := fold_eq_grouping hx g v
    have h2 := fold_eq_any_grouping hx gs (M.apply v (g.eval pm))
    simp only [fullMerge, List.map_cons, List.foldl_cons, List.flatMap_cons,
      List.foldl_append] at *
    rw [h2, h1]

/-- Combining `x` with a left fold equals folding from `x` combined with the
fold's start: associativity, pushed along a list. -/
theorem pm_foldl {O : Type} {pm : O → O → O}
    -- `partial_merge` is associative.
    (ha : Assoc pm) :
    ∀ (rs : List O) (x b : O), pm x (rs.foldl pm b) = rs.foldl pm (pm x b)
  | [], _, _ => rfl
  | c :: rs, x, b => by
    -- One more operand `c`: regroup `pm x (pm b c)` as `pm (pm x b) c`.
    simp only [List.foldl_cons]
    rw [pm_foldl ha rs x (pm b c), ha]

/-- Every grouping combines its leaves `a :: rest` into the left fold
`rest.foldl pm a`, when `partial_merge` is associative. -/
theorem eval_eq_foldl {O : Type} {pm : O → O → O}
    -- `partial_merge` is associative.
    (ha : Assoc pm) :
    ∀ g : Group O, ∃ a rest, g.leaves = a :: rest ∧ g.eval pm = rest.foldl pm a
  | .leaf o => ⟨o, [], rfl, rfl⟩
  | .node l r => by
    -- Each side is a left fold of its own leaves; joining them is one left
    -- fold, by `pm_foldl`.
    obtain ⟨a, ls, hl, el⟩ := eval_eq_foldl ha l
    obtain ⟨b, rs, hr, er⟩ := eval_eq_foldl ha r
    refine ⟨a, ls ++ b :: rs, ?_, ?_⟩
    · simp [Group.leaves, hl, hr]
    · simp only [Group.eval, el, er, List.foldl_append, List.foldl_cons]
      exact pm_foldl ha rs _ b

/-- **Any two groupings agree.** With an associative `partial_merge`, two
groupings of the same operands combine to the same operand. -/
theorem groupings_agree {O : Type} {pm : O → O → O}
    -- `partial_merge` is associative.
    (ha : Assoc pm) (g₁ g₂ : Group O)
    -- The two groupings have the same operands in the same order.
    (h : g₁.leaves = g₂.leaves) :
    g₁.eval pm = g₂.eval pm := by
  -- Both are the left fold of the same list.
  obtain ⟨a, r, h1, e1⟩ := eval_eq_foldl ha g₁
  obtain ⟨b, s, h2, e2⟩ := eval_eq_foldl ha g₂
  rw [h1, h2] at h
  simp only [List.cons.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [e1, e2]

/-! ## Compaction as steps -/

/-- One compaction step: two adjacent operands are replaced by their partial
merge. -/
inductive Step {O : Type} (pm : O → O → O) : List O → List O → Prop
  /-- Operands `a` and `b`, adjacent between `xs` and `ys`, become one. -/
  | merge (xs ys : List O) (a b : O) : Step pm (xs ++ a :: b :: ys) (xs ++ pm a b :: ys)

/-- Any number of compaction steps. -/
inductive Steps {O : Type} (pm : O → O → O) : List O → List O → Prop
  /-- No step. -/
  | refl (l : List O) : Steps pm l l
  /-- Some steps, then one more. -/
  | tail {l₁ l₂ l₃ : List O} : Steps pm l₁ l₂ → Step pm l₂ l₃ → Steps pm l₁ l₃

/-- One step changes no fold, from any base, when `partial_merge` is exact. -/
theorem step_preserves_fold {V O : Type} {M : Operator V O} {pm : O → O → O}
    -- `partial_merge` is exact.
    (hx : Exact M pm) {l₁ l₂ : List O}
    -- One compaction step.
    (h : Step pm l₁ l₂) (v : V) :
    fullMerge M v l₁ = fullMerge M v l₂ := by
  cases h with
  | merge xs ys a b =>
    -- The prefix folds the same; then `a` and `b` in turn equal their
    -- partial merge (exactness); the suffix folds the same from there.
    simp only [fullMerge, List.foldl_append, List.foldl_cons]
    rw [hx]

/-- **Compaction keeps every read.** Any sequence of compaction steps, each
combining two adjacent operands with an exact `partial_merge`, leaves the
fold of the operands unchanged from every base. -/
theorem steps_preserve_fold {V O : Type} {M : Operator V O} {pm : O → O → O}
    -- `partial_merge` is exact.
    (hx : Exact M pm) {l₁ l₂ : List O}
    -- Any number of compaction steps.
    (h : Steps pm l₁ l₂) (v : V) :
    fullMerge M v l₁ = fullMerge M v l₂ := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [ih, step_preserves_fold hx hs]

/-! ## The touches law -/

/-- What a projected read sees of a value: `proj v p` is the value of part
`p`, and `touches o S` is the operator's answer to "does operand `o` change
any part in `S`" (`MergeOperator::touches`, default true). -/
structure Parts (V O P W : Type) where
  /-- The value of one part of a value. -/
  proj : V → P → W
  /-- Whether an operand changes any of the named parts. -/
  touches : O → List P → Bool

/-- The contract `touches` keeps: when it answers false for a set of parts,
applying the operand to any value leaves every one of those parts as it
was. Answering true is always safe; that is the default. -/
def TouchesSound {V O P W : Type} (M : Operator V O) (T : Parts V O P W) : Prop :=
  ∀ v o S, T.touches o S = false → ∀ p ∈ S, T.proj (M.apply v o) p = T.proj v p

/-- **The touches law.** A run of operands none of which touches a part in
`S` leaves every part in `S` as it was: what a projected read over `S`
decided on is unchanged. -/
theorem touches_law {V O P W : Type} {M : Operator V O} {T : Parts V O P W}
    -- `touches` keeps its contract.
    (hs : TouchesSound M T) {S : List P} :
    ∀ (os : List O) (v : V),
      -- No operand touches a part in `S`.
      (∀ o ∈ os, T.touches o S = false) →
      ∀ p ∈ S, T.proj (fullMerge M v os) p = T.proj v p
  | [], _, _, _, _ => rfl
  | o :: os, v, hos, p, hp => by
    -- The rest of the run leaves part `p` as the first operand left it
    -- (the claim for the shorter run, from the new value), and the first
    -- operand left it as it was (the contract).
    have ih := touches_law hs os (M.apply v o)
      (fun o' h' => hos o' (List.mem_cons_of_mem _ h')) p hp
    have h1 := hs v o S (hos o List.mem_cons_self) p hp
    simp only [fullMerge, List.foldl_cons] at ih ⊢
    rw [ih, h1]

/-- The contract `touches` keeps across a partial merge (plan 3.3): the
combined operand touches a set of parts exactly when one of its two inputs
does. -/
def TouchesPartial {V O P W : Type} (T : Parts V O P W) (pm : O → O → O) : Prop :=
  ∀ a b S, T.touches (pm a b) S = (T.touches a S || T.touches b S)

/-- With that contract, the operand a grouping combines into touches a set
of parts exactly when one of its leaves does. -/
theorem touches_grouping {V O P W : Type} {T : Parts V O P W} {pm : O → O → O}
    -- `touches` of a partial merge is the `or` of its inputs.
    (hp : TouchesPartial T pm) (S : List P) :
    ∀ g : Group O, T.touches (g.eval pm) S = g.leaves.any (fun o => T.touches o S)
  | .leaf o => by simp [Group.eval, Group.leaves]
  | .node l r => by
    -- The node's answer is the `or` of its two sides' answers.
    simp only [Group.eval, Group.leaves, List.any_append]
    rw [hp, touches_grouping hp S l, touches_grouping hp S r]

/-- **The touches law survives compaction.** A combined operand whose
`touches` answers false for `S` leaves every part in `S` as it was, when
`partial_merge` is exact and `touches` keeps both contracts. -/
theorem touches_survives_compaction {V O P W : Type} {M : Operator V O}
    {T : Parts V O P W} {pm : O → O → O}
    -- `partial_merge` is exact.
    (hx : Exact M pm)
    -- `touches` keeps its contract on single operands.
    (hs : TouchesSound M T)
    -- `touches` of a partial merge is the `or` of its inputs.
    (hp : TouchesPartial T pm) (g : Group O) (S : List P)
    -- The combined operand touches no part in `S`.
    (hg : T.touches (g.eval pm) S = false) (v : V) :
    ∀ p ∈ S, T.proj (M.apply v (g.eval pm)) p = T.proj v p := by
  intro p hpS
  -- No leaf touches `S`, since their `or` is false.
  have hleaves : ∀ o ∈ g.leaves, T.touches o S = false := by
    intro o ho
    rw [touches_grouping hp S g] at hg
    cases h : T.touches o S with
    | false => rfl
    | true =>
      have : g.leaves.any (fun o => T.touches o S) = true := List.any_eq_true.mpr ⟨o, ho, h⟩
      rw [this] at hg
      cases hg
  -- The combined operand acts as its leaves folded one by one, and those
  -- leave `p` as it was.
  rw [fold_eq_grouping hx g v]
  exact touches_law hs g.leaves v hleaves p hpS

/-! ## The RED case: an inexact partial merge -/

/-- An operator that rounds down to an even number after every operand, as a
floating-point sum rounds after every addition. -/
def roundSum : Operator Nat Nat := ⟨fun v o => (v + o) / 2 * 2⟩

/-- **`inexact_breaks_fold`.** Declaring "add the operands" as this
operator's partial merge breaks fold equality: folding operands 1 and 1
onto 0 rounds twice and gives 0, while their partial merge 2 applied to 0
gives 2. So compaction with it would change what a read returns. -/
theorem inexact_breaks_fold :
    fullMerge roundSum 0 [1, 1] = 0 ∧
      roundSum.apply 0 ((Group.node (.leaf 1) (.leaf 1)).eval (· + ·)) = 2 := by
  -- Both sides are closed arithmetic.
  decide

/-- The same fact as a failure of the contract: "add the operands" is not an
exact partial merge for `roundSum`. -/
theorem roundSum_not_exact : ¬ Exact roundSum (· + ·) := by
  intro h
  -- Exactness at value 0 with operands 1 and 1 would say 0 = 2.
  have := h 0 1 1
  revert this
  decide

/-! ## The part operand of RepeatableRead.tla keeps the contract -/

/-- The part key of RepeatableRead.tla as a pair of parts, and its operands as
pairs of increments: an operand adds its first number to part 1 and its
second to part 2. The model's operands add one to each part they touch. -/
def partOperator : Operator (Nat × Nat) (Nat × Nat) :=
  ⟨fun v o => (v.1 + o.1, v.2 + o.2)⟩

/-- Its partial merge adds the increments. -/
def partMerge (a b : Nat × Nat) : Nat × Nat := (a.1 + b.1, a.2 + b.2)

/-- An operand touches part 1 when it adds to part 1, part 2 when it adds to
part 2, and no other part. -/
def touchesPart (o : Nat × Nat) (p : Nat) : Bool :=
  (p == 1 && o.1 != 0) || (p == 2 && o.2 != 0)

/-- Parts 1 and 2 of the pair; any other part reads 0. `touches` asks each
named part. -/
def partParts : Parts (Nat × Nat) (Nat × Nat) Nat Nat :=
  ⟨fun v p => if p = 1 then v.1 else if p = 2 then v.2 else 0,
   fun o S => S.any (touchesPart o)⟩

/-- Adding increments is an exact partial merge. -/
theorem part_operator_exact : Exact partOperator partMerge := by
  intro v a b
  -- Componentwise, (x + a) + b = x + (a + b).
  simp [partOperator, partMerge, Nat.add_assoc]

/-- Adding increments is associative. -/
theorem part_operator_assoc : Assoc partMerge := by
  intro a b c
  simp [partMerge, Nat.add_assoc]

/-- Its `touches` keeps the contract: an operand that touches none of the
named parts adds nothing to any of them. -/
theorem part_operator_touches_sound : TouchesSound partOperator partParts := by
  intro v o S h p hp
  -- `p` is named and the operand touches no named part, so it does not
  -- touch `p`.
  have hp' : touchesPart o p = false := by
    cases ht : touchesPart o p with
    | false => rfl
    | true =>
      have : S.any (touchesPart o) = true := List.any_eq_true.mpr ⟨p, hp, ht⟩
      simp only [partParts] at h
      rw [this] at h
      cases h
  simp only [touchesPart, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
    bne_eq_false_iff_eq] at hp'
  -- Part 1 untouched means the operand adds 0 to it, and the same for part 2.
  simp only [partParts, partOperator]
  by_cases h1 : p = 1
  · subst h1; simp at hp' ⊢; omega
  · by_cases h2 : p = 2
    · subst h2; simp at hp' ⊢; omega
    · simp [h1, h2]

/-- A sum of two naturals is nonzero exactly when one of them is. -/
theorem bne_zero_add (x y : Nat) : (x + y != 0) = ((x != 0) || (y != 0)) := by
  -- As propositions: x + y ≠ 0 exactly when x ≠ 0 or y ≠ 0.
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq, Bool.or_eq_true]
  omega

/-- A combined operand touches one part exactly when one of its inputs does. -/
theorem touchesPart_merge (a b : Nat × Nat) (p : Nat) :
    touchesPart (partMerge a b) p = (touchesPart a p || touchesPart b p) := by
  simp only [touchesPart, partMerge, bne_zero_add]
  -- Every combination of the six booleans involved.
  generalize (p == 1) = c1
  generalize (p == 2) = c2
  generalize (a.1 != 0) = x1
  generalize (b.1 != 0) = y1
  generalize (a.2 != 0) = x2
  generalize (b.2 != 0) = y2
  cases c1 <;> cases c2 <;> cases x1 <;> cases y1 <;> cases x2 <;> cases y2 <;> rfl

/-- Its `touches` keeps the partial-merge contract: a combined operand adds to
a part exactly when one of its inputs does. -/
theorem part_operator_touches_partial : TouchesPartial partParts partMerge := by
  intro a b S
  simp only [partParts]
  -- Part by part, by `touchesPart_merge`.
  induction S with
  | nil => rfl
  | cons p S ih =>
    simp only [List.any_cons, ih, touchesPart_merge]
    generalize touchesPart a p = x
    generalize touchesPart b p = y
    generalize S.any (touchesPart a) = u
    generalize S.any (touchesPart b) = w
    cases x <;> cases y <;> cases u <;> cases w <;> rfl

end Regolith.MergeOperator
