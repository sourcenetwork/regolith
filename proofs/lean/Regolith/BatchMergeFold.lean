import Regolith.MergeOperator

/-!
A commit may replace two adjacent operands with the caller's exact partial
merge. For example, [+1, +1] becomes [+2]. It must not reorder operands,
invent an answer when the caller declines, or rewrite an older commit.
These proofs cover every base and every surrounding operand sequence.
Publication and snapshot registration remain the existing pipeline's job.
-/

namespace Regolith.BatchMergeFold

open Regolith.MergeOperator

/-- A successful callback agrees with the original pair from every base. -/
def ExactAccepted {V O : Type} (M : Operator V O)
    (pm : O → O → Option O) : Prop :=
  -- Only successful callbacks authorize replacing the pair.
  ∀ a b out, pm a b = some out → ∀ v,
    M.apply (M.apply v a) b = M.apply v out

/-- One accepted replacement, at the same key within one atomic commit. -/
inductive Step {O : Type} (pm : O → O → Option O) : List O → List O → Prop
  -- The prefix and suffix are unchanged; a declined callback has no step.
  | accepted (xs ys : List O) (a b out : O)
      (ok : pm a b = some out) :
      Step pm (xs ++ a :: b :: ys) (xs ++ out :: ys)

/-- Any accepted replacement keeps the read, including its surrounding writes. -/
theorem step_preserves_read {V O : Type} {M : Operator V O}
    {pm : O → O → Option O} (lawful : ExactAccepted M pm)
    {before after : List O} (step : Step pm before after) (base : V) :
    fullMerge M base before = fullMerge M base after := by
  -- A step carries both the original adjacent pair and the callback's success.
  cases step with
  | accepted xs ys a b out ok =>
    -- Fold the unchanged prefix, then the pair, then the unchanged suffix.
    simp only [fullMerge, List.foldl_append, List.foldl_cons]
    -- Exactness makes the two starting values for the suffix equal.
    rw [lawful a b out ok]

/-- Zero or more accepted replacements within the same commit. -/
inductive Steps {O : Type} (pm : O → O → Option O) : List O → List O → Prop
  -- Not folding is always permitted, including for a declined callback.
  | refl (ops : List O) : Steps pm ops ops
  -- Each new step must carry its own successful callback.
  | tail {a b c : List O} : Steps pm a b → Step pm b c → Steps pm a c

/-- Repeated accepted replacements preserve the read from every base. -/
theorem steps_preserve_read {V O : Type} {M : Operator V O}
    {pm : O → O → Option O} (lawful : ExactAccepted M pm)
    {before after : List O}
    (steps : Steps pm before after) (base : V) :
    fullMerge M base before = fullMerge M base after := by
  -- An empty sequence is equality; every additional step keeps that equality.
  induction steps with
  | refl => rfl
  | tail _ step ih => exact ih.trans (step_preserves_read lawful step base)

/-- Folding a later commit cannot change a read of the older commit alone. -/
theorem earlier_read_unchanged {V O : Type} (M : Operator V O)
    (base : V) (older : List O) (laterBefore laterAfter : List O)
    (read : fullMerge M (fullMerge M base older) laterBefore =
      fullMerge M (fullMerge M base older) laterAfter) :
    fullMerge M base older = fullMerge M base older ∧
      fullMerge M base (older ++ laterBefore) =
        fullMerge M base (older ++ laterAfter) := by
  -- The old sequence is not rewritten; concatenated folds use the supplied equality.
  constructor
  · rfl
  · simpa only [fullMerge, List.foldl_append] using read

end Regolith.BatchMergeFold
