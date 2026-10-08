import Lean
import Regolith

/-!
# Audit: every Regolith theorem rests on Lean's standard foundations only

`just lean` runs this file after `lake build`. It walks every declaration
in the `Regolith` namespace and lists the foundational assumptions its
proof depends on. Lean's own three (`propext`, `Classical.choice`,
`Quot.sound`) are allowed. Anything else fails the check: an unfinished
proof shows up here as `sorryAx`, and an assumption added by hand shows up
under its own name.
-/

open Lean
/-- Fail, naming each offender, unless every `Regolith` declaration depends
only on the allowed assumptions. -/
def auditRegolith : CoreM Unit := do
  -- Lean's standard assumptions: propositional extensionality, choice,
  -- and quotient soundness.
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  -- Every declaration whose name starts with `Regolith`.
  let names := env.constants.toList.filterMap fun (n, _) =>
    if (`Regolith).isPrefixOf n then some n else none
  let mut bad : Array (Name × Name) := #[]
  for n in names do
    for a in ← collectAxioms n do
      if !allowed.contains a then
        bad := bad.push (n, a)
  if bad.isEmpty then
    IO.println s!"audit: {names.length} Regolith declarations, standard foundations only"
  else
    throwError m!"audit: declarations resting on a disallowed assumption: {bad.toList}"

#eval auditRegolith
