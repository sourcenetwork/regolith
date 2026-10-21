/- A completed read's caller can resume after any number of other I/O polls.
   The queue retains its landing while a caller handle exists. Once no caller
   exists, the old grace-period rule reclaims it. LandingLifetime.tla checks
   interleaved clones, drops, polling and resumption; these laws hold at every
   age and grace period. Correspondence: keep is Ledger::settle's expiry guard,
   live is a caller Arc beyond Ledger's ownership, age is its poll count. -/
namespace Regolith.LandingLifetime

-- An active caller or the grace period protects a completed wait.
def keep (live : Bool) (age grace : Nat) : Bool :=
  -- Caller ownership wins regardless of elapsed polls.
  live || decide (age ≤ grace)

-- No delay can evict a landing whose caller is still alive.
theorem live_retained (age grace : Nat) : keep true age grace = true := by
  -- The live branch decides the disjunction.
  simp [keep]

-- A cancelled wait past its grace period is reclaimable.
theorem abandoned_expires (age grace : Nat) (old : grace < age) :
    -- Its landing can be released.
    keep false age grace = false := by
  -- Natural-number order makes the grace test false.
  simp [keep, Nat.not_le_of_lt old]

-- A cancelled wait within its grace period is still retained.
theorem grace_retained (age grace : Nat) (young : age ≤ grace) :
    -- Its landing remains protected.
    keep false age grace = true := by
  -- The grace branch decides the disjunction.
  simp [keep, young]

-- Only an absent caller can have an expired landing.
theorem expiry_has_no_caller (live : Bool) (age grace : Nat)
    -- Expiry therefore witnesses the absence of a caller.
    (expired : keep live age grace = false) : live = false := by
  -- Check the two possible ownership states.
  cases live with
  -- No caller is the required result.
  | false => rfl
  -- A live caller contradicts expiry.
  | true => simp [keep] at expired

-- Another read can consume a retained wait only when its caller is gone.
def releaseCovered (live : Bool) : Bool := !live

-- Reading the same block elsewhere cannot release a live caller's hold.
theorem other_read_retains_live : releaseCovered true = false := by
  -- A live caller vetoes release independently of what another read found.
  rfl

-- End of the completed-wait lifetime laws.
end Regolith.LandingLifetime
