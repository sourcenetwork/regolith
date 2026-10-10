/-!
# ShardedStats: per-thread ticker shards add up to every increment

THE STORY. regolith counts what it does in tickers. One shared counter per
ticker makes every core write the same memory, so each ticker is split into
shards, one per thread number (`src/statistics.rs`). A thread adds to its own
shard with one atomic add; threads past the shard count share shards. A
read adds the shards up, one load at a time, while other threads may still
be adding. Tiny example: threads A and B share shard 0 and thread C has
shard 1; A adds 2, B adds 3, C adds 5; a read after all of that must say 10.

WHAT IS PROVED, for any number of shards and any list of adds:

1. `total_after_adds`: after any adds, the shards sum to what they summed
   before plus every amount added. Two threads on one shard lose nothing,
   because each add is applied whole. Backs `QuiescentExact` in
   `proofs/tla/ShardedStats.tla`.
2. `read_between`: a read that loads each shard at some moment between `t0`
   and `t1` reports a total between the true totals at `t0` and at `t1`,
   because shards only grow. Backs `ReadBetween`.
3. `reads_monotone`: a read that loads every shard no earlier than an
   earlier read did never reports less. Backs `NeverBackwards`.
4. `lost_update_drops_an_add`: the RED case, an add made as a load then a
   store, loses an add when two threads share a shard.
-/

-- Everything below lives under this name, so it cannot clash with other files.
namespace Regolith.ShardedStats

/-- The sum of `f 0`, `f 1`, ..., `f (n - 1)`: the shards' values added up,
the way `Statistics::get_ticker` folds them. -/
def sumTo (f : Nat → Nat) : Nat → Nat
  -- No shards: nothing.
  | 0 => 0
  -- The first `n` shards, then shard `n`.
  | n + 1 => sumTo f n + f n

/-- Raising every shard (below `n`) raises the sum: the step every bound
below rests on. -/
theorem sumTo_le (f g : Nat → Nat) :
    ∀ n, (∀ s, s < n → f s ≤ g s) → sumTo f n ≤ sumTo g n := by
  -- One shard at a time.
  intro n
  induction n with
  | zero =>
    -- No shards: both sums are 0.
    intro _
    exact Nat.le_refl 0
  | succ k ih =>
    -- The first `k` shards obey the bound, and so does shard `k`.
    intro h
    -- Add the two bounds together.
    exact Nat.add_le_add (ih (fun s hs => h s (by omega))) (h k (by omega))

/-- One add: `amount` onto shard `shard`. -/
structure Add where
  /-- The shard the adding thread uses. -/
  shard : Nat
  /-- How much it adds. -/
  amount : Nat

/-- What one atomic add does: its shard gains the whole amount, the others
stay. This is `fetch_add`: it cannot be split by another thread. -/
def apply (v : Nat → Nat) (x : Add) : Nat → Nat :=
  -- The chosen shard gains; every other shard keeps its value.
  fun s => if s = x.shard then v s + x.amount else v s

/-- Apply a list of adds in order. -/
def applyAll (v : Nat → Nat) : List Add → (Nat → Nat)
  -- No adds: unchanged.
  | [] => v
  -- The first add, then the rest.
  | x :: xs => applyAll (apply v x) xs

/-- The sum of the amounts of a list of adds. -/
def amounts : List Add → Nat
  -- No adds: nothing.
  | [] => 0
  -- The first amount plus the rest.
  | x :: xs => x.amount + amounts xs

/-- Two shard maps that agree on every shard below `n` have the same sum
over the first `n`. -/
theorem sumTo_congr (f g : Nat → Nat) :
    ∀ n, (∀ s, s < n → f s = g s) → sumTo f n = sumTo g n := by
  -- One shard at a time.
  intro n
  induction n with
  | zero =>
    -- No shards: both sums are 0.
    intro _
    rfl
  | succ k ih =>
    -- The maps agree below `k + 1`.
    intro h
    -- Write both sums as "the first `k`, then shard `k`".
    show sumTo f k + f k = sumTo g k + g k
    -- The first `k` agree by the induction, shard `k` by the assumption.
    rw [ih (fun s hs => h s (by omega)), h k (by omega)]

/-- One add raises the sum of the first `n` shards by its amount, when its
shard is one of them. -/
theorem sumTo_apply (v : Nat → Nat) (x : Add) :
    ∀ n, x.shard < n → sumTo (apply v x) n = sumTo v n + x.amount := by
  -- One shard at a time.
  intro n
  induction n with
  | zero =>
    -- No shard is below 0, so this case cannot happen.
    intro h
    omega
  | succ k ih =>
    -- The add's shard is among the first `k + 1`.
    intro h
    -- Write both sums as "the first `k`, then shard `k`".
    show sumTo (apply v x) k + apply v x k = (sumTo v k + v k) + x.amount
    -- Either the add's shard is the last one, `k`, or it is earlier.
    by_cases hk : x.shard = k
    · -- It is shard `k`: no shard below `k` is touched...
      have hrest : sumTo (apply v x) k = sumTo v k :=
        sumTo_congr _ _ k (fun s hs => by simp [apply, show s ≠ x.shard by omega])
      -- ...and shard `k` gains the whole amount.
      have hlast : apply v x k = v k + x.amount := by simp [apply, hk]
      -- Put the two together and rearrange.
      rw [hrest, hlast]
      omega
    · -- It is earlier: the first `k` gain the amount, by the induction...
      have hrest := ih (by omega)
      -- ...and shard `k` is not the add's shard, so it is unchanged.
      have hlast : apply v x k = v k := by simp [apply, show k ≠ x.shard by omega]
      -- Put the two together and rearrange.
      rw [hrest, hlast]
      omega

/-- **`total_after_adds`.** After any list of adds whose shards are all
among the first `n`, the shards sum to their old sum plus every amount
added. Shared shards change nothing: each add lands whole. Example ruled
out: two threads share shard 0, each adds 1, and the sum grows by 1. -/
theorem total_after_adds (n : Nat) :
    ∀ (xs : List Add) (v : Nat → Nat), (∀ x ∈ xs, x.shard < n) →
      sumTo (applyAll v xs) n = sumTo v n + amounts xs := by
  -- One add at a time.
  intro xs
  induction xs with
  | nil =>
    -- No adds: nothing changes and nothing was added.
    intro v _
    rfl
  | cons x xs ih =>
    -- The first add, then the rest.
    intro v h
    -- The rest, by the induction, from the state after the first add.
    simp only [applyAll, amounts]
    rw [ih (apply v x) (fun y hy => h y (List.mem_cons_of_mem x hy))]
    -- The first add raised the sum by its amount.
    rw [sumTo_apply v x n (h x (List.mem_cons_self))]
    -- Rearrange the additions.
    omega

/-- Shards over time: `V t s` is shard `s` at moment `t`. Shards only grow
between resets: an add never lowers one. -/
def Grows (V : Nat → Nat → Nat) : Prop := ∀ s t t', t ≤ t' → V t s ≤ V t' s

/-- What a read reports when it loads shard `s` at moment `when s`. -/
def readTotal (V : Nat → Nat → Nat) (when : Nat → Nat) (n : Nat) : Nat :=
  -- Each shard as the read saw it, added up.
  sumTo (fun s => V (when s) s) n

/-- **`read_between`.** A read that loads every shard at some moment between
`t0` and `t1` reports at least the true total at `t0` and at most the true
total at `t1`. Example ruled out: a read reporting 7 after the total was
already 10 when it began. -/
theorem read_between (V : Nat → Nat → Nat) (hV : Grows V) (when : Nat → Nat)
    (n t0 t1 : Nat) (h0 : ∀ s, s < n → t0 ≤ when s) (h1 : ∀ s, s < n → when s ≤ t1) :
    sumTo (V t0) n ≤ readTotal V when n ∧ readTotal V when n ≤ sumTo (V t1) n := by
  -- Both halves compare the sums shard by shard.
  constructor
  · -- Each shard at its load is at least what it was at `t0`.
    exact sumTo_le _ _ n (fun s hs => hV s _ _ (h0 s hs))
  · -- Each shard at its load is at most what it is at `t1`.
    exact sumTo_le _ _ n (fun s hs => hV s _ _ (h1 s hs))

/-- **`reads_monotone`.** A later read that loads every shard no earlier
than an earlier read loaded it never reports less. That is what the code
gets from per-location coherence: a load of a shard after an earlier load
of it sees the same value or a newer one. Example ruled out: two reads on
one thread reporting 10 then 9. -/
theorem reads_monotone (V : Nat → Nat → Nat) (hV : Grows V) (first second : Nat → Nat)
    (n : Nat) (h : ∀ s, s < n → first s ≤ second s) :
    readTotal V first n ≤ readTotal V second n :=
  -- Shard by shard, the later load sees at least as much.
  sumTo_le _ _ n (fun s hs => hV s _ _ (h s hs))

/-! ## The RED case: an add made as a load then a store -/

/-- An add made as a load then a store: the shard becomes what the thread
loaded, plus one. Another thread's store in between is overwritten. -/
def storeAfterLoad (loaded : Nat) : Nat := loaded + 1

/-- RED `LostUpdate`: two threads share shard 0, which holds 0. Both load 0
before either stores. The first stores `0 + 1`; the second stores `0 + 1`
over it, and the shard keeps that last store. -/
def lostUpdate : Nat :=
  -- The second thread's store, of what it loaded (0) plus one, is last.
  storeAfterLoad 0

/-- **`lost_update_drops_an_add`.** Two adds of 1 were made and the shard
says 1, not 2. With one atomic add (`apply`) the same two adds give 2. -/
theorem lost_update_drops_an_add :
    lostUpdate = 1 ∧
      sumTo (applyAll (fun _ => 0) [⟨0, 1⟩, ⟨0, 1⟩]) 1 = 2 := by
  -- Both are small computations.
  decide

end Regolith.ShardedStats
