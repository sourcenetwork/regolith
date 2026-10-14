import Regolith.MergeOperator

/-!
# Validation: every key class's commit rule gives a serial history (plan 3.1 to 3.15)

This file backs the TLA+ model `proofs/tla/RepeatableRead.tla`, whose commit
rule is in `RepeatableReadCommit.tla` (`KeptReads`, `ReadDecider`,
`MergeDecider`, `ScanDecider`, `CaExempt`, `ValidatesNothing`). TLC checks
the rules over every interleaving of a few transactions, with invariants
about what each workload decided (`INV_NoStaleDefinition`,
`INV_PartsCurrent`, `INV_ValueReadsCurrent`, `INV_ScanDecisionsCurrent`,
`INV_HoldsCurrent`, `INV_NoDanglingReference`, `INV_WriteFreeConsistent`,
`INV_LogDense`, `INV_CounterExact`). The theorems here hold for every number
of transactions, keys and writes.

## The model

A state maps every key to a value; both are natural numbers and 0 is an
absent key. A transaction reads a snapshot: the state after the commits it
saw. It decides its writes from what it read, and its writes are applied at
its commit, in commit order, on whatever the state is then: a put stores a
value, a merge folds an operand onto the current value, an append takes the
log's next position. That is how the engine applies a commit.

"The history is serial in commit order" means: the state after every commit
equals the state the same transactions reach run one at a time in commit
order, each reading the state just before its own commit (`serial`). A
history keeps that when every transaction's decision at its snapshot has the
same effect as its decision at its commit point would have (`lift`).

A transaction's reads are recorded by class (`Read`), each with the rule the
commit checks against the writes committed since its snapshot (`Ok`) and
what the rule guarantees about the read between the snapshot and the commit
(`Agree`):

* `full`: validated by sequence, as every level validates a read: no newer
  write of the key. The key's value is unchanged.
* `value`: DefraLevel (plan 3.5): the newest newer write of the key is a put
  of exactly the value read, or a delete when it read nothing. The value is
  unchanged; an identical rewrite (ABA) is not a change.
* `presence`: a content-addressed key that held a value (E17): the newest
  newer write is not a removal. Only presence is guaranteed: the class's
  relaxation is that the bytes never differ, which the caller promises.
* `parts`: a projected read (plan 3.4): walking the newer writes newest
  first, the first that changes a named part (a put, a delete, a range
  delete, or an operand `touches` says touches the parts) must be a put of
  exactly the value read. Existence and the named parts are unchanged.
* `scan`: a validated scan (plan 3.15): no newer write inside the range.
  Every key of the range is unchanged, so no key left and none appeared.
* `exempt`: never validated: a Log read, a scan stretch inside a commutative
  prefix, `get_parts` with no part. Nothing is guaranteed; the caller must
  not decide on it.

The caller's side is `Contract`: a transaction's writes depend only on what
its validated reads guarantee. Content-addressed creates are the one
exception the classes allow: a transaction may put a content-addressed key
because it read it as absent, and that read is dropped (D7). The class's
relaxation makes that safe: the key's bytes are fixed (`Env.bytes`), so a
put of them over a key that holds them changes nothing.

Choices this model makes, each recorded here because the plan leaves it
open:

* The fallbacks of a projected read (in full when it found nothing or when
  the transaction puts the key) are which `Read` the engine records; the
  theorems hold for whichever it records, as long as the decision uses only
  what that read's `Agree` covers. A put derived from the read uses every
  part, which is why the engine must record it in full.
* Write-write checks (first committer wins, the validated content-addressed
  delete, the blind-merge rule) are not needed for the equivalence proved
  here: a blind write applies at commit, which is its serial position. They
  protect callers' protocols, which the TLA+ model checks
  (`INV_NoDanglingReference`, `INV_CounterExact`), and the blind-merge rule
  is what lets a merge also be placed at its snapshot
  (`Relaxations.lean`, `blindMerge_commutes`).

## What is proved, in plain words

1. One theorem per class: if every committed transaction's reads are of
   that class and passed its rule, the history is serial in commit order:
   `ordinary_serial`, `value_serial`, `contentAddressed_serial`,
   `parts_serial`, `scan_serial`, `exempt_serial` (Log reads, commutative
   stretches, empty parts) and `blindMerge_serial`. Each rests on its rule's
   soundness lemma (`full_current`, `value_current`, `presence_current`,
   `parts_current`, `scan_current`).
2. `all_classes_serial`: the same for any mix of classes, creates included.
3. Content-addressed puts are idempotent: `ca_put_idempotent`, and
   `ca_commit_point`, the step `contentAddressed_serial` rests on.

`Regolith/Relaxations.lean` continues this file with every other class's
relaxation stated exactly (blind merges commute, Log appends are
commit-ordered, an identical rewrite is not a change, commutative writers
leave the union, a write-free transaction reads one point in time) and with
the RED cases as counterexamples.

How to read the Lean: `def` defines a function or a property, `structure`
groups named fields, `inductive` lists the forms a value can take, and
`theorem` states a fact whose proof follows `:= by`. Lines starting with
`--` are comments; each proof step is commented.
-/

namespace Regolith.Validation

open Regolith.MergeOperator

/-! ## States, writes and the environment -/

/-- A database state: the value of every key. Keys and values are natural
numbers, and value 0 is an absent key. -/
abbrev State := Nat → Nat

/-- What the classes and the operator are, fixed for a database. -/
structure Env where
  /-- The merge operator: `op.apply v o` folds operand `o` onto value `v`. -/
  op : Operator Nat Nat
  /-- An operand always leaves a value: a merge never deletes. -/
  apply_ne_zero : ∀ v o, op.apply v o ≠ 0
  /-- The parts of a value and the operator's `touches`. -/
  parts : Parts Nat Nat Nat Nat
  /-- `touches` keeps its contract (MergeOperator.lean). -/
  touches_sound : TouchesSound op parts
  /-- The log's head key: it holds the newest assigned position. -/
  head : Nat
  /-- The key of the log entry at position `p`. -/
  entry : Nat → Nat
  /-- The keys the classifier declares Log. -/
  isLog : Nat → Bool
  /-- The head is a Log key. -/
  isLog_head : isLog head = true
  /-- Every entry is a Log key. -/
  isLog_entry : ∀ p, isLog (entry p) = true
  /-- Two positions never share a key. -/
  entry_inj : ∀ p q, entry p = entry q → p = q
  /-- No entry is the head. -/
  entry_ne_head : ∀ p, entry p ≠ head
  /-- The keys the classifier declares content-addressed. -/
  isCA : Nat → Bool
  /-- A key has one class. -/
  ca_not_log : ∀ k, isCA k = true → isLog k = false
  /-- The bytes a content-addressed key determines. -/
  bytes : Nat → Nat
  /-- Those bytes are a value, never absent. -/
  bytes_ne_zero : ∀ k, bytes k ≠ 0
  /-- The state before any commit. -/
  init : State

/-- One write of a commit. -/
inductive Write where
  /-- Store value `v` under key `k`. -/
  | put (k v : Nat)
  /-- Remove key `k`. -/
  | del (k : Nat)
  /-- Fold operand `o` onto key `k`'s value. -/
  | merge (k o : Nat)
  /-- Remove every key `j` with `lo ≤ j < hi` (`Db::delete_range`). -/
  | rangeDel (lo hi : Nat)
  /-- Append entry `e` to the log at the next position (plan 3.6). -/
  | append (e : Nat)

/-- State `σ` with key `k` set to `v`. -/
def upd (σ : State) (k v : Nat) : State := fun j => if j = k then v else σ j

/-- One write applied to a state, at commit. An append reads the head the
state holds now: that is where the ordered step assigns positions. -/
def applyWrite (E : Env) (σ : State) : Write → State
  | .put k v => upd σ k v
  | .del k => upd σ k 0
  | .merge k o => upd σ k (E.op.apply (σ k) o)
  | .rangeDel lo hi => fun j => if lo ≤ j ∧ j < hi then 0 else σ j
  | .append e => upd (upd σ (E.entry (σ E.head + 1)) e) E.head (σ E.head + 1)

/-- A list of writes applied in order: a commit in operation order, or many
commits in commit order. -/
def applyWrites (E : Env) (σ : State) (ws : List Write) : State :=
  ws.foldl (applyWrite E) σ

/-- No writes leave the state. -/
theorem applyWrites_nil (E : Env) (σ : State) : applyWrites E σ [] = σ := rfl

/-- The first write, then the rest. -/
theorem applyWrites_cons (E : Env) (σ : State) (w : Write) (ws : List Write) :
    applyWrites E σ (w :: ws) = applyWrites E (applyWrite E σ w) ws := rfl

/-- Whether a write can change key `k`. An append can change any Log key,
since its position depends on the head at commit. -/
def affects (E : Env) (k : Nat) : Write → Bool
  | .put j _ => decide (j = k)
  | .del j => decide (j = k)
  | .merge j _ => decide (j = k)
  | .rangeDel lo hi => decide (lo ≤ k ∧ k < hi)
  | .append _ => E.isLog k

/-- A write that cannot change `k` leaves it as it was. -/
theorem applyWrite_unaffected (E : Env) (σ : State) (w : Write) (k : Nat)
    -- `w` does not affect `k`.
    (h : affects E k w = false) :
    applyWrite E σ w k = σ k := by
  cases w with
  | put j v =>
    -- `j ≠ k`, so the update is elsewhere.
    simp only [affects, decide_eq_false_iff_not] at h
    simp [applyWrite, upd, Ne.symm h]
  | del j =>
    simp only [affects, decide_eq_false_iff_not] at h
    simp [applyWrite, upd, Ne.symm h]
  | merge j o =>
    simp only [affects, decide_eq_false_iff_not] at h
    simp [applyWrite, upd, Ne.symm h]
  | rangeDel lo hi =>
    -- `k` lies outside the range.
    simp only [affects, decide_eq_false_iff_not] at h
    simp [applyWrite, h]
  | append e =>
    -- `k` is not a Log key, so it is neither the head nor an entry.
    simp only [affects] at h
    have h1 : k ≠ E.head := fun hk => by rw [hk, E.isLog_head] at h; cases h
    have h2 : k ≠ E.entry (σ E.head + 1) := fun hk => by
      rw [hk, E.isLog_entry] at h; cases h
    simp [applyWrite, upd, h1, h2]

/-- Writes that cannot change `k` leave it as it was. -/
theorem applyWrites_unaffected (E : Env) (k : Nat) :
    ∀ (ws : List Write) (σ : State), (∀ w ∈ ws, affects E k w = false) →
      applyWrites E σ ws k = σ k
  | [], _, _ => rfl
  | w :: ws, σ, h => by
    -- The first write leaves `k`; then the rest do.
    simp only [applyWrites_cons] at *
    rw [applyWrites_unaffected E k ws _ (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))]
    exact applyWrite_unaffected E σ w k (h w List.mem_cons_self)

/-- Applying two lists in turn is applying them joined. -/
theorem applyWrites_append (E : Env) (σ : State) (a b : List Write) :
    applyWrites E σ (a ++ b) = applyWrites E (applyWrites E σ a) b := by
  simp [applyWrites, List.foldl_append]

/-! ## The newest write that matters, newest first -/

/-- The newest write of `ws` that satisfies `q`, if any: the first one a walk
from the newest end meets. -/
def lastWhere (q : Write → Bool) : List Write → Option Write
  | [] => none
  | w :: ws =>
    match lastWhere q ws with
    | some x => some x
    | none => if q w then some w else none

/-- When no write satisfies `q`, the walk finds nothing. -/
theorem lastWhere_none {q : Write → Bool} :
    ∀ {ws : List Write}, lastWhere q ws = none → ∀ x ∈ ws, q x = false
  | [], _, _, hx => absurd hx List.not_mem_nil
  | w :: ws, h, x, hx => by
    -- The tail found nothing, and the head did not satisfy `q` either.
    simp only [lastWhere] at h
    cases ht : lastWhere q ws with
    | some y => rw [ht] at h; cases h
    | none =>
      rw [ht] at h
      simp only at h
      rcases List.mem_cons.mp hx with rfl | hm
      · cases hq : q x with
        | false => rfl
        | true => rw [hq] at h; cases h
      · exact lastWhere_none ht x hm

/-- When the walk finds `w`, the list is some writes, then `w`, then newer
writes none of which satisfies `q`. -/
theorem lastWhere_some {q : Write → Bool} :
    ∀ {ws : List Write} {w : Write}, lastWhere q ws = some w →
      q w = true ∧ ∃ pre post, ws = pre ++ w :: post ∧ ∀ x ∈ post, q x = false
  | [], _, h => by cases h
  | v :: ws, w, h => by
    simp only [lastWhere] at h
    cases ht : lastWhere q ws with
    | some y =>
      -- Found in the tail: put `v` in front of the tail's prefix.
      rw [ht] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hq, pre, post, hws, hpost⟩ := lastWhere_some ht
      exact ⟨hq, v :: pre, post, by rw [hws]; rfl, hpost⟩
    | none =>
      -- Not in the tail: it is `v` itself, and nothing after it qualifies.
      rw [ht] at h
      simp only at h
      cases hq : q v with
      | false => rw [hq] at h; cases h
      | true =>
        simp [hq] at h
        subst h
        exact ⟨hq, [], ws, rfl, lastWhere_none ht⟩

/-- When the newest write affecting `k` is `w`, the value of `k` after all
the writes is what `w` left, from some state before it. -/
theorem value_at_last (E : Env) {k : Nat} {ws : List Write} {w : Write}
    -- The newest write affecting `k` is `w`.
    (h : lastWhere (affects E k) ws = some w) (σ : State) :
    ∃ σ', applyWrites E σ ws k = applyWrite E σ' w k := by
  obtain ⟨-, pre, post, rfl, hpost⟩ := lastWhere_some h
  -- The writes before `w` give some state; the writes after it leave `k`.
  refine ⟨applyWrites E σ pre, ?_⟩
  rw [applyWrites_append]
  simp only [applyWrites_cons]
  exact applyWrites_unaffected E k post _ hpost

/-! ## The read classes and their rules -/

/-- A write leaves exactly `v` under `k`: a put of the nonzero `v`, or, when
`v` is 0, a delete or a covering range delete. -/
def SetsTo (k v : Nat) (w : Write) : Prop :=
  (w = .put k v ∧ v ≠ 0) ∨ (v = 0 ∧ (w = .del k ∨ ∃ lo hi, w = .rangeDel lo hi ∧ lo ≤ k ∧ k < hi))

/-- A write leaves `k` present: a put of a value, or a merge. -/
def Keeps (k : Nat) (w : Write) : Prop :=
  (∃ v, w = .put k v ∧ v ≠ 0) ∨ (∃ o, w = .merge k o)

/-- A write that leaves exactly `v` does so from any state. -/
theorem setsTo_value (E : Env) {k v : Nat} {w : Write} (h : SetsTo k v w) (σ : State) :
    applyWrite E σ w k = v := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, rfl | ⟨lo, hi, rfl, hlo, hhi⟩⟩
  · simp [applyWrite, upd]
  · simp [applyWrite, upd]
  · simp [applyWrite, hlo, hhi]

/-- A write that keeps `k` present leaves a value there. -/
theorem keeps_present (E : Env) {k : Nat} {w : Write} (h : Keeps k w) (σ : State) :
    applyWrite E σ w k ≠ 0 := by
  rcases h with ⟨v, rfl, hv⟩ | ⟨o, rfl⟩
  · simpa [applyWrite, upd] using hv
  · simpa [applyWrite, upd] using E.apply_ne_zero (σ k) o

/-- An operand on `k` that `touches` says touches none of the parts `P`. -/
def nonTouching (E : Env) (k : Nat) (P : List Nat) : Write → Bool
  | .merge j o => decide (j = k) && !(E.parts.touches o P)
  | _ => false

/-- A write that changes one of the parts `P` of `k`, as a projected read
sees it (plan 3.4): anything that affects `k` except an operand that touches
none of `P`. -/
def decisive (E : Env) (k : Nat) (P : List Nat) (w : Write) : Bool :=
  affects E k w && !(nonTouching E k P w)

/-- A read the commit validates, by class. -/
inductive Read where
  /-- Key `k`, validated by sequence (every level but DefraLevel). -/
  | full (k : Nat)
  /-- Key `k`, validated by value (DefraLevel, plan 3.5). -/
  | value (k : Nat)
  /-- Content-addressed key `k`, found: validated for presence (E17). -/
  | presence (k : Nat)
  /-- `get_parts(k, P)` that found the key (plan 3.4). -/
  | parts (k : Nat) (P : List Nat)
  /-- `scan_validated` over keys `lo ≤ j < hi` (plan 3.15). -/
  | scan (lo hi : Nat)
  /-- Never validated: a Log read, a commutative stretch, `get_parts(k, [])`. -/
  | exempt

/-- The commit's check for read `r`, given the snapshot `σ` it was served at
and the writes `ws` committed since, oldest first. -/
def Ok (E : Env) : Read → State → List Write → Prop
  | .full k, _, ws => lastWhere (affects E k) ws = none
  | .value k, σ, ws =>
    match lastWhere (affects E k) ws with
    | none => True
    | some w => SetsTo k (σ k) w
  | .presence k, σ, ws =>
    σ k ≠ 0 ∧
      match lastWhere (affects E k) ws with
      | none => True
      | some w => Keeps k w
  | .parts k P, σ, ws =>
    σ k ≠ 0 ∧
      match lastWhere (decisive E k P) ws with
      | none => True
      | some w => SetsTo k (σ k) w
  | .scan lo hi, _, ws => ∀ w ∈ ws, ∀ j, lo ≤ j → j < hi → affects E j w = false
  | .exempt, _, _ => True

/-- What a passed check guarantees about read `r` between state `σ` (the
snapshot) and state `τ` (the commit point): what a decision on it may use. -/
def Agree (E : Env) : Read → State → State → Prop
  | .full k, σ, τ => σ k = τ k
  | .value k, σ, τ => σ k = τ k
  | .presence k, σ, τ => (σ k = 0 ↔ τ k = 0)
  | .parts k P, σ, τ =>
    (σ k = 0 ↔ τ k = 0) ∧ ∀ p ∈ P, E.parts.proj (σ k) p = E.parts.proj (τ k) p
  | .scan lo hi, σ, τ => ∀ j, lo ≤ j → j < hi → σ j = τ j
  | .exempt, _, _ => True

/-! ## Each rule is sound -/

/-- **Ordinary keys, by sequence.** No newer write of `k`: its value at commit
is the value read. -/
theorem full_current (E : Env) {k : Nat} {σ : State} {ws : List Write}
    -- The commit's check for the read passed.
    (h : Ok E (.full k) σ ws) : Agree E (.full k) σ (applyWrites E σ ws) := by
  simp only [Ok] at h
  simp only [Agree]
  exact (applyWrites_unaffected E k ws σ (lastWhere_none h)).symm

/-- **Ordinary keys at DefraLevel, by value.** The newest newer write leaves
exactly the value read: its value at commit is the value read, however many
writes came between (an identical rewrite, or a value that came back). -/
theorem value_current (E : Env) {k : Nat} {σ : State} {ws : List Write}
    -- The commit's check for the read passed.
    (h : Ok E (.value k) σ ws) : Agree E (.value k) σ (applyWrites E σ ws) := by
  simp only [Ok] at h
  simp only [Agree]
  cases hl : lastWhere (affects E k) ws with
  | none =>
    -- No newer write of `k`.
    exact (applyWrites_unaffected E k ws σ (lastWhere_none hl)).symm
  | some w =>
    -- The newest leaves exactly the value read.
    rw [hl] at h
    obtain ⟨σ', h'⟩ := value_at_last E hl σ
    rw [h', setsTo_value E h σ']

/-- **Content-addressed keys, found (E17).** The newest newer write is not a
removal: the key is still present at commit. -/
theorem presence_current (E : Env) {k : Nat} {σ : State} {ws : List Write}
    -- The commit's check for the read passed.
    (h : Ok E (.presence k) σ ws) : Agree E (.presence k) σ (applyWrites E σ ws) := by
  simp only [Ok] at h
  obtain ⟨hσ, h⟩ := h
  simp only [Agree]
  -- Both sides are false: present at the snapshot, present at commit.
  have hρ : applyWrites E σ ws k ≠ 0 := by
    cases hl : lastWhere (affects E k) ws with
    | none => rw [applyWrites_unaffected E k ws σ (lastWhere_none hl)]; exact hσ
    | some w =>
      rw [hl] at h
      obtain ⟨σ', h'⟩ := value_at_last E hl σ
      rw [h']
      exact keeps_present E h σ'
  exact ⟨fun h0 => absurd h0 hσ, fun h0 => absurd h0 hρ⟩

/-- Writes that change no part `P` of `k`, from a state where `k` is
present, leave it present with the same parts. -/
theorem untouched_run (E : Env) {k : Nat} {P : List Nat} :
    ∀ (ws : List Write) (σ : State), (∀ w ∈ ws, decisive E k P w = false) → σ k ≠ 0 →
      applyWrites E σ ws k ≠ 0 ∧
        ∀ p ∈ P, E.parts.proj (applyWrites E σ ws k) p = E.parts.proj (σ k) p
  | [], σ, _, hσ => ⟨hσ, fun _ _ => rfl⟩
  | w :: ws, σ, h, hσ => by
    simp only [applyWrites_cons] at *
    -- The first write keeps `k` present with the same parts.
    have hw : applyWrite E σ w k ≠ 0 ∧
        ∀ p ∈ P, E.parts.proj (applyWrite E σ w k) p = E.parts.proj (σ k) p := by
      have hd := h w List.mem_cons_self
      cases ha : affects E k w with
      | false =>
        -- It does not affect `k` at all.
        rw [applyWrite_unaffected E σ w k ha]
        exact ⟨hσ, fun _ _ => rfl⟩
      | true =>
        -- It affects `k` but is not decisive: an operand on `k` touching none
        -- of `P`, which leaves `k` present (a merge never deletes) and its
        -- parts as they were (the touches contract).
        simp only [decisive, ha, Bool.true_and, Bool.not_eq_false'] at hd
        cases w with
        | merge j o =>
          simp only [nonTouching, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hd
          obtain ⟨rfl, ht⟩ := hd
          simp only [applyWrite, upd]
          exact ⟨E.apply_ne_zero _ _, fun p hp => E.touches_sound (σ j) o P ht p hp⟩
        | put _ _ => simp [nonTouching] at hd
        | del _ => simp [nonTouching] at hd
        | rangeDel _ _ => simp [nonTouching] at hd
        | append _ => simp [nonTouching] at hd
    -- Then the rest do too, from there.
    obtain ⟨h1, h2⟩ := untouched_run E ws (applyWrite E σ w)
      (fun w' hw' => h w' (List.mem_cons_of_mem _ hw')) hw.1
    exact ⟨h1, fun p hp => (h2 p hp).trans (hw.2 p hp)⟩

/-- **Projected reads (plan 3.4).** The first newer write, newest first, that
changes a named part is a put of exactly the value read, or there is none:
the key is present at commit with the same named parts. -/
theorem parts_current (E : Env) {k : Nat} {P : List Nat} {σ : State} {ws : List Write}
    -- The commit's check for the read passed.
    (h : Ok E (.parts k P) σ ws) : Agree E (.parts k P) σ (applyWrites E σ ws) := by
  simp only [Ok] at h
  obtain ⟨hσ, h⟩ := h
  simp only [Agree]
  -- Present at commit with the parts read, in either case below.
  have key : applyWrites E σ ws k ≠ 0 ∧
      ∀ p ∈ P, E.parts.proj (applyWrites E σ ws k) p = E.parts.proj (σ k) p := by
    cases hl : lastWhere (decisive E k P) ws with
    | none =>
      -- No newer write changes a named part.
      exact untouched_run E ws σ (lastWhere_none hl) hσ
    | some w =>
      -- The newest decisive write is a put of the value read; the writes
      -- after it change no named part.
      rw [hl] at h
      obtain ⟨-, pre, post, rfl, hpost⟩ := lastWhere_some hl
      have hw : applyWrite E (applyWrites E σ pre) w k = σ k := setsTo_value E h _
      rw [applyWrites_append]
      simp only [applyWrites_cons]
      have := untouched_run E post (applyWrite E (applyWrites E σ pre) w) hpost (by rw [hw]; exact hσ)
      rw [hw] at this
      exact this
  exact ⟨⟨fun h0 => absurd h0 hσ, fun h0 => absurd h0 key.1⟩, fun p hp => (key.2 p hp).symm⟩

/-- **Validated scans (plan 3.15).** No newer write inside the range: every
key of it holds at commit what the scan saw, so no key left and none
appeared. -/
theorem scan_current (E : Env) {lo hi : Nat} {σ : State} {ws : List Write}
    -- The commit's check for the read passed.
    (h : Ok E (.scan lo hi) σ ws) : Agree E (.scan lo hi) σ (applyWrites E σ ws) := by
  simp only [Ok] at h
  simp only [Agree]
  intro j hlo hhi
  exact (applyWrites_unaffected E j ws σ (fun w hw => h w hw j hlo hhi)).symm

/-- Every rule is sound: a passed check guarantees its agreement. -/
theorem ok_current (E : Env) {r : Read} {σ : State} {ws : List Write}
    -- The commit's check for the read passed.
    (h : Ok E r σ ws) : Agree E r σ (applyWrites E σ ws) := by
  cases r with
  | full k => exact full_current E h
  | value k => exact value_current E h
  | presence k => exact presence_current E h
  | parts k P => exact parts_current E h
  | scan lo hi => exact scan_current E h
  | exempt => trivial

/-! ## Transactions, the history, and the serial run -/

/-- A committed transaction. -/
structure Txn where
  /-- How many commits landed between its snapshot and its own commit. -/
  missed : Nat
  /-- Its validated reads, by class. -/
  reads : List Read
  /-- The content-addressed keys it may create, whose reads are dropped (D7). -/
  creates : List Nat
  /-- Its writes other than creates, from the state it read. -/
  body : State → List Write
  /-- Which of `creates` it puts, from the state it read. -/
  made : State → List Nat

/-- Everything a transaction writes, from the state it read: its body, then
a put of each created key's bytes. -/
def txnWrites (E : Env) (T : Txn) (σ : State) : List Write :=
  T.body σ ++ (T.made σ).map (fun k => Write.put k (E.bytes k))

/-- The commit passed: every validated read passed its rule, and every
create key it read and did not put was found and passed the presence rule
(a key the transaction puts has its read dropped). -/
def Passed (E : Env) (T : Txn) (σ : State) (ws : List Write) : Prop :=
  (∀ r ∈ T.reads, Ok E r σ ws) ∧ (∀ k ∈ T.creates, k ∉ T.made σ → Ok E (.presence k) σ ws)

/-- A write keeps the content-addressed contract: on a content-addressed key
it can only remove (creates put the bytes). -/
def CASafe (E : Env) (w : Write) : Prop :=
  ∀ k, E.isCA k = true → affects E k w = true → w = .del k ∨ ∃ lo hi, w = .rangeDel lo hi

/-- Every content-addressed key is absent or holds its bytes. -/
def CAConsistent (E : Env) (σ : State) : Prop :=
  ∀ k, E.isCA k = true → σ k = 0 ∨ σ k = E.bytes k

/-- The caller's side: a decision depends only on what its validated reads
guarantee, and content-addressed creates follow the class's contract. -/
structure Contract (E : Env) (T : Txn) : Prop where
  /-- The body is the same from any two states its reads agree on. -/
  body_agree : ∀ σ τ, (∀ r ∈ T.reads, Agree E r σ τ) → T.body σ = T.body τ
  /-- It only puts keys it declared as creates. -/
  made_sub : ∀ σ, ∀ k ∈ T.made σ, k ∈ T.creates
  /-- It puts every create key it reads as absent. -/
  made_absent : ∀ σ, ∀ k ∈ T.creates, σ k = 0 → k ∈ T.made σ
  /-- Create keys are content-addressed. -/
  creates_ca : ∀ k ∈ T.creates, E.isCA k = true
  /-- The body leaves create keys alone. -/
  body_avoids : ∀ σ, ∀ w ∈ T.body σ, ∀ k ∈ T.creates, affects E k w = false
  /-- The body only removes content-addressed keys. -/
  body_safe : ∀ σ, ∀ w ∈ T.body σ, CASafe E w

/-- The state after a history, newest commit first. Each transaction decided
on the state after the commits it saw (the history without its `missed`
newest ones) and its writes apply at its commit. -/
def run (E : Env) : List Txn → State
  | [] => E.init
  | T :: h => applyWrites E (run E h) (txnWrites E T (run E (h.drop T.missed)))
termination_by h => h.length
decreasing_by
  all_goals simp only [List.length_cons, List.length_drop]
  all_goals omega

/-- The writes committed after the first `m` newest commits were cut off,
oldest first: what a transaction that missed `m` commits did not see. -/
def newer (E : Env) : List Txn → Nat → List Write
  | _, 0 => []
  | [], _ + 1 => []
  | T :: h, m + 1 => newer E h m ++ txnWrites E T (run E (h.drop T.missed))

/-- The same transactions one at a time in commit order, each reading the
state just before its commit. -/
def serial (E : Env) : List Txn → State
  | [] => E.init
  | T :: h => applyWrites E (serial E h) (txnWrites E T (serial E h))

/-- A history in which every commit passed: each transaction missed no more
commits than there were, kept the contract, and passed its checks against
the writes it missed. -/
def Valid (E : Env) : List Txn → Prop
  | [] => True
  | T :: h =>
    Valid E h ∧ T.missed ≤ h.length ∧ Contract E T ∧
      Passed E T (run E (h.drop T.missed)) (newer E h T.missed)

/-- The state after `T :: h`. -/
theorem run_cons (E : Env) (T : Txn) (h : List Txn) :
    run E (T :: h) = applyWrites E (run E h) (txnWrites E T (run E (h.drop T.missed))) := by
  rw [run]

/-- The state after a history is the state at a transaction's snapshot with
the writes it missed applied on top. -/
theorem run_split (E : Env) :
    ∀ (h : List Txn) (m : Nat), m ≤ h.length → run E h = applyWrites E (run E (h.drop m)) (newer E h m)
  | h, 0, _ => by simp [newer, applyWrites]
  | [], _ + 1, hm => by simp at hm
  | T :: h, m + 1, hm => by
    -- Cut one fewer commit off the tail, then apply the newest commit.
    simp only [List.length_cons] at hm
    rw [run_cons, run_split E h m (by omega)]
    simp only [List.drop_succ_cons, newer, applyWrites_append]

/-! ## From commit points to a serial history -/

/-- **The lift.** If every commit of a history, from any state satisfying an
invariant `I`, has the effect its decision at the commit point would have,
and keeps `I`, then the history equals the serial run and keeps `I`. `Q` is
the class restriction a per-class theorem imposes. -/
theorem lift (E : Env) (Q : Txn → Prop) (I : State → Prop)
    -- The invariant holds at the start.
    (hinit : I E.init)
    -- Every commit of a transaction in the class has its commit-point effect
    -- and keeps the invariant.
    (hstep : ∀ T h, Q T → Valid E (T :: h) → I (run E h) →
      applyWrites E (run E h) (txnWrites E T (run E (h.drop T.missed))) =
          applyWrites E (run E h) (txnWrites E T (run E h)) ∧
        I (applyWrites E (run E h) (txnWrites E T (run E (h.drop T.missed))))) :
    ∀ h : List Txn, (∀ T ∈ h, Q T) → Valid E h → run E h = serial E h ∧ I (run E h)
  | [], _, _ => ⟨by rw [run, serial], by rw [run]; exact hinit⟩
  | T :: h, hQ, hv => by
    -- The older commits are serial (the claim for the shorter history); the
    -- newest one has its commit-point effect, which is the serial step.
    have hv' := hv
    simp only [Valid] at hv'
    obtain ⟨heq, hI⟩ := lift E Q I hinit hstep h
      (fun T' hT' => hQ T' (List.mem_cons_of_mem _ hT')) hv'.1
    obtain ⟨hcp, hI'⟩ := hstep T h (hQ T List.mem_cons_self) hv hI
    refine ⟨?_, ?_⟩
    · rw [run_cons, hcp, heq]; simp only [serial]
    · rw [run_cons]; exact hI'

/-- From a valid commit: the state at its snapshot, the writes it missed,
its contract and its passed checks, with the commit state as the snapshot
plus those writes. -/
theorem valid_head (E : Env) {T : Txn} {h : List Txn} (hv : Valid E (T :: h)) :
    Contract E T ∧ Passed E T (run E (h.drop T.missed)) (newer E h T.missed) ∧
      run E h = applyWrites E (run E (h.drop T.missed)) (newer E h T.missed) := by
  simp only [Valid] at hv
  obtain ⟨-, hm, hc, hp⟩ := hv
  exact ⟨hc, hp, run_split E h T.missed hm⟩

/-- A transaction that creates nothing writes exactly its body. -/
theorem txnWrites_no_creates (E : Env) {T : Txn} (hc : Contract E T) (hcr : T.creates = [])
    (σ : State) : txnWrites E T σ = T.body σ := by
  have : T.made σ = [] := by
    -- Everything it puts is a create, and it declared none.
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro k hk
    have := hc.made_sub σ k hk
    rw [hcr] at this
    exact List.not_mem_nil this
  simp [txnWrites, this]

/-- The commit-point step for a transaction that creates nothing and whose
reads are all of a class whose rule is sound. -/
theorem step_of_class (E : Env) (C : Read → Prop)
    -- The class's rule guarantees its agreement.
    (hsound : ∀ r σ ws, C r → Ok E r σ ws → Agree E r σ (applyWrites E σ ws))
    (T : Txn) (h : List Txn)
    -- Every read of the transaction is of the class, and it creates nothing.
    (hC : ∀ r ∈ T.reads, C r) (hcr : T.creates = [])
    -- The commit is valid.
    (hv : Valid E (T :: h)) :
    applyWrites E (run E h) (txnWrites E T (run E (h.drop T.missed))) =
      applyWrites E (run E h) (txnWrites E T (run E h)) := by
  obtain ⟨hc, hp, hsplit⟩ := valid_head E hv
  -- Every read agrees between the snapshot and the commit point, so the body
  -- is the same from both.
  have hag : ∀ r ∈ T.reads, Agree E r (run E (h.drop T.missed)) (run E h) := by
    intro r hr
    rw [hsplit]
    exact hsound r _ _ (hC r hr) (hp.1 r hr)
  rw [txnWrites_no_creates E hc hcr, txnWrites_no_creates E hc hcr, hc.body_agree _ _ hag]

/-! ## One theorem per class -/

/-- **Ordinary keys, every level.** A history whose transactions read only
keys validated by sequence, and passed, is serial in commit order. -/
theorem ordinary_serial (E : Env) (h : List Txn)
    -- Every transaction's reads are of this class, and it creates nothing.
    (hcls : ∀ T ∈ h, (∀ r ∈ T.reads, ∃ k, r = .full k) ∧ T.creates = [])
    -- Every commit of the history passed its checks.
    (hv : Valid E h) : run E h = serial E h :=
  (lift E (fun T => (∀ r ∈ T.reads, ∃ k, r = .full k) ∧ T.creates = []) (fun _ => True)
    trivial
    (fun T h hQ hv _ => ⟨step_of_class E (fun r => ∃ k, r = .full k)
      (fun r _ _ hr hok => by obtain ⟨k, rfl⟩ := hr; exact full_current E hok)
      T h hQ.1 hQ.2 hv, trivial⟩)
    h hcls hv).1

/-- **Ordinary keys at DefraLevel, by value.** A history whose transactions'
reads are value-validated, and passed, is serial in commit order, although a
read survives any newer writes that leave the value it read. -/
theorem value_serial (E : Env) (h : List Txn)
    -- Every transaction's reads are of this class, and it creates nothing.
    (hcls : ∀ T ∈ h, (∀ r ∈ T.reads, ∃ k, r = .value k) ∧ T.creates = [])
    -- Every commit of the history passed its checks.
    (hv : Valid E h) : run E h = serial E h :=
  (lift E (fun T => (∀ r ∈ T.reads, ∃ k, r = .value k) ∧ T.creates = []) (fun _ => True)
    trivial
    (fun T h hQ hv _ => ⟨step_of_class E (fun r => ∃ k, r = .value k)
      (fun r _ _ hr hok => by obtain ⟨k, rfl⟩ := hr; exact value_current E hok)
      T h hQ.1 hQ.2 hv, trivial⟩)
    h hcls hv).1

/-- **Projected reads.** A history whose transactions' reads are projected,
and passed, is serial in commit order: each decision uses only existence and
the parts it named, and those are current at its commit. -/
theorem parts_serial (E : Env) (h : List Txn)
    -- Every transaction's reads are of this class, and it creates nothing.
    (hcls : ∀ T ∈ h, (∀ r ∈ T.reads, ∃ k P, r = .parts k P) ∧ T.creates = [])
    -- Every commit of the history passed its checks.
    (hv : Valid E h) : run E h = serial E h :=
  (lift E (fun T => (∀ r ∈ T.reads, ∃ k P, r = .parts k P) ∧ T.creates = []) (fun _ => True)
    trivial
    (fun T h hQ hv _ => ⟨step_of_class E (fun r => ∃ k P, r = .parts k P)
      (fun r _ _ hr hok => by obtain ⟨k, P, rfl⟩ := hr; exact parts_current E hok)
      T h hQ.1 hQ.2 hv, trivial⟩)
    h hcls hv).1

/-- **Validated scans.** A history whose transactions' reads are validated
scans, and passed, is serial in commit order: no revocation and no phantom
lands under a decision on a range. -/
theorem scan_serial (E : Env) (h : List Txn)
    -- Every transaction's reads are of this class, and it creates nothing.
    (hcls : ∀ T ∈ h, (∀ r ∈ T.reads, ∃ lo hi, r = .scan lo hi) ∧ T.creates = [])
    -- Every commit of the history passed its checks.
    (hv : Valid E h) : run E h = serial E h :=
  (lift E (fun T => (∀ r ∈ T.reads, ∃ lo hi, r = .scan lo hi) ∧ T.creates = []) (fun _ => True)
    trivial
    (fun T h hQ hv _ => ⟨step_of_class E (fun r => ∃ lo hi, r = .scan lo hi)
      (fun r _ _ hr hok => by obtain ⟨lo, hi, rfl⟩ := hr; exact scan_current E hok)
      T h hQ.1 hQ.2 hv, trivial⟩)
    h hcls hv).1

/-- **Exempt reads: Log reads, commutative stretches, `get_parts` with no
part.** Nothing is validated, and the history is serial in commit order
exactly when no decision depends on them: the contract's `body_agree` with
an agreement that says nothing forces the body to ignore them. That is the
relaxation these classes declare; `exempt_decision_breaks_serial` is what
happens when a caller decides on one. Appends in the body are applied at
commit, in commit order. -/
theorem exempt_serial (E : Env) (h : List Txn)
    -- Every transaction's reads are of this class, and it creates nothing.
    (hcls : ∀ T ∈ h, (∀ r ∈ T.reads, r = .exempt) ∧ T.creates = [])
    -- Every commit of the history passed its checks.
    (hv : Valid E h) : run E h = serial E h :=
  (lift E (fun T => (∀ r ∈ T.reads, r = .exempt) ∧ T.creates = []) (fun _ => True)
    trivial
    (fun T h hQ hv _ => ⟨step_of_class E (fun r => r = .exempt)
      (fun r _ _ hr _ => by subst hr; trivial)
      T h hQ.1 hQ.2 hv, trivial⟩)
    h hcls hv).1

/-- **Blind merges.** A history of transactions that read nothing (the
blind-merge path: each merge applies at commit on top of whatever landed) is
serial in commit order. Two concurrent blind merges both commit; that is
the relaxation of snapshot isolation, and `blindMerge_commutes` states when
the merge may also be placed at its snapshot. -/
theorem blindMerge_serial (E : Env) (h : List Txn)
    -- No transaction reads anything or creates anything.
    (hcls : ∀ T ∈ h, T.reads = [] ∧ T.creates = [])
    -- Every commit of the history passed its checks.
    (hv : Valid E h) : run E h = serial E h :=
  (lift E (fun T => T.reads = [] ∧ T.creates = []) (fun _ => True)
    trivial
    (fun T h hQ hv _ => ⟨step_of_class E (fun _ => False)
      (fun _ _ _ hr _ => hr.elim)
      T h (by rw [hQ.1]; intro r hr; exact absurd hr List.not_mem_nil) hQ.2 hv, trivial⟩)
    h hcls hv).1

/-! ## Content-addressed keys: creates are idempotent -/

/-- **`ca_put_idempotent`.** Putting a content-addressed key's bytes where the
key already holds them changes nothing. -/
theorem ca_put_idempotent (E : Env) (σ : State) (k : Nat) (h : σ k = E.bytes k) :
    applyWrite E σ (.put k (E.bytes k)) = σ := by
  funext j
  simp only [applyWrite, upd]
  split
  · subst_vars; exact h.symm
  · rfl

/-- Puts of the bytes of keys `M`: key `j` ends with its bytes if it is in
`M`, as it was otherwise. -/
theorem puts_at (E : Env) :
    ∀ (M : List Nat) (σ : State) (j : Nat),
      applyWrites E σ (M.map (fun k => Write.put k (E.bytes k))) j =
        if j ∈ M then E.bytes j else σ j
  | [], σ, j => by simp [applyWrites_nil]
  | k :: M, σ, j => by
    simp only [List.map_cons, applyWrites_cons] at *
    rw [puts_at E M]
    by_cases hj : j ∈ M
    · simp [hj]
    · by_cases hk : j = k
      · subst hk; simp [applyWrite, upd]
      · simp [hj, hk, applyWrite, upd]

/-- A write that keeps the content-addressed contract and affects a
content-addressed key removes it. -/
theorem caSafe_removes (E : Env) {w : Write} (hw : CASafe E w) {k : Nat}
    (hk : E.isCA k = true) (ha : affects E k w = true) (σ : State) :
    applyWrite E σ w k = 0 := by
  rcases hw k hk ha with rfl | ⟨lo, hi, rfl⟩
  · simp [applyWrite, upd]
  · simp only [affects, decide_eq_true_eq] at ha
    simp [applyWrite, ha.1, ha.2]

/-- Writes that keep the content-addressed contract keep every
content-addressed key absent or at its bytes. -/
theorem caSafe_consistent (E : Env) :
    ∀ (ws : List Write) (σ : State), CAConsistent E σ → (∀ w ∈ ws, CASafe E w) →
      CAConsistent E (applyWrites E σ ws)
  | [], σ, hσ, _ => hσ
  | w :: ws, σ, hσ, hws => by
    simp only [applyWrites_cons]
    apply caSafe_consistent E ws _ _ (fun w' hw' => hws w' (List.mem_cons_of_mem _ hw'))
    -- The first write removes a content-addressed key or leaves it.
    intro k hk
    cases ha : affects E k w with
    | false => rw [applyWrite_unaffected E σ w k ha]; exact hσ k hk
    | true => exact Or.inl (caSafe_removes E (hws w List.mem_cons_self) hk ha σ)

/-- A transaction's writes keep every content-addressed key absent or at its
bytes. -/
theorem txn_consistent (E : Env) {T : Txn} (hc : Contract E T) {ρ : State}
    (hρ : CAConsistent E ρ) (σ : State) :
    CAConsistent E (applyWrites E ρ (txnWrites E T σ)) := by
  simp only [txnWrites, applyWrites_append]
  have hb := caSafe_consistent E (T.body σ) ρ hρ (hc.body_safe σ)
  intro k hk
  rw [puts_at]
  -- A created key gets its bytes; any other is as the body left it.
  split
  · exact Or.inr rfl
  · exact hb k hk

/-- **The content-addressed commit point.** A transaction that passed its
checks, from a commit state where every content-addressed key is absent or
at its bytes, has the effect its decision at the commit point would have,
although its reads of the keys it creates were dropped: a create it made at
its snapshot puts bytes the key holds at commit or that the commit-point
decision would put too. -/
theorem ca_commit_point (E : Env) {T : Txn} (hc : Contract E T) {σs : State}
    {ws : List Write} (hp : Passed E T σs ws)
    (hca : CAConsistent E (applyWrites E σs ws)) :
    applyWrites E (applyWrites E σs ws) (txnWrites E T σs) =
      applyWrites E (applyWrites E σs ws) (txnWrites E T (applyWrites E σs ws)) := by
  -- Write ρ for the commit state.
  generalize hρdef : applyWrites E σs ws = ρ at hca ⊢
  -- The validated reads agree, so the body is the same from both states.
  have hag : ∀ r ∈ T.reads, Agree E r σs ρ := by
    intro r hr; rw [← hρdef]; exact ok_current E (hp.1 r hr)
  simp only [txnWrites, applyWrites_append, hc.body_agree _ _ hag]
  -- Key by key, the creates agree.
  funext j
  rw [puts_at, puts_at]
  by_cases hj : j ∈ T.creates
  · -- A create key: the body leaves it, and both sides end with its bytes.
    have hbody : applyWrites E ρ (T.body ρ) j = ρ j :=
      applyWrites_unaffected E j _ ρ (fun w hw => hc.body_avoids ρ w hw j hj)
    have hbytes : ρ j ≠ 0 → ρ j = E.bytes j := by
      intro h0
      rcases hca j (hc.creates_ca j hj) with h | h
      · exact absurd h h0
      · exact h
    rw [hbody]
    -- The commit-point decision puts it unless it is present, and then it
    -- holds its bytes.
    have rhs : (if j ∈ T.made ρ then E.bytes j else ρ j) = E.bytes j := by
      split
      · rfl
      · rename_i hn
        apply hbytes
        intro h0
        exact hn (hc.made_absent ρ j hj h0)
    -- The snapshot decision puts it, or found it present, and then the
    -- presence check guarantees it is still present at commit.
    have lhs : (if j ∈ T.made σs then E.bytes j else ρ j) = E.bytes j := by
      split
      · rfl
      · rename_i hn
        have hfound : σs j ≠ 0 := fun h0 => hn (hc.made_absent σs j hj h0)
        have hpres := presence_current E (hp.2 j hj hn)
        rw [hρdef] at hpres
        simp only [Agree] at hpres
        exact hbytes (fun h0 => hfound (hpres.mpr h0))
    rw [lhs, rhs]
  · -- Not a create key: neither side puts it.
    have h1 : j ∉ T.made σs := fun hm => hj (hc.made_sub σs j hm)
    have h2 : j ∉ T.made ρ := fun hm => hj (hc.made_sub ρ j hm)
    simp [h1, h2]

/-- **Content-addressed keys (E17, D7).** A history whose transactions read
content-addressed keys for presence (or in full, when they found nothing)
and create them with their bytes, and passed, is serial in commit order,
provided every content-addressed key starts absent or at its bytes. Two
creates of one key both commit; the relaxation that makes it serial is that
a create is idempotent (`ca_put_idempotent`). -/
theorem contentAddressed_serial (E : Env)
    -- Every content-addressed key starts absent or at its bytes.
    (hinit : CAConsistent E E.init) (h : List Txn)
    -- Every read is a presence read, or a full one (a read that found nothing).
    (hcls : ∀ T ∈ h, ∀ r ∈ T.reads, (∃ k, r = .presence k) ∨ (∃ k, r = .value k) ∨
      (∃ k, r = .full k))
    -- Every commit of the history passed its checks.
    (hv : Valid E h) : run E h = serial E h :=
  (lift E (fun T => ∀ r ∈ T.reads, (∃ k, r = .presence k) ∨ (∃ k, r = .value k) ∨
      (∃ k, r = .full k)) (CAConsistent E) hinit
    (fun T h _ hv hI => by
      obtain ⟨hc, hp, hsplit⟩ := valid_head E hv
      refine ⟨?_, txn_consistent E hc hI _⟩
      rw [hsplit] at hI ⊢
      exact ca_commit_point E hc hp hI)
    h hcls hv).1

/-! ## The combined theorem -/

/-- **Every class at once.** A history in which every commit passed its
checks, whatever classes its reads are and whatever it creates, is serial in
commit order, provided every content-addressed key starts absent or at its
bytes. -/
theorem all_classes_serial (E : Env)
    -- Every content-addressed key starts absent or at its bytes.
    (hinit : CAConsistent E E.init) (h : List Txn)
    -- Every commit of the history passed its checks.
    (hv : Valid E h) : run E h = serial E h :=
  (lift E (fun _ => True) (CAConsistent E) hinit
    (fun T h _ hv hI => by
      obtain ⟨hc, hp, hsplit⟩ := valid_head E hv
      refine ⟨?_, txn_consistent E hc hI _⟩
      rw [hsplit] at hI ⊢
      exact ca_commit_point E hc hp hI)
    h (fun _ _ => trivial) hv).1

end Regolith.Validation
