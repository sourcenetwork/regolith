import Regolith.Validation

/-!
# Relaxations: what each key class gives up, stated exactly (plan 3.1 to 3.15)

This file continues `Regolith/Validation.lean` and backs the same TLA+ model,
`proofs/tla/RepeatableRead.tla`. Validation.lean proves that every class's
rule gives a history serial in commit order. Here each class's declared
relaxation is stated exactly, with the RED cases as counterexamples:

* `blindMerge_commutes` (configuration `MC_DefraLevel_Green_Counters`,
  invariant `INV_IncrementsCommitUnlessReplaced`): with commuting operands, a
  blind merge that passed its rule may be serialized at its snapshot as well
  as at its commit; `blindMerge_across_replacement` is why the rule refuses a
  newer replacement (`MC_DefraLevel_Red_MergeIgnoresReplacement`).
* `identical_rewrite` (`MC_DefraLevel_Green_ValueReads`,
  `INV_IdenticalRewritesCommit`): an identical rewrite passes the value rule
  and fails the sequence rule (`MC_DefraLevel_Red_SeqOnlyValidation`).
* `commutative_union` (`MC_DefraLevel_Green_Heads`, `INV_HeadsExact`):
  writers that add their own keys and remove keys they saw leave the same
  state in either commit order.
* `appends_advance_head` and `appends_keep_dense` (`MC_DefraLevel_Green_Log`,
  `INV_LogDense`): each append takes the next position at its commit, so
  positions are dense from 1 and follow commit order.
* `writeFree_at_snapshot` (`MC_DefraLevel_Green_WriteFree`,
  `INV_WriteFreeConsistent`): what a transaction read is the serial state at
  its snapshot, so a write-free one serializes there.
* `exempt_decision_breaks_serial` (`MC_DefraLevel_Red_DecideOnLogRead`,
  `MC_DefraLevel_Red_PartsNamesOther`) and `promoted_read_skew`
  (`MC_DefraLevel_Red_WriteFreePessimistic`): the RED cases.

How to read the Lean: as in Validation.lean; every proof step is commented.
-/

namespace Regolith.Validation

/-! ## The relaxations, stated exactly -/

/-- The blind-merge rule: every newer write of `k` is an operand, so no
replacement landed since the snapshot (`newest_terminator_seq_above`). -/
def BlindMergeOk (E : Env) (k : Nat) (ws : List Write) : Prop :=
  ∀ w ∈ ws, affects E k w = true → ∃ o, w = .merge k o

/-- A merge into `k` leaves on `k` the operand applied to what `k` held. -/
theorem merge_at (E : Env) (σ : State) (k o : Nat) :
    applyWrite E σ (.merge k o) k = E.op.apply (σ k) o := by
  simp [applyWrite, upd]

/-- When every write affecting `k` is an operand on `k`, the value of `k`
after the writes depends only on the value of `k` before them. -/
theorem merges_at (E : Env) {k : Nat} :
    ∀ (ws : List Write) (σ τ : State), BlindMergeOk E k ws → σ k = τ k →
      applyWrites E σ ws k = applyWrites E τ ws k
  | [], _, _, _, h => h
  | w :: ws, σ, τ, hok, h => by
    simp only [applyWrites_cons]
    apply merges_at E ws _ _ (fun w' hw' => hok w' (List.mem_cons_of_mem _ hw'))
    -- The first write leaves `k` on both sides, or folds the same operand
    -- onto the same value.
    cases ha : affects E k w with
    | false => rw [applyWrite_unaffected E σ w k ha, applyWrite_unaffected E τ w k ha, h]
    | true =>
      obtain ⟨o, rfl⟩ := hok w List.mem_cons_self ha
      rw [merge_at, merge_at, h]

/-- **Blind merges commute.** With operands that commute, a blind merge that
passed its rule leaves `k` the same whether it is placed at its commit
(after the operands it missed) or at its snapshot (before them). -/
theorem blindMerge_commutes (E : Env)
    -- The operator's operands commute.
    (hcomm : ∀ v a b, E.op.apply (E.op.apply v a) b = E.op.apply (E.op.apply v b) a)
    (k o : Nat) :
    ∀ (ws : List Write) (σ : State), BlindMergeOk E k ws →
      applyWrite E (applyWrites E σ ws) (.merge k o) k =
        applyWrites E (applyWrite E σ (.merge k o)) ws k
  | [], σ, _ => rfl
  | w :: ws, σ, hok => by
    have hok' : BlindMergeOk E k ws := fun w' hw' => hok w' (List.mem_cons_of_mem _ hw')
    -- Place the merge before the rest of the missed writes (the claim for
    -- the shorter list).
    have ih := blindMerge_commutes E hcomm k o ws (applyWrite E σ w) hok'
    simp only [applyWrites_cons] at ih ⊢
    rw [ih]
    -- Then swap it with the first missed write. Only `k` matters to the rest
    -- (`merges_at`), and on `k` the first write either does nothing or is an
    -- operand, which commutes with ours.
    apply merges_at E ws _ _ hok'
    cases ha : affects E k w with
    | false =>
      rw [merge_at, applyWrite_unaffected E σ w k ha,
        applyWrite_unaffected E _ w k ha, merge_at]
    | true =>
      obtain ⟨o', rfl⟩ := hok w List.mem_cons_self ha
      rw [merge_at, merge_at, merge_at, merge_at]
      exact hcomm _ _ _

/-- **An identical rewrite is not a change (plan 3.5).** A read that found
`v`, with a newer put of the same `v`, passes the value rule and fails the
sequence rule. -/
theorem identical_rewrite (E : Env) (σ : State) (k : Nat) (hv : σ k ≠ 0) :
    Ok E (.value k) σ [.put k (σ k)] ∧ ¬ Ok E (.full k) σ [.put k (σ k)] := by
  refine ⟨?_, ?_⟩
  · -- The newest write of `k` is the put itself, of the value read.
    simp [Ok, lastWhere, affects, SetsTo, hv]
  · -- By sequence, any newer write of `k` fails.
    simp [Ok, lastWhere, affects]

/-- Puts and deletes of disjoint keys commute: applying two writers' lists in
either order leaves the same state. -/
def PutDel (w : Write) : Prop := (∃ k v, w = .put k v) ∨ ∃ k, w = .del k

/-- A put or a delete leaves the same value on its key from any state. -/
theorem putDel_const (E : Env) {w : Write}
    -- `w` is a put or a delete, and it affects `k`.
    (hw : PutDel w) {k : Nat}
    (ha : affects E k w = true) (σ τ : State) : applyWrite E σ w k = applyWrite E τ w k := by
  rcases hw with ⟨j, v, rfl⟩ | ⟨j, rfl⟩
  · simp only [affects, decide_eq_true_eq] at ha; subst ha; simp [applyWrite, upd]
  · simp only [affects, decide_eq_true_eq] at ha; subst ha; simp [applyWrite, upd]

/-- After a list of puts and deletes, a key's value depends only on whether
the list affects it: if it does, not on the state the list started from. -/
theorem putDels_at (E : Env) {k : Nat} :
    ∀ (ws : List Write), (∀ w ∈ ws, PutDel w) → (∃ w ∈ ws, affects E k w = true) →
      ∀ σ τ, applyWrites E σ ws k = applyWrites E τ ws k := by
  intro ws hws hex σ τ
  cases hl : lastWhere (affects E k) ws with
  | none =>
    obtain ⟨w, hw, ha⟩ := hex
    rw [lastWhere_none hl w hw] at ha
    cases ha
  | some w =>
    obtain ⟨hq, pre, post, rfl, hpost⟩ := lastWhere_some hl
    rw [applyWrites_append, applyWrites_append]
    simp only [applyWrites_cons]
    rw [applyWrites_unaffected E k post _ hpost, applyWrites_unaffected E k post _ hpost]
    exact putDel_const E (hws w (by simp)) hq _ _

/-- **Concurrent writers in a commutative prefix leave the union.** Two
commits whose writes are puts and deletes of disjoint keys (each writer adds
its own keys and removes keys it observed) leave the same state in either
commit order. -/
theorem commutative_union (E : Env) (a b : List Write)
    -- Both writers only put and delete.
    (ha : ∀ w ∈ a, PutDel w) (hb : ∀ w ∈ b, PutDel w)
    -- No key is affected by both.
    (hdisj : ∀ k, (∃ w ∈ a, affects E k w = true) → ∀ w ∈ b, affects E k w = false)
    (σ : State) :
    applyWrites E (applyWrites E σ a) b = applyWrites E (applyWrites E σ b) a := by
  funext k
  by_cases hka : ∃ w ∈ a, affects E k w = true
  · -- `a` decides `k`, and `b` leaves it.
    rw [applyWrites_unaffected E k b _ (hdisj k hka)]
    exact putDels_at E a ha hka σ _
  · -- `a` leaves `k`; then `b` decides it or leaves it too.
    have hna : ∀ w ∈ a, affects E k w = false := by
      intro w hw
      cases h : affects E k w with
      | false => rfl
      | true => exact absurd ⟨w, hw, h⟩ hka
    rw [applyWrites_unaffected E k a _ hna]
    by_cases hkb : ∃ w ∈ b, affects E k w = true
    · exact putDels_at E b hb hkb _ σ
    · have hnb : ∀ w ∈ b, affects E k w = false := by
        intro w hw
        cases h : affects E k w with
        | false => rfl
        | true => exact absurd ⟨w, hw, h⟩ hkb
      rw [applyWrites_unaffected E k b _ hnb, applyWrites_unaffected E k b _ hnb,
        applyWrites_unaffected E k a _ hna]

/-! ## Log appends are commit-ordered -/

/-- A write keeps the Log contract: on a Log key, only an append of an entry
writes (plan 3.6: a transaction's own put or delete of a Log key is
refused). -/
def LogSafe (E : Env) (w : Write) : Prop :=
  ∀ k, E.isLog k = true → affects E k w = true → ∃ e, w = .append e ∧ e ≠ 0

/-- One for an append, zero for any other write. -/
def isAppend : Write → Nat
  | .append _ => 1
  | .put _ _ => 0
  | .del _ => 0
  | .merge _ _ => 0
  | .rangeDel _ _ => 0

/-- The number of appends in a list of writes. -/
def appends : List Write → Nat
  | [] => 0
  | w :: ws => isAppend w + appends ws

/-- **Appends advance the head one position each, in commit order.** Writes
that keep the Log contract move the head by exactly the number of appends
among them: each append takes the next position when it is applied. -/
theorem appends_advance_head (E : Env) :
    ∀ (ws : List Write) (σ : State), (∀ w ∈ ws, LogSafe E w) →
      applyWrites E σ ws E.head = σ E.head + appends ws
  | [], σ, _ => rfl
  | w :: ws, σ, hws => by
    simp only [applyWrites_cons] at *
    rw [appends_advance_head E ws _ (fun w' hw' => hws w' (List.mem_cons_of_mem _ hw'))]
    cases w with
    | append e =>
      -- The append sets the head to one more.
      simp [applyWrite, upd, appends, isAppend] <;> omega
    | put k v =>
      -- Anything else leaves the head: a write of it would have to be an
      -- append.
      have : affects E E.head (.put k v) = false := by
        cases h : affects E E.head (.put k v) with
        | false => rfl
        | true => obtain ⟨_, he, _⟩ := hws _ List.mem_cons_self E.head E.isLog_head h; cases he
      rw [applyWrite_unaffected E σ _ _ this]; simp [appends, isAppend]
    | del k =>
      have : affects E E.head (.del k) = false := by
        cases h : affects E E.head (.del k) with
        | false => rfl
        | true => obtain ⟨_, he, _⟩ := hws _ List.mem_cons_self E.head E.isLog_head h; cases he
      rw [applyWrite_unaffected E σ _ _ this]; simp [appends, isAppend]
    | merge k o =>
      have : affects E E.head (.merge k o) = false := by
        cases h : affects E E.head (.merge k o) with
        | false => rfl
        | true => obtain ⟨_, he, _⟩ := hws _ List.mem_cons_self E.head E.isLog_head h; cases he
      rw [applyWrite_unaffected E σ _ _ this]; simp [appends, isAppend]
    | rangeDel lo hi =>
      have : affects E E.head (.rangeDel lo hi) = false := by
        cases h : affects E E.head (.rangeDel lo hi) with
        | false => rfl
        | true => obtain ⟨_, he, _⟩ := hws _ List.mem_cons_self E.head E.isLog_head h; cases he
      rw [applyWrite_unaffected E σ _ _ this]; simp [appends, isAppend]

/-- The log is dense: every position from 1 to the head holds an entry. -/
def LogDense (E : Env) (σ : State) : Prop :=
  ∀ p, 1 ≤ p → p ≤ σ E.head → σ (E.entry p) ≠ 0

/-- **Appends keep the log dense.** Writes that keep the Log contract, from a
dense log, leave a dense log: each append fills the position just past the
head and moves the head onto it, so no position is skipped. -/
theorem appends_keep_dense (E : Env) :
    ∀ (ws : List Write) (σ : State), LogDense E σ → (∀ w ∈ ws, LogSafe E w) →
      LogDense E (applyWrites E σ ws)
  | [], σ, hd, _ => hd
  | w :: ws, σ, hd, hws => by
    simp only [applyWrites_cons]
    apply appends_keep_dense E ws _ _ (fun w' hw' => hws w' (List.mem_cons_of_mem _ hw'))
    intro p hp1 hp
    cases ha : affects E E.head w with
    | false =>
      -- The head does not move, and no entry changes: a write of an entry
      -- would be an append, which moves the head.
      rw [applyWrite_unaffected E σ w _ ha] at hp
      have he : affects E (E.entry p) w = false := by
        cases h : affects E (E.entry p) w with
        | false => rfl
        | true =>
          obtain ⟨e, rfl, _⟩ := hws w List.mem_cons_self _ (E.isLog_entry p) h
          simp [affects, E.isLog_head] at ha
      rw [applyWrite_unaffected E σ w _ he]
      exact hd p hp1 hp
    | true =>
      -- An append: the new head is one more, its entry is the new one, and
      -- every earlier position keeps its entry.
      obtain ⟨e, rfl, he0⟩ := hws w List.mem_cons_self _ E.isLog_head ha
      simp [applyWrite, upd] at hp
      have hne : E.entry p ≠ E.head := E.entry_ne_head p
      simp only [applyWrite, upd, hne]
      by_cases hlast : p = σ E.head + 1
      · subst hlast; simp [he0]
      · have hlt : p ≤ σ E.head := by omega
        have hneq : E.entry p ≠ E.entry (σ E.head + 1) := fun h => hlast (E.entry_inj _ _ h)
        simp only [hneq]
        exact hd p hp1 hlt

/-! ## Write-free transactions read one point in time -/

/-- A valid history's suffixes are valid. -/
theorem valid_drop (E : Env) : ∀ (h : List Txn) (m : Nat), Valid E h → Valid E (h.drop m)
  | h, 0, hv => by simpa using hv
  | [], _ + 1, _ => by simp [Valid]
  | _ :: h, m + 1, hv => by
    simp only [Valid] at hv
    simpa using valid_drop E h m hv.1

/-- **Write-free transactions (plan 3.8).** What any transaction read is the
serial state at its snapshot. A transaction with no writes changes nothing,
so it serializes there although it validated nothing. -/
theorem writeFree_at_snapshot (E : Env) (hinit : CAConsistent E E.init) {T : Txn}
    {h : List Txn} (hv : Valid E (T :: h)) :
    run E (h.drop T.missed) = serial E (h.drop T.missed) := by
  simp only [Valid] at hv
  exact all_classes_serial E hinit _ (valid_drop E h T.missed hv.1)

/-! ## The RED cases -/

/-- A small environment for the counterexamples: operands add one more than
themselves, `touches` always answers true, the log lives at keys 1000 and
up, and no key is content-addressed. -/
def demo : Env where
  op := ⟨fun v o => v + o + 1⟩
  apply_ne_zero := by intro v o; show v + o + 1 ≠ 0; omega
  parts := ⟨fun v _ => v, fun _ _ => true⟩
  touches_sound := by intro v o S h; cases h
  head := 1000
  entry := fun p => 1001 + p
  isLog := fun k => decide (1000 ≤ k)
  isLog_head := by decide
  isLog_entry := by intro p; simp only [decide_eq_true_eq]; omega
  entry_inj := by intro p q h; omega
  entry_ne_head := by intro p; omega
  isCA := fun _ => false
  ca_not_log := by intro k h; cases h
  bytes := fun _ => 1
  bytes_ne_zero := by intro k; omega
  init := fun _ => 0

/-- A decider that copies key 5, read without validation, into key 6, and a
writer of key 5 that commits after the decider's snapshot. -/
def decider : Txn := ⟨1, [.exempt], [], fun σ => [.put 6 (σ 5)], fun _ => []⟩
/-- The writer: key 5 set to 1. -/
def writer : Txn := ⟨0, [], [], fun _ => [.put 5 1], fun _ => []⟩

/-- **`exempt_decision_breaks_serial`.** A decision on an exempt read is not
serial: the decider copied 0, while run after the writer it copies 1. This
is why a caller must not decide on a Log read, a commutative stretch, or
parts it did not name (the RED configs `MC_DefraLevel_Red_DecideOnLogRead`
and `MC_DefraLevel_Red_PartsNamesOther`). -/
theorem exempt_decision_breaks_serial :
    run demo [decider, writer] 6 = 0 ∧ serial demo [decider, writer] 6 = 1 := by
  constructor
  · rw [run_cons, run_cons]
    simp [run, txnWrites, decider, writer, applyWrites, applyWrite, upd, demo]
  · simp [serial, txnWrites, decider, writer, applyWrites, applyWrite, upd, demo]

/-- **`promoted_read_skew`.** A pessimistic transaction that reads key 1 at
its snapshot and key 2 with get_for_update after a writer changed both reads
(0, 1), and neither state of the history shows that pair. If such a
transaction validated nothing, as a write-free optimistic one may, it would
commit a view of no point in time (`MC_DefraLevel_Red_WriteFreePessimistic`). -/
theorem promoted_read_skew :
    demo.init 1 = 0 ∧ applyWrites demo demo.init [.put 1 1, .put 2 1] 2 = 1 ∧
      ¬ (demo.init 1 = 0 ∧ demo.init 2 = 1) ∧
      ¬ (applyWrites demo demo.init [.put 1 1, .put 2 1] 1 = 0 ∧
         applyWrites demo demo.init [.put 1 1, .put 2 1] 2 = 1) := by
  -- Key 1 and key 2 before the writer, and after it.
  simp [applyWrites, applyWrite, upd, demo]


/-- **`blindMerge_across_replacement`: why the blind-merge rule refuses a newer
replacement.** With a put of key 7 between a merge's snapshot and its
commit, the merge placed at its commit lands on the put and counts, while
placed at its snapshot the put erases it: the two positions disagree, so a
merge that crossed a replacement has no single place in the history that
both its snapshot and its effect agree with
(`MC_DefraLevel_Red_MergeIgnoresReplacement`). -/
theorem blindMerge_across_replacement (σ : State) (o : Nat) :
    applyWrite demo (applyWrite demo σ (.put 7 5)) (.merge 7 o) 7 ≠
      applyWrite demo (applyWrite demo σ (.merge 7 o)) (.put 7 5) 7 := by
  -- At its commit it gives 5 + o + 1; at its snapshot the put leaves 5.
  simp [applyWrite, upd, demo]
  omega

end Regolith.Validation
