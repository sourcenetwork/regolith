/-!
# WalRecovery: sync the sealed log before the next log takes a record (E2)

This file backs the TLA+ model `proofs/tla/WalRotation.tla`, invariants
`RecoversPrefix` (the conjunction of `RecoveryOpens` and `NoGap`) and
`KeepsSynced` (configurations `MC_WalRotation_Green`,
`MC_WalRotation_Red_NoSync` and `MC_WalRotation_Red_NoSync_Gap`).

The write-ahead log is a sequence of files. Records are appended to the
newest file; a rotation seals it and opens a new one. A power cut keeps,
of each file, the prefix an fsync made durable plus an arbitrary further
prefix of the bytes not yet synced, which may end in the middle of a
record: a torn tail. Replay (`WalReplayIter`, `WalPosition` in
`src/engine/wal_replay.rs`) tolerates a torn tail only in the newest file;
a torn record in an earlier file is damage, and recovery refuses.

What is proved, in plain words:

1. `step_inv` and `reachable_inv`: when a rotation syncs the sealed file
   before the new file exists, every sealed file is fully durable. That is
   the protocol's invariant.
2. `recovers_prefix`: then, after a power cut at any moment, whatever each
   file kept, recovery succeeds and yields commits `0, 1, ..., m - 1` for
   some `m`: a gap-free prefix of commit order, containing every record a
   sync made durable.
3. `no_sync_breaks_recovery`: a rotation that does not sync lets a power
   cut either make recovery refuse (a torn record in a sealed file) or
   recover commit 2 without commits 0 and 1 (a gap). This is the RED
   configuration as a concrete counterexample.

The order inside the rotation is the one the model checks: the sync of the
sealed file completes before the new file is created. A new file that
exists, even empty, beside an unsynced sealed file makes that sealed file
an earlier file, whose torn tail replay refuses.
-/

namespace Regolith.WalRecovery

/-- One write-ahead log file. -/
structure LogFile where
  /-- The records the file holds, in append order. A record is named by
  its commit number; commits are numbered `0, 1, 2, ...` in commit order. -/
  records : List Nat
  /-- How many leading records an fsync has made durable. -/
  synced : Nat
  deriving DecidableEq

/-- The whole log. -/
structure Wal where
  /-- The sealed files, oldest first: earlier rotations closed them. -/
  sealed : List LogFile
  /-- The newest file: the one taking records. -/
  active : LogFile
  /-- The number the next commit takes. -/
  next : Nat
  deriving DecidableEq

/-- Every record in the log, oldest file first. -/
def allRecords (w : Wal) : List Nat := (w.sealed.map LogFile.records).flatten ++ w.active.records

/-- How many records are durable: every record of a sealed file (the
invariant makes each one fully synced) plus the synced prefix of the newest
file. -/
def durable (w : Wal) : Nat := ((w.sealed.map LogFile.records).flatten).length + w.active.synced

/-- The protocol's invariant. -/
structure Inv (w : Wal) : Prop where
  /-- The files hold commits `0, 1, ..., next - 1`, in order, each once. -/
  commit_order : allRecords w = List.range w.next
  /-- Every sealed file is fully durable. -/
  sealed_synced : ∀ f ∈ w.sealed, f.synced = f.records.length
  /-- The newest file's synced prefix is within the file. -/
  active_synced : w.active.synced ≤ w.active.records.length

/-- The start: one empty file, no commit yet. -/
def init : Wal := ⟨[], ⟨[], 0⟩, 0⟩

/-- The fixed protocol's steps. -/
inductive Step : Wal → Wal → Prop
  /-- A commit appends its record to the newest file. -/
  | append (w : Wal) :
      Step w { w with active := { w.active with records := w.active.records ++ [w.next] },
                      next := w.next + 1 }
  /-- An fsync of the newest file makes every record in it durable. -/
  | sync (w : Wal) :
      Step w { w with active := { w.active with synced := w.active.records.length } }
  /-- The fix: a rotation first syncs the newest file, then seals it and
  opens a new, empty one. -/
  | rotate (w : Wal) :
      Step w { w with sealed := w.sealed ++ [{ w.active with synced := w.active.records.length }],
                      active := ⟨[], 0⟩ }

/-- Any number of steps, one after another. -/
inductive Steps : Wal → Wal → Prop
  /-- No step at all. -/
  | refl (w : Wal) : Steps w w
  /-- Some steps, then one more. -/
  | tail {u v w : Wal} : Steps u v → Step v w → Steps u w

/-- The start satisfies the invariant. -/
theorem init_inv : Inv init :=
  -- No records, no sealed file, nothing synced.
  ⟨rfl, fun _ h => absurd h List.not_mem_nil, Nat.le_refl 0⟩

/-- **Every step keeps the invariant.** -/
theorem step_inv {w w' : Wal}
    -- The invariant holds before the step.
    (hinv : Inv w)
    -- One step of the fixed protocol.
    (hstep : Step w w') :
    Inv w' := by
  obtain ⟨horder, hsealed, hactive⟩ := hinv
  cases hstep with
  | append =>
    refine ⟨?_, hsealed, ?_⟩
    · -- Appending commit `next` extends `0, ..., next - 1` by `next`.
      unfold allRecords at horder ⊢
      simp only
      rw [← List.append_assoc, horder, List.range_succ]
    · -- The synced prefix stays within the longer file.
      simp only [List.length_append, List.length_singleton]
      omega
  | sync =>
    -- The records do not change; the newest file is now fully synced.
    exact ⟨horder, hsealed, Nat.le_refl _⟩
  | rotate =>
    refine ⟨?_, ?_, Nat.le_refl 0⟩
    · -- The sealed file's records move to the sealed list unchanged.
      unfold allRecords at horder ⊢
      simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_append,
        List.flatten_cons, List.flatten_nil, List.append_nil]
      exact horder
    · -- The new sealed file was synced by the rotation; the older ones
      -- already were.
      intro f hf
      rcases List.mem_append.mp hf with hold | hnew
      · exact hsealed f hold
      · rcases List.mem_singleton.mp hnew with rfl
        rfl

/-- Every state the fixed protocol reaches satisfies the invariant. -/
theorem reachable_inv {w : Wal} (hreach : Steps init w) : Inv w := by
  induction hreach with
  | refl => exact init_inv
  | tail _ hstep ih => exact step_inv ih hstep

/-! ## Power cuts and replay -/

/-- What a power cut leaves of one file. -/
structure Cut where
  /-- How many whole records survive. -/
  kept : Nat
  /-- Whether part of one more record follows them: a torn tail. -/
  torn : Bool

/-- `Survives f c`: a power cut may leave `c` of file `f`. Everything synced
survives, at most every record survives, and a torn partial record can only
follow when at least one more record was written. -/
def Survives (f : LogFile) (c : Cut) : Prop :=
  f.synced ≤ c.kept ∧ c.kept ≤ f.records.length ∧ (c.torn = true → c.kept < f.records.length)

/-- Replay after a power cut. The sealed files come first, oldest first,
each with what the cut left of it; then the newest file. A sealed file
with a torn tail makes recovery refuse (`none`). The newest file's torn
tail ends the log. Otherwise recovery yields every surviving record, in
file order. -/
def replay : List (LogFile × Cut) → LogFile × Cut → Option (List Nat)
  -- The newest file: its whole surviving records, whatever follows them.
  | [], (f, c) => some (f.records.take c.kept)
  -- A sealed file: refuse if torn, else its records and then the rest.
  | (f, c) :: rest, newest =>
    if c.torn then none else (replay rest newest).map (f.records.take c.kept ++ ·)

/-- When every sealed file is fully synced, no power cut tears one, so
replay succeeds and yields all of their records, then what survived of the
newest file. -/
theorem replay_synced {newest : LogFile × Cut} :
    ∀ (cs : List (LogFile × Cut)),
      -- Every sealed file is fully synced ...
      (∀ p ∈ cs, p.1.synced = p.1.records.length) →
      -- ... and the cut left it something it may leave.
      (∀ p ∈ cs, Survives p.1 p.2) →
      replay cs newest =
        some (((cs.map Prod.fst).map LogFile.records).flatten ++
          newest.1.records.take newest.2.kept)
  | [], _, _ => by
    -- Only the newest file.
    obtain ⟨f, c⟩ := newest
    simp [replay]
  | (f, c) :: rest, hsync, hsurv => by
    -- The first sealed file is fully synced, so the cut kept all of it and
    -- could not tear it.
    have hs := hsync (f, c) List.mem_cons_self
    obtain ⟨hlo, hhi, htorn⟩ := hsurv (f, c) List.mem_cons_self
    simp only at hs hlo hhi htorn
    have hkept : c.kept = f.records.length := by omega
    have hnottorn : c.torn = false := by
      cases ht : c.torn
      · rfl
      · have := htorn ht
        omega
    -- The rest replays by induction.
    have ih := replay_synced (newest := newest) rest
      (fun p hp => hsync p (List.mem_cons_of_mem _ hp))
      (fun p hp => hsurv p (List.mem_cons_of_mem _ hp))
    -- Replay does not refuse the untorn file, yields all of its records
    -- (`take` of the whole length is the whole list), then the rest.
    simp only [replay, hnottorn, Bool.false_eq_true, ite_false, ih, Option.map_some,
      List.map_cons, List.flatten_cons, hkept, List.take_length, List.append_assoc]

/-- **E2, recovery yields a gap-free prefix.** Take any state the fixed
protocol satisfies the invariant in, and any power cut: each sealed file
and the newest file keep something a cut may leave. Recovery then succeeds
and yields commits `0, 1, ..., m - 1` for some `m` no larger than the
number of commits, and `m` covers every durable record. -/
theorem recovers_prefix {w : Wal}
    -- The invariant holds.
    (hinv : Inv w)
    -- What the cut left of each sealed file, in order ...
    (cs : List (LogFile × Cut)) (hcs : cs.map Prod.fst = w.sealed)
    -- ... each something a cut may leave ...
    (hsurv : ∀ p ∈ cs, Survives p.1 p.2)
    -- ... and what it left of the newest file.
    (c : Cut) (hc : Survives w.active c) :
    ∃ m, replay cs (w.active, c) = some (List.range m) ∧ m ≤ w.next ∧ durable w ≤ m := by
  -- horder: the log holds commits `0, ..., next - 1`; hsealed: every sealed
  -- file is fully synced. hlo, hhi: the newest file kept between its synced
  -- prefix and all of its records.
  obtain ⟨horder, hsealed, -⟩ := hinv
  obtain ⟨hlo, hhi, -⟩ := hc
  -- The sealed files are fully synced, so replay is all of their records
  -- followed by what survived of the newest file.
  have hsync : ∀ p ∈ cs, p.1.synced = p.1.records.length := by
    intro p hp
    apply hsealed
    rw [← hcs]
    exact List.mem_map_of_mem hp
  rw [replay_synced cs hsync hsurv, hcs]
  -- Name the sealed files' records `F`; with the newest file's they are
  -- `0, ..., next - 1`.
  generalize hF : (w.sealed.map LogFile.records).flatten = F at horder
  unfold allRecords at horder
  rw [hF] at horder
  -- Counting: the sealed records and the newest file's make `next`.
  have hlen : F.length + w.active.records.length = w.next := by
    have := congrArg List.length horder
    simpa using this
  -- `F` followed by the first `kept` records of the newest file is the
  -- first `F.length + kept` records of the whole log, hence a range. That
  -- length is at most `next`, since `kept` is at most the newest file's.
  refine ⟨F.length + c.kept, ?_, by omega, ?_⟩
  · -- Taking `F.length + kept` records of `F ++ newest` takes all of `F`
    -- and then `kept` records of the newest file.
    have htake : F ++ w.active.records.take c.kept =
        (F ++ w.active.records).take (F.length + c.kept) := by
      rw [List.take_append,
        List.take_of_length_le (l := F) (i := F.length + c.kept) (by omega)]
      simp
    -- So replay yields the first `F.length + kept` of `0, ..., next - 1`,
    -- which is `0, ..., F.length + kept - 1` (`List.take_range`).
    simp only [htake, horder, List.take_range]
    congr 2
    omega
  · -- Everything durable survived: the sealed records all, and the newest
    -- file's synced prefix, since `kept` is at least that.
    unfold durable
    rw [hF]
    omega

/-- **E2 for every reachable state.** -/
theorem reachable_recovers_prefix {w : Wal}
    -- `w` is reachable from the start by the fixed protocol.
    (hreach : Steps init w)
    (cs : List (LogFile × Cut)) (hcs : cs.map Prod.fst = w.sealed)
    (hsurv : ∀ p ∈ cs, Survives p.1 p.2)
    (c : Cut) (hc : Survives w.active c) :
    ∃ m, replay cs (w.active, c) = some (List.range m) ∧ m ≤ w.next ∧ durable w ≤ m :=
  recovers_prefix (reachable_inv hreach) cs hcs hsurv c hc

/-! ## The RED case: rotation without a sync -/

/-- The defective protocol: a rotation seals the newest file as it is,
synced or not. -/
inductive StepNoSync : Wal → Wal → Prop
  /-- As `Step.append`. -/
  | append (w : Wal) :
      StepNoSync w { w with active := { w.active with records := w.active.records ++ [w.next] },
                            next := w.next + 1 }
  /-- As `Step.sync`. -/
  | sync (w : Wal) :
      StepNoSync w { w with active := { w.active with synced := w.active.records.length } }
  /-- The defect: no sync before the new file opens. -/
  | rotate (w : Wal) :
      StepNoSync w { w with sealed := w.sealed ++ [w.active], active := ⟨[], 0⟩ }

/-- Any number of defective steps. -/
inductive StepsNoSync : Wal → Wal → Prop
  /-- No step at all. -/
  | refl (w : Wal) : StepsNoSync w w
  /-- Some steps, then one more. -/
  | tail {u v w : Wal} : StepsNoSync u v → StepNoSync v w → StepsNoSync u w

/-- Commits 0 and 1 in a sealed file that was never synced, and commit 2
in the newest file. -/
def unsyncedRotation : Wal := ⟨[⟨[0, 1], 0⟩], ⟨[2], 0⟩, 3⟩

/-- **`no_sync_breaks_recovery`.** The defective protocol reaches
`unsyncedRotation` from the start: two appends, a rotation without a sync,
one more append. Then two power cuts break recovery:

* the sealed file keeps commit 0 and half of commit 1: a torn record in a
  sealed file, and recovery refuses;
* the sealed file keeps nothing and the newest file keeps commit 2:
  recovery yields commit 2 alone, which is no prefix of commit order. -/
theorem no_sync_breaks_recovery :
    StepsNoSync init unsyncedRotation ∧
    -- The torn cut is one a power cut may leave, and replay refuses.
    Survives ⟨[0, 1], 0⟩ ⟨1, true⟩ ∧
    replay [(⟨[0, 1], 0⟩, ⟨1, true⟩)] (⟨[2], 0⟩, ⟨1, false⟩) = none ∧
    -- The clean cut is one a power cut may leave, and replay leaves a gap.
    Survives ⟨[0, 1], 0⟩ ⟨0, false⟩ ∧ Survives ⟨[2], 0⟩ ⟨1, false⟩ ∧
    replay [(⟨[0, 1], 0⟩, ⟨0, false⟩)] (⟨[2], 0⟩, ⟨1, false⟩) = some [2] ∧
    ∀ m, [2] ≠ List.range m := by
  refine ⟨?_, ?_, by decide, ?_, ?_, by decide, ?_⟩
  · -- The four defective steps, in order.
    exact .tail (.tail (.tail (.tail (.refl _) (.append _)) (.append _)) (.rotate _)) (.append _)
  · -- Nothing synced, one of two records kept, a torn second one.
    exact ⟨by decide, by decide, fun _ => by decide⟩
  · -- Nothing synced, nothing kept, no torn record.
    exact ⟨by decide, by decide, fun h => absurd h (by decide)⟩
  · -- Nothing synced, the one record kept, no torn record.
    exact ⟨by decide, by decide, fun h => absurd h (by decide)⟩
  · -- A range of length 1 is `[0]`, not `[2]`.
    intro m h
    have hlen := congrArg List.length h
    simp only [List.length_cons, List.length_nil, List.length_range] at hlen
    subst hlen
    simp at h

end Regolith.WalRecovery
