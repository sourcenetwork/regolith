/-!
# WalRecovery: the rotation sync (E2) and format 2 replay (plan 4.2)

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

The second part of this file, "Format 2", backs `proofs/tla/WalRecovery.tla`
(configurations `MC_WalRecovery_*`): the `synced_through` stamps, CLOSE,
and the replay rule that refuses below P and drops a tail above it. Its
own header lists what it proves.
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

/-! ## Format 2: `synced_through` stamps, CLOSE, and the replay rule (plan 4.2)

This part backs `proofs/tla/WalRecovery.tla`, invariants `RecoveryOpens`,
`NoGap`, `KeepsSynced`, `AckedSurvive`, `NoProvenLoss`, `LossIsReported`
and `WrongKeyRefuses` (configurations `MC_WalRecovery_*`).

Format 2 stamps every group record with `synced_through`: how many leading
records the last completed sync had made durable when the record was
written. A clean close syncs every record, appends CLOSE and syncs again.
Replay of the newest log reads P, the largest stamp of any usable record,
or the whole file when a usable CLOSE ends it, and finds O, the first
unusable record. It refuses when O < P, since a surviving record proves
the damaged one was synced; otherwise it keeps the records before O and
drops the rest, reporting it.

Positions and stamps count records here, not bytes: record `i` starts
where `i` records end, so "O < P in bytes" is "O < P in records".

The earlier logs are complete by the rotation sync (the first part of this
file), so here they are a list of commits `0, 1, ..., e - 1`, all synced;
the newest log's group `i` holds commit `e + i`. One record per group,
holding one commit: a group of several is lost or kept whole, like one.

What is proved, in plain words:

1. `step2_inv`, `reachable2_inv`: the writer keeps every stamp at or below
   the completed sync, and appends CLOSE only after a sync of every group.
2. `honest_of_inv`: so under any crash that keeps the synced prefix (the
   device honoured its flush), no surviving record claims more than
   survived: P is at most O.
3. `replay2_opens_of_honest` and `recovers_prefix2`: then replay opens,
   and recovery is a gap-free prefix of commit order that keeps every
   group a completed sync covered.
4. `replay2_keeps_proven`: whenever replay opens, it keeps every group
   below P: no record a surviving stamp proves synced is discarded.
5. `residual_is_reported`: when damage reached the synced prefix (bit rot,
   or a torn write over a sector holding acknowledged bytes; D6 leaves
   that case open) and replay still opens, it has discarded a nonempty
   tail, which it reports: the loss is never silent.
6. `wrong_key_refuses`: with encryption at rest the stamp is sealed under
   the key, so a wrong key refuses instead of dropping the log.
7. The RED cases as counterexamples: `drop_below_p_loses_proven`,
   `refuse_above_p_never_opens`, `format1_refuses_torn_tail` and
   `unsealed_stamp_drops_log`.
-/

/-- The newest log in format 2: its group records, then CLOSE when it was
closed cleanly. -/
structure Log2 where
  /-- Each group record's `synced_through` stamp, in order. -/
  stamps : List Nat
  /-- How many leading records a completed sync made durable. CLOSE, when
  present, is the record after the groups. -/
  synced : Nat
  /-- Whether CLOSE follows the groups. -/
  closed : Bool

/-- How many records the newest log holds: the groups, and CLOSE. -/
def Log2.total (l : Log2) : Nat := l.stamps.length + (if l.closed then 1 else 0)

/-- The whole write-ahead log in format 2. -/
structure Wal2 where
  /-- The commits of the earlier logs, in order. -/
  earlier : List Nat
  /-- The newest log. -/
  log : Log2

/-- O: how many leading records are usable, which is the position of the
first unusable one. `ok` says, for each record the crash left in the file,
whether it is usable (it survived and its checksum or tag verifies). -/
def firstBad : List Bool → Nat
  | [] => 0
  | true :: rest => firstBad rest + 1
  | false :: _ => 0

/-- The largest stamp among the usable group records. -/
def groupProof : List Nat → List Bool → Nat
  | st :: sts, ok :: oks => max (if ok then st else 0) (groupProof sts oks)
  | _, _ => 0

/-- P: what the surviving records prove synced. The largest stamp of a
usable group record, or the whole file when CLOSE survived usable. -/
def proofOf (l : Log2) (ok : List Bool) : Nat :=
  max (groupProof l.stamps ok)
    (if l.closed && ok[l.stamps.length]? == some true then l.stamps.length + 1 else 0)

/-- Replay of the newest log in format 2. `stampOk` says whether the log's
stamp verifies (with encryption, whether the key is right). The result is
how many group records recovery keeps, or `none` when it refuses. -/
def replay2 (stampOk : Bool) (l : Log2) (ok : List Bool) : Option Nat :=
  if !stampOk then none
  else if firstBad ok < proofOf l ok then none
  else some (min (firstBad ok) l.stamps.length)

/-- What recovery yields when it keeps `kept` groups of the newest log:
the earlier logs' commits, then the newest log's first `kept`. -/
def recovered2 (w : Wal2) (kept : Nat) : List Nat :=
  w.earlier ++ List.range' w.earlier.length kept

/-- `Survives2 l ok`: a crash the device's flush honoured may leave `ok`.
Every record a completed sync covered survived usable, and the file holds
no more records than were written. -/
def Survives2 (l : Log2) (ok : List Bool) : Prop :=
  l.synced ≤ firstBad ok ∧ ok.length ≤ l.total

/-- The writer's invariant on the newest log. -/
structure Inv2Log (l : Log2) : Prop where
  /-- No stamp claims more than the completed sync. -/
  stamps_le : ∀ st ∈ l.stamps, st ≤ l.synced
  /-- The sync covered only records that exist. -/
  synced_le : l.synced ≤ l.total
  /-- CLOSE was appended only after every group was synced. -/
  close_after_sync : l.closed = true → l.stamps.length ≤ l.synced

/-- The invariant of the whole log: the earlier logs hold commits
`0, ..., e - 1`, and the newest log keeps `Inv2Log`. -/
structure Inv2 (w : Wal2) : Prop where
  /-- The earlier logs hold commits `0, ..., e - 1` in order. -/
  earlier_order : w.earlier = List.range w.earlier.length
  /-- The newest log keeps the writer's invariant. -/
  log_inv : Inv2Log w.log

/-- The start: no earlier log, an empty newest log. -/
def init2 : Wal2 := ⟨[], ⟨[], 0, false⟩⟩

/-- The format 2 writer's steps. -/
inductive Step2 : Wal2 → Wal2 → Prop
  /-- A commit group appends its record, stamped with the completed sync. -/
  | append (w : Wal2) (hopen : w.log.closed = false) :
      Step2 w { w with log := { w.log with stamps := w.log.stamps ++ [w.log.synced] } }
  /-- A sync that began when `k` records were written completes. -/
  | sync (w : Wal2) (k : Nat) (hgrow : w.log.synced < k) (hle : k ≤ w.log.total) :
      Step2 w { w with log := { w.log with synced := k } }
  /-- A clean close appends CLOSE once every group is synced; a later
  `sync` makes CLOSE durable. -/
  | close (w : Wal2) (hopen : w.log.closed = false) (hall : w.log.synced = w.log.stamps.length) :
      Step2 w { w with log := { w.log with closed := true } }
  /-- A rotation syncs the newest log (E2), so its commits join the
  earlier logs, and a new, empty log takes the next record. -/
  | rotate (w : Wal2) (hopen : w.log.closed = false) :
      Step2 w ⟨w.earlier ++ List.range' w.earlier.length w.log.stamps.length, ⟨[], 0, false⟩⟩

/-- Any number of format 2 steps. -/
inductive Steps2 : Wal2 → Wal2 → Prop
  /-- No step at all. -/
  | refl (w : Wal2) : Steps2 w w
  /-- Some steps, then one more. -/
  | tail {u v w : Wal2} : Steps2 u v → Step2 v w → Steps2 u w

/-- The start satisfies the invariant. -/
theorem init2_inv : Inv2 init2 :=
  -- No commit, no stamp, nothing synced, not closed.
  ⟨rfl, ⟨fun _ h => absurd h List.not_mem_nil, Nat.le_refl 0, fun h => absurd h (by decide)⟩⟩

/-- **Every format 2 step keeps the invariant.** -/
theorem step2_inv {w w' : Wal2}
    -- The invariant holds before the step.
    (hinv : Inv2 w)
    -- One step of the writer.
    (hstep : Step2 w w') :
    Inv2 w' := by
  obtain ⟨horder, ⟨hst, hsyn, hclose⟩⟩ := hinv
  cases hstep with
  | append hopen =>
    refine ⟨horder, ⟨?_, ?_, ?_⟩⟩ <;> dsimp only
    · -- The new stamp is the completed sync; the old ones were below it.
      intro st hmem
      rcases List.mem_append.mp hmem with h | h
      · exact hst st h
      · rw [List.mem_singleton.mp h]
        exact Nat.le_refl _
    · -- One more record: the sync still covers only records that exist.
      simp only [Log2.total, List.length_append, List.length_singleton] at hsyn ⊢
      omega
    · -- The log is still open.
      intro h
      rw [hopen] at h
      cases h
  | sync k hgrow hle =>
    refine ⟨horder, ⟨?_, hle, ?_⟩⟩ <;> dsimp only
    · -- The sync only grew: every stamp is still below it.
      intro st hmem
      have := hst st hmem
      omega
    · -- If closed, every group was synced before, and still is.
      intro h
      have := hclose h
      omega
  | close hopen hall =>
    refine ⟨horder, ⟨hst, ?_, fun _ => Nat.le_of_eq hall.symm⟩⟩
    -- CLOSE adds a record after every synced group.
    simp only [Log2.total, hopen] at hsyn ⊢
    simp only [Bool.false_eq_true, ite_false, ite_true] at hsyn ⊢
    omega
  | rotate hopen =>
    refine ⟨?_, ⟨fun _ h => absurd h List.not_mem_nil, Nat.le_refl 0, ?_⟩⟩ <;> dsimp only
    · -- The newest log's commits continue the earlier ones.
      simp only [List.length_append, List.length_range']
      rw [horder, List.length_range, List.range_add, List.range'_eq_map_range]
    · -- The new log is open.
      intro h
      cases h

/-- Every state the format 2 writer reaches satisfies the invariant. -/
theorem reachable2_inv {w : Wal2} (hreach : Steps2 init2 w) : Inv2 w := by
  induction hreach with
  | refl => exact init2_inv
  | tail _ hstep ih => exact step2_inv ih hstep

/-- O is at most the number of records in the file. -/
theorem firstBad_le_length : ∀ ok : List Bool, firstBad ok ≤ ok.length
  | [] => Nat.le_refl 0
  | true :: rest => by
    have := firstBad_le_length rest
    simp only [firstBad, List.length_cons]
    omega
  | false :: _ => Nat.zero_le _

/-- If the first `g` records are usable and record `g` is too, the first
`g + 1` are. -/
theorem firstBad_succ : ∀ (ok : List Bool) (g : Nat), g ≤ firstBad ok → ok[g]? = some true →
    g + 1 ≤ firstBad ok
  | [], _, _, h => by simp at h
  | true :: rest, 0, _, _ => by simp only [firstBad]; omega
  | true :: rest, g + 1, hle, hg => by
    -- Drop the first record: the claim for the rest, shifted by one.
    simp only [firstBad] at hle ⊢
    have := firstBad_succ rest g (by omega) (by simpa using hg)
    omega
  | false :: _, 0, _, hg => by simp at hg
  | false :: _, g + 1, hle, _ => by simp only [firstBad] at hle; omega

/-- The largest usable stamp is at most any bound on every stamp. -/
theorem groupProof_le {n : Nat} : ∀ (sts : List Nat) (oks : List Bool),
    (∀ st ∈ sts, st ≤ n) → groupProof sts oks ≤ n
  | [], _, _ => Nat.zero_le _
  | _ :: _, [], _ => Nat.zero_le _
  | st :: sts, ok :: oks, h => by
    have h1 := h st List.mem_cons_self
    have h2 := groupProof_le sts oks fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [groupProof]
    split <;> omega

/-- **The stamps are honest.** Under the writer's invariant, after a crash
the device's flush honoured, no usable record proves more than survived:
P is at most O. -/
theorem honest_of_inv {l : Log2} {ok : List Bool}
    -- The writer's invariant.
    (hinv : Inv2Log l)
    -- A crash that kept the synced prefix.
    (hsurv : Survives2 l ok) :
    proofOf l ok ≤ firstBad ok := by
  obtain ⟨hst, -, hclose⟩ := hinv
  obtain ⟨hsyn, -⟩ := hsurv
  unfold proofOf
  refine Nat.max_le.mpr ⟨?_, ?_⟩
  · -- Every stamp is at most the completed sync, which survived.
    exact Nat.le_trans (groupProof_le _ _ hst) hsyn
  · -- A usable CLOSE: every group before it was synced, so it survived,
    -- and CLOSE itself is usable.
    split
    · rename_i h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hc, hg⟩ := h
      exact firstBad_succ ok _ (Nat.le_trans (hclose hc) hsyn) hg
    · exact Nat.zero_le _

/-- **Replay opens on honest stamps.** When the stamp verifies and P is at
most O, replay keeps every group before O. -/
theorem replay2_opens_of_honest {l : Log2} {ok : List Bool}
    -- P is at most O.
    (h : proofOf l ok ≤ firstBad ok) :
    replay2 true l ok = some (min (firstBad ok) l.stamps.length) := by
  have hnot : ¬ firstBad ok < proofOf l ok := by omega
  simp only [replay2, Bool.not_true, Bool.false_eq_true, ite_false, hnot]

/-- **Replay never discards what a stamp proves synced.** Whenever replay
opens, it keeps every group below P. -/
theorem replay2_keeps_proven {s : Bool} {l : Log2} {ok : List Bool} {kept : Nat}
    -- Replay opened, keeping `kept` groups.
    (h : replay2 s l ok = some kept) :
    min (proofOf l ok) l.stamps.length ≤ kept := by
  unfold replay2 at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hge
      simp only [Option.some.injEq] at h
      subst h
      omega

/-- **Format 2 recovery yields a gap-free prefix that keeps every synced
commit.** For every state the writer reaches and every crash the device's
flush honoured, replay opens; recovery yields commits `0, ..., n - 1` for
some `n`; and it keeps every group a completed sync covered. -/
theorem recovers_prefix2 {w : Wal2} {ok : List Bool}
    -- `w` is reachable by the format 2 writer.
    (hreach : Steps2 init2 w)
    -- The crash kept the synced prefix.
    (hsurv : Survives2 w.log ok) :
    ∃ kept, replay2 true w.log ok = some kept ∧
      recovered2 w kept = List.range (w.earlier.length + kept) ∧
      min w.log.synced w.log.stamps.length ≤ kept ∧ kept ≤ w.log.stamps.length := by
  obtain ⟨horder, hlog⟩ := reachable2_inv hreach
  refine ⟨min (firstBad ok) w.log.stamps.length,
    replay2_opens_of_honest (honest_of_inv hlog hsurv), ?_, ?_, Nat.min_le_right _ _⟩
  · -- The earlier commits `0, ..., e - 1`, then `e, ..., e + kept - 1`.
    unfold recovered2
    rw [List.range_add, List.range'_eq_map_range, ← horder]
  · -- O is at least the completed sync, since the synced prefix survived.
    have := hsurv.1
    omega

/-- **Residual damage is never silent.** Suppose a crash damaged bytes a
completed sync had covered, but the file still holds the synced prefix's
records. If replay opens and keeps fewer groups than were synced, it has
discarded a nonempty tail: records from O on are in the file, so the
discard is reported. -/
theorem residual_is_reported {s : Bool} {l : Log2} {ok : List Bool} {kept : Nat}
    -- The file holds at least the records the sync covered.
    (hlen : l.synced ≤ ok.length)
    -- Replay opened, keeping `kept` groups ...
    (h : replay2 s l ok = some kept)
    -- ... fewer than were synced.
    (hlost : kept < min l.synced l.stamps.length) :
    firstBad ok < ok.length := by
  unfold replay2 at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      omega

/-- **A wrong key refuses.** With encryption at rest the stamp is sealed
under the key and was synced when the log was created; under the wrong
key its tag fails, and replay refuses rather than drop the log. -/
theorem wrong_key_refuses (l : Log2) (ok : List Bool) : replay2 false l ok = none := rfl

/-! ### The RED cases of the format 2 rule -/

/-- The defect: replay drops the tail at O even when O < P. -/
def replayDropBelowP (l : Log2) (ok : List Bool) : Option Nat :=
  some (min (firstBad ok) l.stamps.length)

/-- **`drop_below_p_loses_proven`.** Group 0 was synced; group 1 was
written after that sync completed, so it is stamped 1. A crash damages
group 0 (residual damage) and keeps group 1. P is 1 and O is 0: the
design refuses, while the defect opens with nothing, losing group 0 that
group 1's stamp proves synced. -/
theorem drop_below_p_loses_proven :
    proofOf ⟨[0, 1], 1, false⟩ [false, true] = 1 ∧
    replay2 true ⟨[0, 1], 1, false⟩ [false, true] = none ∧
    replayDropBelowP ⟨[0, 1], 1, false⟩ [false, true] = some 0 := by
  decide

/-- The defect: replay refuses every unusable record, a torn tail above P
included. -/
def replayRefuseAny (l : Log2) (ok : List Bool) : Option Nat :=
  if firstBad ok < ok.length then none else some (min (firstBad ok) l.stamps.length)

/-- **`refuse_above_p_never_opens`.** Nothing synced yet; a crash keeps
group 0 and tears group 1. That crash honours every flush (`Survives2`),
and the design opens with group 0, but the defect refuses: a database
that never opens. -/
theorem refuse_above_p_never_opens :
    Survives2 ⟨[0, 0], 0, false⟩ [true, false] ∧
    replay2 true ⟨[0, 0], 0, false⟩ [true, false] = some 1 ∧
    replayRefuseAny ⟨[0, 0], 0, false⟩ [true, false] = none := by
  refine ⟨⟨by decide, by decide⟩, by decide, by decide⟩

/-- What a crash may leave of one record, as format 1 tells them apart. -/
inductive Kind where
  /-- The record survived whole. -/
  | intact
  /-- The record is whole but its bytes are wrong. -/
  | garbage
  /-- The record's bytes read back as zeros: the length persisted, the
  data did not. -/
  | zero
  /-- The file ends inside the record: a torn write. -/
  | torn
  deriving DecidableEq

/-- Format 1's replay (E3): at the first record that is not intact, a
torn record, or zeros to the end of the file, end the log there; anything
else refuses. The result is how many records it keeps. -/
def replay1 : List Kind → Option Nat
  | [] => some 0
  | .intact :: rest => (replay1 rest).map (· + 1)
  | .torn :: _ => some 0
  | k :: rest => if k = .zero ∧ rest.all (· == .zero) then some 0 else none

/-- **`format1_refuses_torn_tail`.** A crash keeps group 0 and leaves group
1 whole but wrong, as when its length persisted before its data. Format 1
refuses; format 2, where every unusable record is alike, opens with group
0. -/
theorem format1_refuses_torn_tail :
    replay1 [.intact, .garbage] = none ∧
    replay2 true ⟨[0, 0], 0, false⟩ ([Kind.intact, .garbage].map (· == .intact)) = some 1 := by
  decide

/-- **`unsealed_stamp_drops_log`.** Two groups, both synced. Under the
wrong key every record's tag fails, so no stamp can be read and P is 0.
If the stamp were not sealed under the key, it would verify, O would be 0
and replay would drop the whole log as a tail, losing both synced groups.
Sealed, it refuses (`wrong_key_refuses`). -/
theorem unsealed_stamp_drops_log :
    replay2 true ⟨[0, 1], 2, false⟩ [false, false] = some 0 ∧
    replay2 false ⟨[0, 1], 2, false⟩ [false, false] = none := by
  decide

end Regolith.WalRecovery
