-- The log files, cuts and replay of the rotation part, and the format 2 replay, come from here.
import Regolith.WalRecovery

/-!
# WalClose: a close that seals its last log in place (E46)

This file backs the TLA+ model `proofs/tla/WalRecovery.tla`: its actions
`SealInPlace`, `FlushInPlace` and `CloseNext` with the invariants
`RecoveryOpens`, `NoGap` and `KeepsSynced`, and the RED configuration
`MC_WalRecovery_Red_NewLogBeforeFlush`.

## The story, for a reader who has never seen the code

Before a write counts, the database notes it in a file, the write-ahead
log. Writing to a file does not put the bytes on the disk; only a "sync"
does. When the log has served one in-memory table (a "memtable"), the
memtable is "sealed", written out as a table on disk ("flushed"), and the
log is no longer needed. After a power cut, recovery reads every log that
is still needed. It forgives a torn record at the end of the newest log,
which is where an unsynced write can end, but takes a torn record in an
earlier log for damage and refuses to open.

Closing the database flushes the last memtable. The old way sealed it as
a rotation does: sync the whole log (tens of megabytes, the slow part),
create the next log, flush, close the next log. The new way seals it "in
place": the log stays the newest file, where a torn tail is forgiven, so
it needs no sync. The flush writes the table and, in the same synced note
in the manifest, says "recovery skips this log". Only then is the log
removed, and the next log created and closed.

Tiny example. Commits 0 and 1 sit unsynced in the only log when close
begins. A power cut before the manifest note is durable finds that log
as the newest and keeps a prefix of it, maybe just commit 0. A power cut
after finds commits 0 and 1 in a table. Either way recovery opens with a
gap-free prefix. If close created the next log first (the RED case), a
power cut could tear commit 1 in a log that is no longer the newest, and
recovery would refuse to open.

What is proved, in plain words:

1. `close_step_inv`, `close_reachable_inv`: with the seal in place, every
   earlier log stays fully synced, and the tables, the earlier logs and
   the newest log hold commits `0, 1, ..., next - 1` in order.
2. `close_recovers_prefix`, `close_reachable_recovers_prefix`: after a
   power cut at any moment, recovery opens and yields a gap-free prefix
   of commit order holding every durable commit.
3. `new_log_first_breaks_recovery`: creating the next log before the
   flush is durable lets a power cut make recovery refuse (RED).
-/

-- Everything below is named Regolith.WalClose.<name>.
namespace Regolith.WalClose

-- Use the rotation part's log files, cuts and replay without the prefix.
open Regolith.WalRecovery

/-! ## The seal in place -/

/-- The whole log while a close may be under way: what is in tables, the
earlier log files, the newest one, and whether the close sealed it in
place. -/
structure CloseWal where
  /-- The commits flushed into tables, in order: recovery reads no log that holds them. -/
  tables : List Nat
  /-- The earlier log files, oldest first, each waiting for its memtable's flush. -/
  sealed : List LogFile
  /-- The newest log file. -/
  active : LogFile
  /-- The number the next commit takes. -/
  next : Nat
  /-- Whether the close sealed the newest log in place: it takes no record any more. -/
  inPlace : Bool
  -- Lean may compare two such states for equality, so the counterexample below can be computed.
  deriving DecidableEq

/-- The commits of the earlier log files, oldest first. -/
def sealedRecords (w : CloseWal) : List Nat :=
  -- Join the records of every earlier file.
  (w.sealed.map LogFile.records).flatten

/-- Every commit, in order: the tables', the earlier files', the newest file's. -/
def closeRecords (w : CloseWal) : List Nat :=
  -- The three parts, one after another.
  w.tables ++ sealedRecords w ++ w.active.records

/-- How many commits are durable: those in tables, every one of an
earlier file (the invariant makes each fully synced), and the synced
prefix of the newest file. -/
def closeDurable (w : CloseWal) : Nat :=
  -- The three counts added up.
  w.tables.length + (sealedRecords w).length + w.active.synced

/-- The protocol's invariant. -/
structure CloseInv (w : CloseWal) : Prop where
  /-- Tables and files hold commits `0, 1, ..., next - 1`, in order, each once. -/
  commit_order : closeRecords w = List.range w.next
  /-- Every earlier file is fully synced. -/
  sealed_synced : ∀ f ∈ w.sealed, f.synced = f.records.length
  /-- The newest file's synced prefix is within the file. -/
  active_synced : w.active.synced ≤ w.active.records.length

/-- The start: no table, no earlier file, an empty newest file, no commit. -/
def closeInit : CloseWal := ⟨[], [], ⟨[], 0⟩, 0, false⟩

/-- The steps of the engine, a close included. -/
inductive CloseStep : CloseWal → CloseWal → Prop
  /-- A commit appends its record to the newest file, unless the close sealed it in place. -/
  | append (w : CloseWal) (hopen : w.inPlace = false) :
      -- The newest file gains the record of commit `next` at its end,
      CloseStep w { w with active := { w.active with records := w.active.records ++ [w.next] },
                           -- and the next commit number moves up by one.
                           next := w.next + 1 }
  /-- A sync of the newest file makes every record in it durable. -/
  | sync (w : CloseWal) :
      -- The newest file's synced count becomes its number of records.
      CloseStep w { w with active := { w.active with synced := w.active.records.length } }
  /-- A rotation (E2): sync the newest file, seal it, open an empty one. It
  is also how a close that failed after sealing in place takes writes
  again (`Ordered::reopen_log`), so it ends a seal in place. -/
  | rotate (w : CloseWal) :
      -- The newest file, marked fully synced, joins the earlier files,
      CloseStep w { w with sealed := w.sealed ++ [{ w.active with synced := w.active.records.length }],
                           -- a new, empty file becomes the newest,
                           active := ⟨[], 0⟩,
                           -- and no seal in place is left.
                           inPlace := false }
  /-- The flush of the oldest earlier file's memtable: its commits are in a
  table, with the manifest note that recovery skips the file, which is
  then removed. -/
  | flush (w : CloseWal) (f : LogFile) (rest : List LogFile) (holdest : w.sealed = f :: rest) :
      -- The file's commits join the tables, and the file leaves the earlier ones.
      CloseStep w { w with tables := w.tables ++ f.records, sealed := rest }
  /-- The close seals the last memtable in place: nothing is synced, no file is created. -/
  | sealInPlace (w : CloseWal) :
      -- Only the flag changes.
      CloseStep w { w with inPlace := true }
  /-- The flush of the memtable sealed in place, once every earlier file is
  flushed: its commits are in a table, the note says recovery skips its
  file, and the file is removed. The next file, created after this, holds
  no commit: here it is the empty newest file. -/
  | flushInPlace (w : CloseWal) (hin : w.inPlace = true) (hnone : w.sealed = []) :
      -- The newest file's commits join the tables,
      CloseStep w { w with tables := w.tables ++ w.active.records,
                           -- the next, empty file is the newest,
                           active := ⟨[], 0⟩,
                           -- and the seal in place is done.
                           inPlace := false }

/-- Any number of steps, one after another. -/
inductive CloseSteps : CloseWal → CloseWal → Prop
  /-- No step at all. -/
  | refl (w : CloseWal) : CloseSteps w w
  /-- Some steps, then one more. -/
  | tail {u v w : CloseWal} : CloseSteps u v → CloseStep v w → CloseSteps u w

/-- The start satisfies the invariant. -/
theorem close_init_inv : CloseInv closeInit :=
  -- No commits anywhere, no earlier file, nothing synced.
  ⟨rfl, fun _ h => absurd h List.not_mem_nil, Nat.le_refl 0⟩

/-- **Every step keeps the invariant.** -/
theorem close_step_inv {w w' : CloseWal}
    -- The invariant holds before the step.
    (hinv : CloseInv w)
    -- One step of the engine.
    (hstep : CloseStep w w') :
    -- The statement: the invariant holds after the step.
    CloseInv w' := by
  -- Take the invariant's three facts.
  obtain ⟨horder, hsealed, hactive⟩ := hinv
  -- Split on the kind of step.
  cases hstep with
  -- An append.
  | append =>
    -- The earlier files are untouched; the order and the synced bound are left to show.
    refine ⟨?_, hsealed, ?_⟩
    -- Appending commit `next` extends `0, ..., next - 1` by `next`.
    ·
      -- Unfold "every commit" in the assumption and the goal.
      unfold closeRecords sealedRecords at horder ⊢
      -- Regroup the lists; the old ones are 0, ..., next - 1, and one more makes 0, ..., next.
      rw [← List.append_assoc, horder, List.range_succ]
    -- The synced prefix stays within the longer file.
    ·
      -- The file is one record longer.
      simp only [List.length_append, List.length_singleton]
      -- The synced count was within the shorter file: arithmetic.
      omega
  -- A sync: the records do not change, and the newest file is now fully synced.
  | sync => exact ⟨horder, hsealed, Nat.le_refl _⟩
  -- A rotation.
  | rotate =>
    -- The new newest file is empty with nothing synced; the order and the earlier files are left.
    refine ⟨?_, ?_, Nat.le_refl 0⟩
    -- The sealed file's records move to the earlier files unchanged.
    ·
      -- Unfold "every commit" in the assumption and the goal.
      unfold closeRecords sealedRecords at horder ⊢
      -- Join the lists: nothing moved, nothing was added.
      simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_append,
        List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] at horder ⊢
      -- That is the same list as before.
      exact horder
    -- The new earlier file was synced by the rotation; the older ones already were.
    ·
      -- Take an earlier file after the step.
      intro f hf
      -- It is an older one, or the one just sealed.
      rcases List.mem_append.mp hf with hold | hnew
      -- An older one was fully synced already.
      · exact hsealed f hold
      -- The one just sealed:
      · rcases List.mem_singleton.mp hnew with rfl
        -- the rotation set its synced count to its length.
        rfl
  -- A flush of the oldest earlier file.
  | flush f rest holdest =>
    -- The newest file is untouched; the order and the remaining earlier files are left.
    refine ⟨?_, ?_, hactive⟩
    -- The flushed file's commits move from the earlier files to the tables, in place.
    ·
      -- Unfold "every commit", and name the earlier files as the oldest one and the rest.
      unfold closeRecords sealedRecords at horder ⊢
      -- Write the earlier files as `f :: rest` in the assumption.
      rw [holdest] at horder
      -- Join the lists: the same commits in the same order.
      simp only [List.map_cons, List.flatten_cons, List.append_assoc] at horder ⊢
      -- That is the assumption.
      exact horder
    -- Every remaining earlier file was one before, so it is fully synced.
    ·
      -- Take a remaining earlier file.
      intro g hg
      -- It was among the earlier files, which were `f :: rest`.
      exact hsealed g (holdest ▸ List.mem_cons_of_mem f hg)
  -- The seal in place changes only the flag.
  | sealInPlace => exact ⟨horder, hsealed, hactive⟩
  -- The flush of the memtable sealed in place.
  | flushInPlace hin hnone =>
    -- No earlier file is left, and the newest is empty; only the order is left to show.
    refine ⟨?_, ?_, Nat.le_refl 0⟩
    -- The newest file's commits move to the tables, in place.
    ·
      -- Unfold "every commit" in the assumption and the goal.
      unfold closeRecords sealedRecords at horder ⊢
      -- There is no earlier file.
      rw [hnone] at horder ⊢
      -- Join the lists: the same commits in the same order.
      simp only [List.map_nil, List.flatten_nil, List.append_nil] at horder ⊢
      -- That is the assumption.
      exact horder
    -- There is no earlier file, so the claim about them holds for lack of a case.
    ·
      -- Take an earlier file after the step: there are none.
      intro g hg
      -- The earlier files are the empty list.
      rw [hnone] at hg
      -- Nothing is in the empty list.
      exact absurd hg List.not_mem_nil

/-- Every state the engine reaches satisfies the invariant. -/
theorem close_reachable_inv {w : CloseWal} (hreach : CloseSteps closeInit w) : CloseInv w := by
  -- Go through the steps one at a time.
  induction hreach with
  -- No step: the start satisfies the invariant.
  | refl => exact close_init_inv
  -- Some steps, then one more: the invariant held before the last step, and a step keeps it.
  | tail _ hstep ih => exact close_step_inv ih hstep

/-- What recovery yields after a power cut: the tables' commits, then
what replay of the files yields, or `none` when replay refuses. -/
def recoverClose (w : CloseWal) (cs : List (LogFile × Cut)) (c : Cut) : Option (List Nat) :=
  -- Replay the earlier files with their cuts and the newest file with its cut, after the tables.
  (replay cs (w.active, c)).map (w.tables ++ ·)

/-- **Recovery yields a gap-free prefix.** In any state the invariant holds
in, after any power cut, recovery opens and yields commits
`0, 1, ..., m - 1` for some `m` no larger than the number of commits, and
`m` covers every durable commit. -/
theorem close_recovers_prefix {w : CloseWal}
    -- The invariant holds.
    (hinv : CloseInv w)
    -- What the cut left of each earlier file, in order ...
    (cs : List (LogFile × Cut)) (hcs : cs.map Prod.fst = w.sealed)
    -- ... each something a cut may leave ...
    (hsurv : ∀ p ∈ cs, Survives p.1 p.2)
    -- ... and what it left of the newest file.
    (c : Cut) (hc : Survives w.active c) :
    -- The statement: recovery yields commits 0, ..., m - 1, with m at most the commits made and at
    -- least the durable ones.
    ∃ m, recoverClose w cs c = some (List.range m) ∧ m ≤ w.next ∧ closeDurable w ≤ m := by
  -- The order of the commits, and that every earlier file is fully synced.
  obtain ⟨horder, hsealed, -⟩ := hinv
  -- The newest file kept between its synced prefix and all of its records.
  obtain ⟨hlo, hhi, -⟩ := hc
  -- Every earlier file in the cut list is fully synced.
  have hsync : ∀ p ∈ cs, p.1.synced = p.1.records.length := by
    -- Take a file with its cut.
    intro p hp
    -- It is enough that the file is one of the earlier files.
    apply hsealed
    -- The files of the pairs are the earlier files.
    rw [← hcs]
    -- And p is one of the pairs.
    exact List.mem_map_of_mem hp
  -- Unfold what recovery yields.
  unfold recoverClose
  -- Replay yields every earlier file's records, then what survived of the newest file.
  rw [replay_synced cs hsync hsurv, hcs]
  -- Put the tables in front of that.
  simp only [Option.map_some]
  -- Regroup: the tables and the earlier files first, then the newest file's kept records.
  rw [← List.append_assoc]
  -- Name the tables' and the earlier files' commits together `G`.
  generalize hG : w.tables ++ (w.sealed.map LogFile.records).flatten = G
  -- Unfold "every commit" in the order fact.
  unfold closeRecords sealedRecords at horder
  -- Write it with G: `G` followed by the newest file's records is `0, ..., next - 1`.
  rw [hG] at horder
  -- Counting: G and the newest file make `next`.
  have hlen : G.length + w.active.records.length = w.next := by
    -- Equal lists have equal lengths.
    have := congrArg List.length horder
    -- Compute both lengths.
    simpa using this
  -- G's length is the tables' plus the earlier files'.
  have hGlen : G.length = w.tables.length + (sealedRecords w).length := by
    -- G is the two joined.
    rw [← hG]
    -- The length of a join is the sum of the lengths.
    simp [sealedRecords]
  -- The kept count is all of G and the newest file's kept records.
  refine ⟨G.length + c.kept, ?_, by omega, ?_⟩
  -- G followed by `kept` records of the newest file is the first G.length + kept of all, a range.
  ·
    -- The claim, as an equation between lists.
    have htake : G ++ w.active.records.take c.kept =
        (G ++ w.active.records).take (G.length + c.kept) := by
      -- Split "the first n of a joined list"; the first part, G, is taken whole.
      rw [List.take_append, List.take_of_length_le (l := G) (i := G.length + c.kept) (by omega)]
      -- What is left over for the newest file is `kept`.
      simp
    -- So recovery yields the first G.length + kept of `0, ..., next - 1`, which is a range.
    simp only [htake, horder, List.take_range]
    -- Both sides are ranges from 0; compare their lengths.
    congr 2
    -- Arithmetic.
    omega
  -- Everything durable survived: the tables and earlier files whole, and the synced prefix.
  ·
    -- Unfold "durable".
    unfold closeDurable
    -- The synced count is at most `kept`: arithmetic with G's length.
    omega

/-- **For every reachable state.** -/
theorem close_reachable_recovers_prefix {w : CloseWal}
    -- `w` is reachable from the start.
    (hreach : CloseSteps closeInit w)
    -- (what the cut left of each earlier file,
    (cs : List (LogFile × Cut)) (hcs : cs.map Prod.fst = w.sealed)
    -- each something a cut may leave,
    (hsurv : ∀ p ∈ cs, Survives p.1 p.2)
    -- and what it left of the newest file)
    (c : Cut) (hc : Survives w.active c) :
    -- The statement: recovery yields a gap-free prefix covering every durable commit.
    ∃ m, recoverClose w cs c = some (List.range m) ∧ m ≤ w.next ∧ closeDurable w ≤ m :=
  -- A reachable state satisfies the invariant, and the theorem above applies.
  close_recovers_prefix (close_reachable_inv hreach) cs hcs hsurv c hc

/-! ### The RED case: the next log created before the flush is durable -/

/-- The defective close: it seals in place but creates the next log at
once, so the unsynced newest file becomes an earlier one before its
flush is durable. -/
inductive StepNewLogFirst : CloseWal → CloseWal → Prop
  /-- As `CloseStep.append`. -/
  | append (w : CloseWal) :
      -- The newest file gains the record of commit `next`,
      StepNewLogFirst w { w with active := { w.active with records := w.active.records ++ [w.next] },
                                 -- and the next commit number moves up.
                                 next := w.next + 1 }
  /-- The defect: the newest file joins the earlier ones as it is, synced
  or not, and the next, empty file becomes the newest. -/
  | newLogFirst (w : CloseWal) :
      -- The unsynced file is now an earlier one, and an empty file is the newest.
      StepNewLogFirst w { w with sealed := w.sealed ++ [w.active], active := ⟨[], 0⟩ }

/-- Any number of defective steps. -/
inductive StepsNewLogFirst : CloseWal → CloseWal → Prop
  /-- No step at all. -/
  | refl (w : CloseWal) : StepsNewLogFirst w w
  /-- Some steps, then one more. -/
  | tail {u v w : CloseWal} : StepsNewLogFirst u v → StepNewLogFirst v w → StepsNewLogFirst u w

/-- Commits 0 and 1 in an earlier file nothing synced, and an empty newest file. -/
def newLogFirst : CloseWal := ⟨[], [⟨[0, 1], 0⟩], ⟨[], 0⟩, 2, false⟩

/-- **`new_log_first_breaks_recovery`.** The defective close reaches
`newLogFirst` from the start: two appends, then the next log before the
flush. A power cut that keeps commit 0 and half of commit 1 in that file
leaves a torn record in a file that is not the newest, and recovery
refuses. -/
theorem new_log_first_breaks_recovery :
    -- The defective close reaches the state;
    StepsNewLogFirst closeInit newLogFirst ∧
    -- the torn cut is one a power cut may leave of the unsynced file;
    Survives ⟨[0, 1], 0⟩ ⟨1, true⟩ ∧
    -- the empty newest file keeps nothing, which a power cut may leave;
    Survives ⟨[], 0⟩ ⟨0, false⟩ ∧
    -- and recovery refuses.
    recoverClose newLogFirst [(⟨[0, 1], 0⟩, ⟨1, true⟩)] ⟨0, false⟩ = none := by
  -- Four parts; the last is computed.
  refine ⟨?_, ?_, ?_, by decide⟩
  -- From the start: append, append, the next log first.
  ·
    -- The three defective steps, in order.
    exact .tail (.tail (.tail (.refl _) (.append _)) (.append _)) (.newLogFirst _)
  -- Nothing synced, one of two records kept, a torn second one.
  ·
    -- The three bounds of "may be left by a power cut", each computed.
    exact ⟨by decide, by decide, fun _ => by decide⟩
  -- Nothing synced, nothing kept, nothing torn.
  ·
    -- The three bounds, each computed; "torn" is false, so its bound holds for lack of a case.
    exact ⟨by decide, by decide, fun h => absurd h (by decide)⟩

-- The end of the names that start with Regolith.WalClose.
end Regolith.WalClose
