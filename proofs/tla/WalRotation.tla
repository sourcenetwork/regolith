---- MODULE WalRotation ----
\* E2: WAL rotation. The log is a sequence of files; a power cut keeps the
\* synced prefix of each file plus an arbitrary prefix of its unsynced bytes,
\* and replay tolerates a torn tail only in the newest file.
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/WalRecovery.lean:
\*   step_inv, reachable_inv        a rotation that syncs first leaves every
\*                                  sealed file fully durable
\*   recovers_prefix,               after any power cut recovery succeeds
\*   reachable_recovers_prefix      with a gap-free prefix of commit order
\*                                  holding every durable record
\*   no_sync_breaks_recovery        the RED case, as a counterexample
\* TLC checks the same invariants here over every interleaving of appends,
\* syncs and rotations, against every power cut at every state.
\*
\* THE ENGINE.
\*   Wal::append / Wal::sync_data   src/engine/wal.rs
\*     A commit appends its record to the newest log file; a sync makes
\*     every record in that file durable.
\*   rotate_memtable                src/engine/mod.rs
\*     Seals the newest log file and opens the next one.
\*   WalReplayIter, WalPosition     src/engine/wal_replay.rs
\*     A torn record ends the newest file. In an earlier file it is damage,
\*     and recovery refuses to open.
\*
\* THE DEFECT (Rotation = "NoSync"). The sealed file is not synced before the
\* next file opens. A power cut can then tear a record in the sealed file,
\* which is no longer the newest, and recovery refuses; or cut the sealed
\* file at a record boundary while the newer file keeps its records, and
\* recovery yields later commits without the earlier ones: a gap.
\*
\* THE FIX (Rotation = "SyncFirst"). The rotation syncs the sealed file, and
\* only then opens the new file, so the new file takes a record only after
\* the sealed one is durable. The order matters even with no record in the
\* new file yet: replay ranks files by name, and an empty newer file makes an
\* unsynced sealed file an earlier one, whose torn tail it refuses.
\*
\* Commit numbers start at 1 here and at 0 in Lean; nothing else differs.
\*
\* CONFIGURATIONS.
\*   MC_WalRotation_Green           Rotation = "SyncFirst"
\*     RecoversPrefix and KeepsSynced hold.
\*   MC_WalRotation_Red_NoSync      Rotation = "NoSync"
\*     RecoversPrefix fails: the first break is a refusal.
\*   MC_WalRotation_Red_NoSync_Gap  Rotation = "NoSync"
\*     NoGap fails: a cut that keeps recovery open loses earlier commits.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  MaxRecords,  \* the most commits the model appends
  MaxFiles,    \* the most log files the model opens
  Rotation     \* "SyncFirst" (the fix) or "NoSync" (the defect)

ASSUME MaxRecords \in Nat /\ MaxFiles \in Nat \ {0}
ASSUME Rotation \in {"SyncFirst", "NoSync"}

VARIABLES
  files,   \* the log files, oldest first; each a sequence of commit numbers
  synced,  \* synced[i]: how many leading records of file i a sync made durable
  next     \* the number of commits appended so far

\* Every variable, so a step that changes none of them is a stutter.
vars == <<files, synced, next>>

\* The position of the newest file.
Last == Len(files)

\* The set of elements of a sequence.
Range(s) == {s[j] : j \in 1..Len(s)}

\* The start: one empty log file, nothing synced, no commit.
Init ==
  /\ files  = <<<<>>>>
  /\ synced = <<0>>
  /\ next   = 0

\* A commit appends its record, the next commit number, to the newest file.
AppendRecord ==
  /\ next < MaxRecords
  /\ files' = [files EXCEPT ![Last] = Append(@, next + 1)]
  /\ next'  = next + 1
  /\ UNCHANGED synced

\* A sync of the newest file makes every record in it durable.
Sync ==
  /\ synced[Last] < Len(files[Last])
  /\ synced' = [synced EXCEPT ![Last] = Len(files[Last])]
  /\ UNCHANGED <<files, next>>

\* A rotation seals the newest file and opens an empty one. The fix syncs
\* the sealed file first; the defect does not.
Rotate ==
  /\ Len(files) < MaxFiles
  /\ files[Last] # <<>>
  /\ files'  = Append(files, <<>>)
  /\ synced' = Append(IF Rotation = "SyncFirst"
                        THEN [synced EXCEPT ![Last] = Len(files[Last])]
                        ELSE synced,
                      0)
  /\ UNCHANGED next

\* Every step the system can take.
Next == AppendRecord \/ Sync \/ Rotate

\* Every behaviour: start in Init, then take Next steps or stutter.
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Power cuts and replay. A cut of one file is <<kept, torn>>: how many whole
\* records survive, and whether part of one more record follows them.

\* What a power cut may leave of file i: everything synced survives, at most
\* every record survives, and a torn record follows only if one was written.
CutsOf(i) ==
  {c \in (synced[i]..Len(files[i])) \X BOOLEAN : c[2] => c[1] < Len(files[i])}

\* Every power cut of the whole log: one cut per file.
Cuts ==
  {c \in [1..Len(files) -> UNION {CutsOf(i) : i \in 1..Len(files)}] :
     \A i \in 1..Len(files) : c[i] \in CutsOf(i)}

\* WalPosition::Earlier: replay refuses when a file other than the newest
\* ends in a torn record.
Refused(c) == \E i \in 1..(Len(files) - 1) : c[i][2]

\* The records replay yields from file i on, in file order. A torn tail
\* contributes nothing: it ends the newest file, and an earlier one refuses.
RECURSIVE Replayed(_, _)
Replayed(c, i) ==
  IF i > Len(files) THEN <<>>
  ELSE SubSeq(files[i], 1, c[i][1]) \o Replayed(c, i + 1)

\* A gap-free prefix of commit order: commits 1, 2, ..., n.
IsPrefix(s) == s = [j \in 1..Len(s) |-> j]

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ Len(files) \in 1..MaxFiles
  /\ Len(synced) = Len(files)
  /\ \A i \in 1..Len(files) : synced[i] \in 0..Len(files[i])
  /\ next \in 0..MaxRecords

\* Recovery opens after any power cut at this moment: no cut leaves a torn
\* record in a file other than the newest.
RecoveryOpens == \A c \in Cuts : ~Refused(c)

\* Whatever recovery yields when it opens is commits 1..n: no commit is
\* recovered without every commit before it.
NoGap == \A c \in Cuts : ~Refused(c) => IsPrefix(Replayed(c, 1))

\* THE HEADLINE. After a power cut at this moment, whatever it left of each
\* file, recovery succeeds and yields a gap-free prefix of commit order.
\* Lean: recovers_prefix.
RecoversPrefix == RecoveryOpens /\ NoGap

\* Recovery also keeps every record a sync made durable.
\* Lean: recovers_prefix, its bound durable w <= m.
KeepsSynced ==
  \A c \in Cuts : ~Refused(c) =>
    \A i \in 1..Len(files) : \A j \in 1..synced[i] : files[i][j] \in Range(Replayed(c, 1))

====
