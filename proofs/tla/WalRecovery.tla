---- MODULE WalRecovery ----
\* 4.2 and 4.3: crash-aware WAL recovery with format 2. Every group record
\* carries `synced_through`, the end of what the last completed sync made
\* durable; a clean close syncs, appends CLOSE and syncs again. Replay of
\* the newest log takes P, the largest `synced_through` it reads (end of
\* file when a usable CLOSE ends the file), and at the first unusable
\* record, at O, refuses when O < P and otherwise drops [O, end of file),
\* truncates, and reports it. Earlier logs are complete by the rotation sync
\* (WalRotation.tla), so damage there is refused. With encryption at rest
\* (4.12, D45) the AEAD tag replaces the checksum: a record whose tag fails
\* is an unusable record under the same rule.
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/WalRecovery.lean
\* (the "Format 2" part):
\*   replay2_opens_of_honest     replay opens when every surviving stamp is
\*                               honest: what it claims synced survived
\*   replay2_keeps_proven        an open never discards a record a surviving
\*                               stamp proves synced
\*   step2_inv, reachable2_inv   the format 2 writer keeps every stamp at or
\*                               below the completed sync, and CLOSE only
\*                               after a sync of everything before it
\*   honest_of_inv               so after a crash the flush honoured, P is
\*                               at most O
\*   recovers_prefix2            after any crash the device's flush honoured,
\*                               recovery opens with a gap-free prefix that
\*                               keeps every synced commit
\*   residual_is_reported        a crash that damaged synced bytes and still
\*                               opens has discarded a nonempty tail
\*   wrong_key_refuses           a stamp that fails its tag refuses
\*   drop_below_p_loses_proven, refuse_above_p_never_opens,
\*   format1_refuses_torn_tail, unsealed_stamp_drops_log
\*                               the RED cases, as counterexamples
\* TLC checks the same invariants here over every interleaving of appends,
\* syncs, rotations, a clean close and a crash with recovery, against every
\* crash state at every reachable state.
\*
\* THE ENGINE TODAY (format 1). Wal::append, Wal::sync_data and
\* WalReplayIter (src/engine/wal.rs, wal_replay.rs): a whole record with a
\* bad checksum is refused unless every byte after it is zero, and a record
\* the file ends inside is a torn tail (E3). Plan 4.2 replaces that with the
\* rule above; this model specifies it before the code.
\*
\* WHAT A CRASH LEAVES (the crash states, `CrashStates`).
\*   - Under powersafe overwrite (D6: assumed, synced groups are not padded
\*     to whole sectors), every record a completed sync covered survives.
\*   - Each record past the synced prefix independently survives intact, or
\*     is unusable (garbage; a block of zeros where the length persisted
\*     before the data, which format 1 tells apart), and the file may end
\*     after any of them, inside the last one (a partial record) or not.
\*     Persistence out of order is allowed: ext4 data=writeback, volatile
\*     device caches and the OPFS slot header all produce it (E3).
\*   - Residual = TRUE adds the residual case of 4.2 item 5: the last synced
\*     group is damaged (bit rot, or a torn write rewriting a sector that
\*     held acknowledged bytes). It must be reported, never silent.
\*   - Frame = "AEAD" adds an open under the wrong key: every tag fails.
\*
\* PROMISES (4.2 item 5).
\*   Immediate: an acknowledged commit survives any crash the device's
\*     flush honours (AckedSurvive).
\*   Eventual: recovery is a gap-free prefix of commit order (NoGap).
\*   Both: every commit a completed sync covered survives (KeepsSynced); a
\*     record a surviving stamp proves synced is never discarded
\*     (NoProvenLoss); a loss of synced data is refused or reported
\*     (LossIsReported); a wrong key never opens (WrongKeyRefuses).
\*
\* DESIGN CHOICES where the plan leaves room (recorded in the report):
\*   - P is read from every usable record in the file, including those
\*     after O. Read only from the records before O it could never exceed
\*     O (a record's stamp covers only bytes written before it), and the
\*     refusal would never fire. Format 2 framing must therefore find the
\*     records after a damaged one without trusting its length (for
\*     example fixed-size blocks); the model assumes it does.
\*   - A clean close syncs every record BEFORE it appends CLOSE. Otherwise
\*     a crash can keep CLOSE (P = end of file) and lose an unsynced record
\*     before it, and replay refuses a crash it should survive
\*     (RED CloseWithoutSync).
\*   - The truncation of a dropped tail is synced before the next log is
\*     created, so the truncated log is complete when it becomes an earlier
\*     log (RED NoTruncate shows why).
\*   - With AEAD, the stamp at the head of each log is sealed under the key
\*     and synced when the log is created, so it is always inside the
\*     synced prefix: a stamp whose tag fails is refused ("wrong key or
\*     damaged header"). Without that, a wrong key fails every record, P is
\*     0, and replay would drop the whole log as a torn tail
\*     (RED StampNotSealed).
\*   - A group of commits is one record here, so it holds one commit; a
\*     group of several survives or is lost whole, like one commit.
\*
\* CONFIGURATIONS.
\*   MC_WalRecovery_Green_Immediate          every invariant holds
\*   MC_WalRecovery_Green_Eventual           every invariant holds
\*   MC_WalRecovery_Green_Residual           damage in the last synced group
\*                                           is refused or reported
\*   MC_WalRecovery_Green_Aead               AEAD frames and a wrong key
\*   MC_WalRecovery_Red_DropBelowP           NoProvenLoss fails
\*   MC_WalRecovery_Red_RefuseAboveP         RecoveryOpens fails
\*   MC_WalRecovery_Red_Format1              RecoveryOpens fails
\*   MC_WalRecovery_Red_CloseWithoutSync     RecoveryOpens fails
\*   MC_WalRecovery_Red_NoTruncate           RecoveryOpens fails
\*   MC_WalRecovery_Red_StampNotSealed       AckedSurvive fails

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  MaxCommits,  \* the most commits the model appends, across crashes
  MaxFiles,    \* the most log files: earlier logs plus the newest
  MaxCrashes,  \* how many crashes with recovery the model performs
  Mode,        \* "Immediate" or "Eventual": DurabilityMode
  Frame,       \* "Checksum" or "AEAD": what makes a record usable
  Residual,    \* TRUE: crash states may damage the last synced group
  Mutant       \* "none" (the design) or one defect, named in the header

ASSUME MaxCommits \in Nat /\ MaxFiles \in Nat \ {0} /\ MaxCrashes \in Nat
ASSUME Mode \in {"Immediate", "Eventual"}
ASSUME Frame \in {"Checksum", "AEAD"}
ASSUME Residual \in BOOLEAN
ASSUME Mutant \in {"none", "DropBelowP", "RefuseAboveP", "Format1",
                   "CloseWithoutSync", "NoTruncate", "StampNotSealed"}

VARIABLES
  sealed,   \* the earlier logs, oldest first; each a sequence of records
            \* [c, st, ok]: commit (0 for CLOSE), stamp, and whether the
            \* bytes are usable (FALSE only for an untruncated dropped tail)
  log,      \* the newest log: a sequence of records [c, st] as written
  synced,   \* how many leading records of `log` a completed sync covered
  closed,   \* whether CLOSE has been appended to `log`
  next,     \* the last commit number appended (commits are 1, 2, ...)
  crashes   \* how many crashes with recovery have happened

\* Every variable, so a step that changes none of them is a stutter.
vars == <<sealed, log, synced, closed, next, crashes>>

----------------------------------------------------------------------------
\* Helpers.

\* The least and greatest elements of a finite, nonempty set of naturals.
Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max(S) == CHOOSE x \in S : \A y \in S : y <= x

\* The set of elements of a sequence.
Range(s) == {s[i] : i \in 1..Len(s)}

\* The commit numbers of a sequence of records, in order; CLOSE has none.
RECURSIVE CommitsOf(_)
CommitsOf(recs) ==
  IF recs = <<>> THEN <<>>
  ELSE (IF Head(recs).c = 0 THEN <<>> ELSE <<Head(recs).c>>) \o CommitsOf(Tail(recs))

\* The commits of the earlier logs, oldest first.
RECURSIVE SealedFrom(_)
SealedFrom(j) == IF j > Len(sealed) THEN <<>> ELSE CommitsOf(sealed[j]) \o SealedFrom(j + 1)
SealedCommits == SealedFrom(1)

\* A gap-free prefix of commit order: commits 1, 2, ..., n.
IsPrefix(s) == s = [i \in 1..Len(s) |-> i]

\* The commits a completed sync made durable: every earlier log (synced at
\* rotation or at the truncation after a crash) and the synced prefix.
SyncedCommits == Range(SealedCommits) \cup Range(CommitsOf(SubSeq(log, 1, synced)))

\* The commits acknowledged to their callers. Immediate acknowledges a
\* commit once a completed sync covers it; Eventual when it is appended.
Acked ==
  IF Mode = "Immediate" THEN SyncedCommits
  ELSE Range(SealedCommits) \cup Range(CommitsOf(log))

----------------------------------------------------------------------------
\* Crash states of the newest log. A crash state is a record:
\*   st     [1..Len(log) -> state] of each record: "intact", "garbage",
\*          "zero", "partial" (the file ends inside it) or "absent";
\*   keyOk  whether the key provider returned the key the log was sealed
\*          under (always TRUE with checksums);
\*   rot    whether the last synced group was damaged (Residual only).

\* What an unsynced record may become. Format 2 treats every unusable
\* record alike, so one kind suffices; format 1 tells zeros and a partial
\* record from garbage.
UnsyncedKinds ==
  IF Mutant = "Format1" THEN {"intact", "garbage", "zero", "partial"}
  ELSE {"intact", "garbage"}

\* Every crash state at this moment. L is how many records the file keeps
\* (never fewer than the synced prefix); records past the synced prefix and
\* up to L each take an unsynced kind, a partial record only as the last;
\* the rest are absent.
CrashStates ==
  LET n == Len(log) IN
  UNION {
    {[st |-> [i \in 1..n |->
               IF i <= synced THEN (IF rot /\ i = synced THEN "garbage" ELSE "intact")
               ELSE IF i <= L THEN f[i] ELSE "absent"],
      keyOk |-> key, rot |-> rot] :
       f \in {g \in [(synced + 1)..L -> UnsyncedKinds] :
                \A i \in (synced + 1)..L : g[i] = "partial" => i = L}} :
    L \in synced..n,
    key \in (IF Frame = "AEAD" THEN BOOLEAN ELSE {TRUE}),
    rot \in (IF Residual /\ synced > 0 THEN BOOLEAN ELSE {FALSE})}

\* How many records the crash left in the file: they are a prefix.
PLen(cs) == Cardinality({i \in DOMAIN cs.st : cs.st[i] # "absent"})

\* A record is usable when its bytes survived and its checksum or tag
\* verifies; a tag verifies only under the right key.
Usable(cs, i) == cs.st[i] = "intact" /\ (Frame = "Checksum" \/ cs.keyOk)

\* The stamp at the head of each log verifies. It is synced when the log is
\* created, so it survives every crash; with AEAD it is sealed under the
\* key, so a wrong key fails it. The mutant leaves it unsealed.
StampOk(cs) == Frame = "Checksum" \/ cs.keyOk \/ Mutant = "StampNotSealed"

\* The present records that are not usable.
Bad(cs) == {i \in 1..PLen(cs) : ~Usable(cs, i)}

\* O: the position of the first unusable record, or one past the end.
O(cs) == IF Bad(cs) = {} THEN PLen(cs) + 1 ELSE Min(Bad(cs))

\* P: how many leading records some usable record proves synced. Each
\* usable record's stamp counts; a usable CLOSE counts the whole file. In
\* offsets, record O starts below P exactly when O <= P here.
P(cs) ==
  Max({0} \cup {log[i].st : i \in {j \in 1..PLen(cs) : Usable(cs, j)}}
          \cup {i \in 1..PLen(cs) : Usable(cs, i) /\ log[i].c = 0})

\* Format 1's rule on the first damaged record: a partial record, or a
\* zero record followed only by zeros, ends the log; anything else refuses.
Format1Refuses(cs) ==
  /\ Bad(cs) # {}
  /\ cs.st[O(cs)] # "partial"
  /\ ~(\A j \in O(cs)..PLen(cs) : cs.st[j] = "zero")

\* Replay refuses the newest log. The design refuses a bad stamp, and an
\* unusable record below P. Each mutant changes this rule as named.
RefusedNewest(cs) ==
  \/ ~StampOk(cs)
  \/ CASE Mutant = "DropBelowP"   -> FALSE
       [] Mutant = "RefuseAboveP" -> Bad(cs) # {}
       [] Mutant = "Format1"      -> Format1Refuses(cs)
       [] OTHER                   -> Bad(cs) # {} /\ O(cs) <= P(cs)

\* Replay refuses an earlier log: they are complete, so any unusable
\* record there, or a stamp that fails, is damage.
RefusedSealed(cs) ==
  \E j \in 1..Len(sealed) :
    \/ ~StampOk(cs)
    \/ \E i \in 1..Len(sealed[j]) : ~(sealed[j][i].ok /\ (Frame = "Checksum" \/ cs.keyOk))

\* Recovery refuses to open.
Refused(cs) == RefusedSealed(cs) \/ RefusedNewest(cs)

\* What recovery yields when it opens: every earlier log's commits, then
\* the newest log's records before O.
Recovered(cs) == SealedCommits \o CommitsOf(SubSeq(log, 1, O(cs) - 1))

\* Recovery reports a discarded tail: it dropped bytes the file holds,
\* which is a warn line, two tickers and an EventListener callback.
Discarded(cs) == O(cs) <= PLen(cs)

----------------------------------------------------------------------------
\* Actions.

\* The start: no earlier log, an empty newest log whose stamp is synced.
Init ==
  /\ sealed  = <<>>
  /\ log     = <<>>
  /\ synced  = 0
  /\ closed  = FALSE
  /\ next    = 0
  /\ crashes = 0

\* A commit group appends its record, stamped with the completed sync.
AppendRecord ==
  /\ ~closed
  /\ next < MaxCommits
  /\ log'  = Append(log, [c |-> next + 1, st |-> synced])
  /\ next' = next + 1
  /\ UNCHANGED <<sealed, synced, closed, crashes>>

\* A sync that began when k records were written completes: they are
\* durable. Records appended while it ran keep the older stamp.
Sync(k) ==
  /\ synced < k /\ k <= Len(log)
  /\ synced' = k
  /\ UNCHANGED <<sealed, log, closed, next, crashes>>

\* Rotation (E2, WalRotation.tla): the newest log is synced, sealed, and a
\* new log with a synced stamp takes the next record.
Rotate ==
  /\ ~closed
  /\ log # <<>>
  /\ Len(sealed) + 1 < MaxFiles
  /\ sealed' = Append(sealed, [i \in 1..Len(log) |-> [c |-> log[i].c, st |-> log[i].st, ok |-> TRUE]])
  /\ log'    = <<>>
  /\ synced' = 0
  /\ UNCHANGED <<closed, next, crashes>>

\* A clean close appends CLOSE once every record is synced; a Sync then
\* makes CLOSE durable. The mutant appends it without the first sync.
\* Format 1 has no CLOSE.
AppendClose ==
  /\ ~closed
  /\ Mutant # "Format1"
  /\ synced = Len(log) \/ Mutant = "CloseWithoutSync"
  /\ log'    = Append(log, [c |-> 0, st |-> synced])
  /\ closed' = TRUE
  /\ UNCHANGED <<sealed, synced, next, crashes>>

\* A crash (or a reopen after a clean close) and a recovery that opens.
\* The newest log is truncated at O, synced, and becomes an earlier log;
\* a new log takes the next commit, numbered after the last recovered one.
\* The mutant NoTruncate leaves the dropped tail in the file.
Crash ==
  /\ crashes < MaxCrashes
  /\ Len(sealed) + 1 < MaxFiles
  /\ \E cs \in CrashStates :
       /\ ~Refused(cs)
       /\ sealed' = Append(sealed,
            IF Mutant = "NoTruncate"
              THEN [i \in 1..PLen(cs) |-> [c |-> log[i].c, st |-> log[i].st, ok |-> Usable(cs, i)]]
              ELSE [i \in 1..(O(cs) - 1) |-> [c |-> log[i].c, st |-> log[i].st, ok |-> TRUE]])
       /\ next' = Len(Recovered(cs))
  /\ log'     = <<>>
  /\ synced'  = 0
  /\ closed'  = FALSE
  /\ crashes' = crashes + 1

\* Every step the system can take.
Next ==
  \/ AppendRecord
  \/ \E k \in 1..(MaxCommits + 1) : Sync(k)
  \/ Rotate
  \/ AppendClose
  \/ Crash

\* Every behaviour: start in Init, then take Next steps or stutter.
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Invariants. Each quantifies over every crash state at this moment, so a
\* crash at every step of every behaviour is checked.

\* Every variable holds what its comment says.
TypeOK ==
  /\ Len(sealed) < MaxFiles
  /\ synced \in 0..Len(log)
  /\ closed \in BOOLEAN
  /\ next \in 0..MaxCommits
  /\ crashes \in 0..MaxCrashes

\* A crash the device's flush honoured, opened with the right key, never
\* leaves a database that refuses to open. Lean: recovers_prefix2.
RecoveryOpens == \A cs \in CrashStates : cs.keyOk /\ ~cs.rot => ~Refused(cs)

\* Whatever recovery yields when it opens is commits 1..n: the Eventual
\* promise, and true in every mode. Lean: recovers_prefix2.
NoGap == \A cs \in CrashStates : ~Refused(cs) => IsPrefix(Recovered(cs))

\* Every commit a completed sync covered survives a crash the flush
\* honoured. Lean: recovers_prefix2, its bound.
KeepsSynced ==
  \A cs \in CrashStates : ~Refused(cs) /\ ~cs.rot => SyncedCommits \subseteq Range(Recovered(cs))

\* THE IMMEDIATE PROMISE. Every acknowledged commit survives any crash the
\* device's flush honours. Lean: recovers_prefix2, since Immediate
\* acknowledges exactly the commits a completed sync covered.
AckedSurvive ==
  Mode = "Immediate" =>
    \A cs \in CrashStates : ~Refused(cs) /\ ~cs.rot => Acked \subseteq Range(Recovered(cs))

\* Replay never discards a record a surviving stamp proves synced: below P
\* it refuses instead. Lean: replay2_keeps_proven.
NoProvenLoss ==
  \A cs \in CrashStates : ~Refused(cs) =>
    \A i \in 1..P(cs) : log[i].c # 0 => log[i].c \in Range(Recovered(cs))

\* A recovery that opens without a synced commit has reported a discarded
\* tail: residual damage is never silent. Lean: residual_is_reported.
LossIsReported ==
  \A cs \in CrashStates :
    ~Refused(cs) /\ ~(SyncedCommits \subseteq Range(Recovered(cs))) => Discarded(cs)

\* An open under the wrong key refuses; it never drops the log as a tail.
\* Lean: wrong_key_refuses, and unsealed_stamp_drops_log for the RED.
WrongKeyRefuses == \A cs \in CrashStates : ~cs.keyOk => Refused(cs)

====
