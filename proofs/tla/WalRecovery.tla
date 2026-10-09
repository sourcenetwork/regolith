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
\* THE ENGINE (format 2, src/engine/wal.rs, wal_frame.rs, wal_replay.rs,
\* recovery.rs).
\*   AppendRecord   Wal::append_group: one record per commit group, its
\*                  header carrying `synced_through`, the offset the last
\*                  completed Wal::sync_data covered (record i's `st`).
\*   Sync(k)        Wal::sync_data: `synced_through` moves, once the sync
\*                  returns, to the offset it began at.
\*   AppendClose    Wal::close: sync, append CLOSE, sync; the engine's
\*                  close calls it, and nothing is appended after CLOSE.
\*   Rotate         RegolithEngine::swap_wal (WalRotation.tla).
\*   Crash          WalReplayIter reads P from every usable record
\*                  (wal_frame::proof_past scans past the damage), refuses
\*                  when O < P, and otherwise ends the log at O; recovery
\*                  then truncates the log at O and syncs it
\*                  (wal::truncate_durably) before the next log is created,
\*                  and reports the drop.
\* Format 1 logs written by 0.1.x are still read by the format 1 rule
\* (RED Format1): a whole record with a bad checksum is refused unless
\* every byte after it is zero, and a record the file ends inside is a
\* torn tail.
\*
\* THE STAMP UNDER CHECKSUMS. The engine writes a log's stamp when it
\* creates the log and makes it durable with the log's first sync, not
\* with a sync of its own. A crash before that first sync (synced = 0
\* here) can lose the stamp, and replay then keeps nothing of the log and
\* reports every byte it held: the outcome of the crash state in which
\* every record is unusable, which CrashStates holds whenever synced = 0.
\* Every invariant below is checked against that outcome, so the model
\* needs no state of its own for it.
\*
\* THE ENGINE UNDER AEAD (Frame = "AEAD"; src/engine/wal_seal.rs, with
\* Options::key_provider set).
\*   Usable         a sealed record is usable when its header check holds
\*                  and its AES-256-GCM-SIV tag verifies under the key the
\*                  stamp names (wal_seal::open_record); the tag's
\*                  associated data is the header check's input, so it
\*                  binds the payload to `st`, the offset and the log. The
\*                  scan past damage (wal_frame::proof_past) reads P only
\*                  from records whose tag verifies.
\*   StampKeyOk     the stamp is sealed under the log's key: a stamp whose
\*                  tag fails refuses the open, naming the file
\*                  (wal_seal::open_stamp), so a wrong key refuses and
\*                  never drops the log (WrongKeyRefuses; RED
\*                  StampNotSealed).
\*   NewestStampOk  and it is whole: the engine writes the sealed stamp to
\*                  a staging file, syncs it, renames it into place and
\*                  syncs the directory (wal_seal::create_durably) before
\*                  the log takes a record, which is the model's Init and
\*                  Rotate creating a log whose stamp is already synced. A
\*                  crash leaves no log, or one whose whole stamp is
\*                  durable (RED StampUnsynced).
\*   keyOk = FALSE  a provider handing other bytes under the key id the
\*                  stamp names; a key id it does not provide at all is
\*                  refused before any tag is checked (Error::UnknownKey).
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
\*     damaged header"). Without the seal, a wrong key fails every record,
\*     P is 0, and replay would drop the whole log as a torn tail
\*     (RED StampNotSealed). Without the sync at creation, a power cut
\*     before the log's first sync can tear the stamp, and since a torn
\*     sealed stamp cannot be told from a wrong key, the open refuses a
\*     crash it must survive (RED StampUnsynced).
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
\*   MC_WalRecovery_Red_StampUnsynced        RecoveryOpens fails

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
                   "CloseWithoutSync", "NoTruncate", "StampNotSealed",
                   "StampUnsynced"}

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
\*   st         [1..Len(log) -> state] of each record: "intact", "garbage",
\*              "zero", "partial" (the file ends inside it) or "absent";
\*   keyOk      whether the key provider returned the key the log was
\*              sealed under (always TRUE with checksums);
\*   rot        whether the last synced group was damaged (Residual only);
\*   stampTorn  whether the crash tore the newest log's stamp (only the
\*              StampUnsynced defect can, see StampTears).

\* What an unsynced record may become. Format 2 treats every unusable
\* record alike, so one kind suffices; format 1 tells zeros and a partial
\* record from garbage.
UnsyncedKinds ==
  \* Format 1 must tell four shapes apart, so its defect gets all four.
  IF Mutant = "Format1" THEN {"intact", "garbage", "zero", "partial"}
  \* Format 2 only asks "usable or not", so two shapes cover every case.
  ELSE {"intact", "garbage"}

\* Whether a crash can tear the newest log's stamp. The engine writes a
\* sealed stamp to a staging file, syncs it, and only then renames it to
\* the log's name (src/engine/wal_seal.rs, create_durably): after a power
\* cut the log either does not exist or carries its whole stamp, so there
\* is nothing to tear. The StampUnsynced defect writes the stamp in place
\* and lets the first record's sync carry it, the way an unsealed log does;
\* until that sync (synced = 0) a power cut may leave half a stamp.
StampTears ==
  \* Only the defect, only with sealed frames, only before the first sync.
  IF Frame = "AEAD" /\ Mutant = "StampUnsynced" /\ synced = 0
    \* Then the stamp may come back torn or whole.
    THEN BOOLEAN
    \* Otherwise it always comes back whole.
    ELSE {FALSE}

\* Every crash state at this moment. L is how many records the file keeps
\* (never fewer than the synced prefix); records past the synced prefix and
\* up to L each take an unsynced kind, a partial record only as the last;
\* the rest are absent.
CrashStates ==
  \* n: how many records the newest log held when the power went.
  LET n == Len(log) IN
  \* Collect one crash state for every combination of the choices below.
  UNION {
    \* One crash state: what became of each record, the key, rot, the stamp.
    {[st |-> [i \in 1..n |->
               \* A synced record survives, but for rot in the last synced one.
               IF i <= synced THEN (IF rot /\ i = synced THEN "garbage" ELSE "intact")
               \* An unsynced record still in the file takes its chosen kind.
               ELSE IF i <= L THEN f[i] ELSE "absent"],
      \* Whether the reopen comes with the right key.
      keyOk |-> key,
      \* Whether the last synced record rotted.
      rot |-> rot,
      \* Whether the stamp came back torn.
      stampTorn |-> torn] :
       \* f picks a kind for each unsynced record the file still holds...
       f \in {g \in [(synced + 1)..L -> UnsyncedKinds] :
                \* ...and only the last of them may be cut short.
                \A i \in (synced + 1)..L : g[i] = "partial" => i = L}} :
    \* The file keeps at least the synced prefix and at most every record.
    L \in synced..n,
    \* With sealed frames the reopen may come with the wrong key.
    key \in (IF Frame = "AEAD" THEN BOOLEAN ELSE {TRUE}),
    \* Rot only in the Residual configurations, and only of a synced record.
    rot \in (IF Residual /\ synced > 0 THEN BOOLEAN ELSE {FALSE}),
    \* A torn stamp only under the defect.
    torn \in StampTears}

\* How many records the crash left in the file: they are a prefix.
PLen(cs) == Cardinality({i \in DOMAIN cs.st : cs.st[i] # "absent"})

\* A record is usable when its bytes survived and its check verifies.
\* Under AEAD the tag is the check: the engine opens the record's sealed
\* payload under the key the stamp names (wal_seal::open_record), and a
\* wrong key fails every tag exactly as damage fails it.
Usable(cs, i) ==
  \* The bytes are the ones the writer wrote...
  /\ cs.st[i] = "intact"
  \* ...and, with sealed frames, the key is the one that sealed them.
  /\ (Frame = "Checksum" \/ cs.keyOk)

\* The key half of a stamp's check: a sealed stamp's tag holds only under
\* the key that sealed it (wal_seal::open_stamp).
StampKeyOk(cs) ==
  \* A checksummed log has no key to get wrong.
  \/ Frame = "Checksum"
  \* A sealed stamp opened under the right key.
  \/ cs.keyOk
  \* The StampNotSealed defect: a stamp nobody sealed passes under any key.
  \/ Mutant = "StampNotSealed"

\* The newest log's stamp verifies: right key, and every byte there. An
\* earlier log was synced whole before the next one existed, so only the
\* newest log's stamp can be torn.
NewestStampOk(cs) ==
  \* The key half, as for every log.
  /\ StampKeyOk(cs)
  \* And the stamp is whole: a torn sealed stamp cannot be told from one
  \* under another key, so it refuses like a wrong key.
  /\ ~cs.stampTorn

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

\* Replay refuses the newest log. The design refuses a stamp that fails,
\* and an unusable record below P. A record whose tag fails is unusable
\* like any damaged one, so in the tail above P it is dropped and
\* reported, and below P it refuses. Each mutant changes this rule as named.
RefusedNewest(cs) ==
  \* A stamp that fails refuses the open, naming the file.
  \/ ~NewestStampOk(cs)
  \* Then the O < P rule, or the defect that replaces it.
  \/ CASE Mutant = "DropBelowP"   -> FALSE
       [] Mutant = "RefuseAboveP" -> Bad(cs) # {}
       [] Mutant = "Format1"      -> Format1Refuses(cs)
       [] OTHER                   -> Bad(cs) # {} /\ O(cs) <= P(cs)

\* Replay refuses an earlier log: they are complete, so any unusable
\* record there, or a stamp that fails, is damage.
RefusedSealed(cs) ==
  \* Some earlier log j...
  \E j \in 1..Len(sealed) :
    \* ...whose stamp fails under this key...
    \/ ~StampKeyOk(cs)
    \* ...or that holds a record that is not usable: rot, or a failed tag.
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
\* leaves a database that refuses to open. It rules out, say, a power cut
\* just after a rotation created log 2: reopened with the right key, the
\* database must open, whatever state log 2's records are in. Lean:
\* recovers_prefix2, and sealed_stamp_opens_after_honest_crash with its
\* RED unsynced_stamp_refuses_honest_crash.
RecoveryOpens ==
  \* Every crash state...
  \A cs \in CrashStates :
    \* ...reopened with the right key, with no rot in the synced prefix...
    cs.keyOk /\ ~cs.rot
      \* ...opens.
      => ~Refused(cs)

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
\* It rules out a provider that hands back other bytes under the right key
\* id and a database that opens empty because every tag failed. Lean:
\* wrong_key_refuses and wrong_key_refuses_sealed, and
\* unsealed_stamp_drops_log for the RED.
WrongKeyRefuses ==
  \* Every crash state reopened under the wrong key...
  \A cs \in CrashStates : ~cs.keyOk
    \* ...refuses to open.
    => Refused(cs)

====
