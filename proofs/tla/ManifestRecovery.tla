---- MODULE ManifestRecovery ----
\* THE STORY.
\* The MANIFEST is regolith's list of which table files make up the database.
\* It is a log of "batches" appended one after another. Some batches only
\* reserve a file number; nobody waits for those to reach the disk. Others
\* add a table, and the writer waits (it "syncs") until such a batch is on
\* the disk before it does anything else. A power cut can mangle whatever was
\* written after the last finished sync, and nothing before it.
\*
\* Tiny example. A brand new database takes two writes, a = 1 and b = 2,
\* into its write-ahead log (the "log"). Then it flushes them into table
\* file 3: it reserves file numbers (two quick batches, never synced), writes
\* table 3, appends the batch "table 3 is in", and syncs. The power goes out
\* during that sync. On restart, the manifest's last three batches are
\* garbage, and table 3 sits in the table folder with nobody naming it.
\*
\* WHAT WENT WRONG BEFORE (E29). The open used to refuse that database: "the
\* manifest names no table, yet a table holds data". But a crash produces
\* exactly this state, and the log still holds a = 1 and b = 2, so refusing
\* lost nothing but the user's database. The fix judges the damaged end the
\* way a log's damaged end is judged: refuse only when a batch AFTER the
\* damage proves the damage was synced; otherwise drop the damaged bytes.
\*
\* WHAT WENT WRONG BEFORE (E30). After a flush, the engine deletes the log the
\* table now covers. If that delete failed, the log stayed, and the next open
\* replayed it into memory, where reads look first: a = 1 came back even
\* though a newer table said a = 5. The fix writes, in the same batch that
\* adds the table, "every log below this number is in tables" (min_wal_id),
\* and recovery skips those logs. A failed delete is reported and retried.
\*
\* WHAT THIS MODEL SHOWS. At every reachable state, for every way a power
\* cut can mangle the unsynced end of the manifest:
\*   RecoveryOpens  the open never refuses a state a crash produced;
\*   AckedSurvive   every acknowledged write comes back;
\*   ReadsNewest    reading memory first, then tables newest first, returns
\*                  the newest version that came back, for every key;
\*   RotSafe        and when the disk rots a synced batch (no crash does
\*                  that) and a later batch proves it was synced, the open
\*                  either refuses or loses nothing acknowledged.
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/ManifestRecovery.lean:
\*   crash_never_proves          no crash image carries a proof past its
\*                               first damage, so the open accepts it
\*                               (RecoveryOpens)
\*   replay_is_prefix,           the batches replay keeps are a prefix of
\*   replay_keeps_synced         those written, holding every synced one
\*                               (AckedSurvive's manifest half)
\*   replay_never_above_newer_table
\*                               with min_wal_id in the table's batch, every
\*                               replayed version is newer than every table's
\*                               version of its key (ReadsNewest)
\*   no_sync_before_next_refuses_a_crash, stale_without_min_wal
\*                               the RED cases, as counterexamples
\*
\* THE ENGINE, and the action that mirrors each part.
\*   Put            RegolithEngine::write path: a write lands in the active
\*                  memtable and its log, synced (Immediate durability).
\*   Seal           RegolithEngine::seal_active: reserve the next log's
\*                  number (SetNextFileId, unsynced) and freeze the memtable.
\*   FlushTable     flush_oldest_frozen_inner: reserve the table's number
\*                  (unsynced) and write the table file.
\*   FlushInstall   the same, `versions.apply([AddFile, SetLastSeq,
\*                  SetMinWalId])`: one batch, which needs a sync.
\*   SyncManifest   VersionSet::apply's `writer.sync_all()`.
\*   FlushRetire    RegolithEngine::remove_sealed_wal ->
\*                  RetiredLogs::retire (src/engine/log_retirement.rs): unlink
\*                  the flushed log and any left below it; each may fail.
\*   Ingest         RegolithEngine::install (src/engine/ingest.rs): a new
\*                  table holding a key no memtable holds, its batch synced.
\*   the crash      VersionSet::open_with_policy -> judge_end -> tail::judge
\*                  (src/engine/manifest/tail.rs), then replay of the logs at
\*                  or above min_wal_id (`should_replay_wal`).
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - Bytes inside a batch: a batch is whole or damaged. tail.rs finds whole
\*     batches past a damaged one by testing every offset; its unit tests
\*     check that search (tail_tests.rs).
\*   - The log's own torn tail: every write is synced here (Immediate), and
\*     the log rules are WalRecovery.tla's.
\*   - The open's own retirement batch and later runs: one crash, one
\*     recovery, checked from every state.
\*
\* CONFIGURATIONS (every RED also checks the invariants it does not break).
\*   MC_ManifestRecovery_Green                  the fix
\*   MC_ManifestRecovery_Green_Refuses          witness: some rot is refused,
\*                                              NeverRefusesRot fails
\*   MC_ManifestRecovery_Red_OldGuard           RecoveryOpens fails
\*   MC_ManifestRecovery_Red_NoSyncBeforeNext   RecoveryOpens fails
\*   MC_ManifestRecovery_Red_UnlinkBeforeSync   AckedSurvive fails
\*   MC_ManifestRecovery_Red_RetireBeforeTable  AckedSurvive fails
\*   MC_ManifestRecovery_Red_NoMinWalId         ReadsNewest fails
\*   MC_ManifestRecovery_Red_IgnoreProof        RotSafe fails

\* We use numbers, sequences, finite sets, and TLC's function helpers.
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* The knobs a configuration file sets.
CONSTANTS
  \* The user keys, as strings, like {"a", "b"}.
  Keys,
  \* How many writes (puts and ingests) a run may make; keeps runs finite.
  MaxSeq,
  \* How many batches the manifest may hold; keeps runs finite.
  MaxBatches,
  \* Which bug to plant: "none" is the fixed engine.
  Mutant

\* The mutant must be one we know how to plant.
ASSUME Mutant \in {"none", "OldGuard", "NoSyncBeforeNext", "UnlinkBeforeSync",
                   "RetireBeforeTable", "NoMinWalId", "IgnoreProof"} \* the RED names

\* A batch, as the manifest holds it:
\*   sync    does the writer wait for it to reach the disk (it adds a table);
\*   table   the table number it adds, 0 for none;
\*   minWal  the min_wal_id it records, 0 for none;
\*   whole   does it read back intact (FALSE only in a crash or rot image).
\* A reservation (SetNextFileId): needs no sync, adds nothing.
Reserve == [sync |-> FALSE, table |-> 0, minWal |-> 0, whole |-> TRUE]
\* What a damaged batch reads as: nothing usable at all.
Torn == [sync |-> FALSE, table |-> 0, minWal |-> 0, whole |-> FALSE]
\* No frozen memtable: an empty write set and log number 0.
NoFrozen == [w |-> {}, log |-> 0]
\* No flush under way.
Idle == [stage |-> "idle", table |-> 0, log |-> 0, at |-> 0]

\* What changes from step to step.
VARIABLES
  \* The last sequence number handed out (RegolithEngine::latest_seq).
  seq,
  \* The active memtable's writes, as <<key, seq>> pairs (ReadView::active).
  mem,
  \* The number of the log the active memtable writes to (wal_id).
  memLog,
  \* Every log ever created: its number maps to the writes it holds.
  logs,
  \* The log numbers whose files are still in the wal/ folder.
  onDisk,
  \* The frozen memtable waiting for its flush, or NoFrozen (ReadView::frozen).
  frozen,
  \* The next file number to hand out (Version::next_file_id).
  nextId,
  \* Every table file written: its number maps to the writes it holds.
  files,
  \* The manifest: the sequence of batches appended so far.
  man,
  \* How many leading batches a finished sync has put on the disk.
  synced,
  \* TRUE while a batch that needs a sync waits for that sync.
  pending,
  \* Ingested writes acknowledged once the pending sync finishes.
  toAck,
  \* The writes the caller has been told are durable.
  acked,
  \* The flush under way: its stage, table, log, and its batch's position.
  flushing

\* Every variable, so a step that changes none of them is a stutter.
vars == <<seq, mem, memLog, logs, onDisk, frozen, nextId, files, man, synced,
          pending, toAck, acked, flushing>> \* (the list goes on to here)

\* Every <<key, seq>> pair a write can make.
Writes == Keys \X (1..MaxSeq)

----------------------------------------------------------------------------
\* Small helpers.

\* The smallest number in a nonempty finite set.
MinOf(S) == CHOOSE m \in S : \A n \in S : m <= n
\* The largest number in a finite set, or 0 when the set is empty.
MaxOr0(S) == IF S = {} THEN 0 ELSE CHOOSE m \in S : \A n \in S : n <= m
\* The sequence numbers of key k among the writes W.
SeqsOf(W, k) == {w[2] : w \in {x \in W : x[1] = k}}
\* The writer may append now: in the fix, only when no sync is pending,
\* because VersionSet::apply holds the writer until its sync finishes.
CanAppend == ~pending \/ Mutant = "NoSyncBeforeNext"

----------------------------------------------------------------------------
\* What a power cut, or rot, can leave of the manifest.

\* The manifest with the positions in D mangled and everything else intact.
Image(D) == [j \in 1..Len(man) |-> IF j \in D THEN Torn ELSE man[j]]
\* Every state a crash can leave: any of the unsynced batches mangled, none
\* of the synced ones. Mangling a suffix is a truncated file.
CrashImages == {Image(D) : D \in SUBSET ((synced + 1)..Len(man))}
\* Rot: one synced batch mangled, which no crash does.
Rot(i) == Image({i})

\* The positions of an image that do not read back whole.
TornAt(img) == {j \in 1..Len(img) : ~img[j].whole}
\* Where replay stops: the first damaged position, or one past the end.
FirstTorn(img) == IF TornAt(img) = {} THEN Len(img) + 1 ELSE MinOf(TornAt(img))
\* The batches replay keeps: everything before the first damage.
Replayed(img) == SubSeq(img, 1, FirstTorn(img) - 1)

\* tail::proof_past: a whole batch after the damage that needed a sync and
\* has a batch after it. Its sync finished before that next batch was
\* written, and a sync covers every byte before it, the damage included.
Proof(img) ==
  \* Some position after the damage, but not the very last one, holds a
  \* whole batch of the kind the writer syncs before it writes on.
  \E j \in (FirstTorn(img) + 1)..(Len(img) - 1) : img[j].whole /\ img[j].sync

\* Does the open refuse this image?
Refuses(img) ==
  \* Only an image whose replay stopped short can be refused at all.
  /\ FirstTorn(img) <= Len(img)
  \* And then it depends on which engine we run.
  /\ CASE Mutant = "OldGuard" ->
            \* The old guard: refuse when the kept batches name no table while
            \* a table file holds data, whatever proves what.
            /\ \A j \in 1..Len(Replayed(img)) : Replayed(img)[j].table = 0
            /\ \E t \in DOMAIN files : files[t] # {} \* some table file holds writes
       \* The RED that never refuses.
       [] Mutant = "IgnoreProof" ->
            \* Never refuse: every damaged end is dropped.
            FALSE
       \* Every other engine, the fixed one included.
       [] OTHER ->
            \* The fix: refuse exactly when a later batch proves the damage
            \* was synced.
            Proof(img)

\* The min_wal_id the kept batches record: the largest, as each one only
\* ever raises it.
MinWalOf(r) == MaxOr0({r[j].minWal : j \in 1..Len(r)})
\* The kept positions that add a table, in the order they were added.
TablePositions(r) == {j \in 1..Len(r) : r[j].table # 0}
\* Recovery's memtable: the logs still on disk at or above min_wal_id.
MemOf(img) ==
  \* r is what replay kept of the manifest.
  LET r == Replayed(img) IN
  \* Every write of every log file still on disk whose number is not below
  \* min_wal_id: should_replay_wal in src/engine/mod.rs.
  UNION {logs[l] : l \in {x \in onDisk : x >= MinWalOf(r)}}
\* The writes the kept tables hold.
TableWritesOf(img) ==
  \* r is what replay kept of the manifest.
  LET r == Replayed(img) IN
  \* Every write of every table a kept batch adds.
  UNION {files[r[j].table] : j \in TablePositions(r)}
\* Everything recovery brings back.
Recovered(img) == MemOf(img) \cup TableWritesOf(img)

\* A read of key k after recovery: the memtable first, then the tables from
\* the newest added to the oldest; 0 when nothing holds k.
ReadOf(img, k) ==
  \* r is what replay kept of the manifest.
  LET r == Replayed(img)
      \* The versions of k the recovered memtable holds.
      inMem == SeqsOf(MemOf(img), k)
      \* The kept positions whose table holds a version of k.
      holders == {j \in TablePositions(r) : SeqsOf(files[r[j].table], k) # {}}
  \* The memtable answers first, with its newest version of k.
  IN IF inMem # {} THEN MaxOr0(inMem)
     \* Nothing anywhere holds k: absent.
     ELSE IF holders = {} THEN 0
     \* Otherwise the table added last that holds k answers, newest version.
     ELSE MaxOr0(SeqsOf(files[r[MaxOr0(holders)].table], k))

\* The newest version of key k anything recovered holds.
NewestOf(img, k) == MaxOr0(SeqsOf(Recovered(img), k))

----------------------------------------------------------------------------
\* The engine's steps.

\* A new database: no writes, log 1 active, an empty manifest.
Init ==
  \* No sequence handed out yet.
  /\ seq = 0
  \* The memtable is empty.
  /\ mem = {}
  \* It writes to log 1.
  /\ memLog = 1
  \* Log 1 exists and is empty.
  /\ logs = (1 :> {})
  \* Its file is on disk.
  /\ onDisk = {1}
  \* Nothing is frozen.
  /\ frozen = NoFrozen
  \* File number 2 is next.
  /\ nextId = 2
  \* No table file yet.
  /\ files = [t \in {} |-> {}]
  \* The manifest holds no batch.
  /\ man = <<>>
  \* Nothing synced beyond its header.
  /\ synced = 0
  \* No sync pending.
  /\ pending = FALSE
  \* No ingest waits for its acknowledgement.
  /\ toAck = {}
  \* Nothing acknowledged.
  /\ acked = {}
  \* No flush under way.
  /\ flushing = Idle

\* A put of key k: it takes the next sequence, lands in the memtable and the
\* active log, and is acknowledged, durable in the synced log.
Put(k) ==
  \* There is a sequence left to take.
  /\ seq < MaxSeq
  \* It takes the next one.
  /\ seq' = seq + 1
  \* The memtable holds it.
  /\ mem' = mem \cup {<<k, seq + 1>>}
  \* So does the active log.
  /\ logs' = [logs EXCEPT ![memLog] = @ \cup {<<k, seq + 1>>}]
  \* The caller is told it is durable.
  /\ acked' = acked \cup {<<k, seq + 1>>}
  \* Nothing else changes.
  /\ UNCHANGED <<memLog, onDisk, frozen, nextId, files, man, synced, pending,
                 toAck, flushing>> \* (the list goes on to here)

\* seal_active: the memtable freezes behind a fresh one and a fresh log,
\* whose number a reservation batch records.
Seal ==
  \* There is something to freeze.
  /\ mem # {}
  \* The previous frozen memtable is flushed already (one at a time here).
  /\ frozen = NoFrozen
  \* The manifest writer is free.
  /\ CanAppend
  \* The manifest has room in this bounded run.
  /\ Len(man) < MaxBatches
  \* Append the reservation of the new log's number; it needs no sync.
  /\ man' = Append(man, Reserve)
  \* The old memtable and its log wait for a flush.
  /\ frozen' = [w |-> mem, log |-> memLog]
  \* A fresh, empty memtable takes new writes.
  /\ mem' = {}
  \* It writes to the new log.
  /\ memLog' = nextId
  \* That number is used.
  /\ nextId' = nextId + 1
  \* The new log exists, empty.
  /\ logs' = logs @@ (nextId :> {})
  \* Its file is on disk.
  /\ onDisk' = onDisk \cup {nextId}
  \* Nothing else changes.
  /\ UNCHANGED <<seq, files, synced, pending, toAck, acked, flushing>>

\* The flush reserves a number for its table and writes the table file.
FlushTable ==
  \* A memtable is frozen.
  /\ frozen.log # 0
  \* No flush is under way.
  /\ flushing = Idle
  \* The manifest writer is free.
  /\ CanAppend
  \* The manifest has room.
  /\ Len(man) < MaxBatches
  \* Append the reservation of the table's number; it needs no sync.
  /\ man' = Append(man, Reserve)
  \* The table file holds the frozen memtable's writes.
  /\ files' = files @@ (nextId :> frozen.w)
  \* The flush remembers its table and the log that table covers.
  /\ flushing' = [stage |-> "written", table |-> nextId, log |-> frozen.log, at |-> 0]
  \* That number is used.
  /\ nextId' = nextId + 1
  \* Nothing else changes.
  /\ UNCHANGED <<seq, mem, memLog, logs, onDisk, frozen, synced, pending,
                 toAck, acked>> \* (the list goes on to here)

\* The flush appends the batch that adds its table. In the fix that batch
\* also records min_wal_id: every log up to the flushed one is in tables.
FlushInstall ==
  \* The table file is written.
  /\ flushing.stage = "written"
  \* The manifest writer is free.
  /\ CanAppend
  \* The table's batch: needs a sync, adds the table, and in the fix
  \* records the log after the flushed one as the lowest to replay.
  /\ LET table == [sync |-> TRUE, table |-> flushing.table, whole |-> TRUE,
                   minWal |-> IF Mutant \in {"NoMinWalId", "RetireBeforeTable"}
                              THEN 0 \* the REDs that leave it out of this batch
                              ELSE flushing.log + 1] \* the fix: logs up to ours are done
         \* RED RetireBeforeTable: min_wal_id in a batch of its own, ahead
         \* of the table's, needing no sync.
         retire == [Reserve EXCEPT !.minWal = flushing.log + 1]
         \* What this step appends.
         bs == IF Mutant = "RetireBeforeTable" THEN <<retire, table>> ELSE <<table>>
     IN \* The manifest has room for it.
        /\ Len(man) + Len(bs) <= MaxBatches \* the manifest has room for it
        \* Append it.
        /\ man' = man \o bs
        \* The flush remembers where its batch ends, to wait for its sync.
        /\ flushing' = [flushing EXCEPT !.stage = "installed", !.at = Len(man) + Len(bs)]
  \* A sync is now pending.
  /\ pending' = TRUE
  \* RED UnlinkBeforeSync: the log goes before its table's batch is durable.
  /\ onDisk' = IF Mutant = "UnlinkBeforeSync" THEN onDisk \ {flushing.log} ELSE onDisk
  \* Nothing else changes.
  /\ UNCHANGED <<seq, mem, memLog, logs, frozen, nextId, files, synced, toAck, acked>>

\* The pending sync finishes: every batch written so far is on the disk.
SyncManifest ==
  \* A batch waits for it.
  /\ pending
  \* Everything appended is now synced.
  /\ synced' = Len(man)
  \* Nothing waits any more.
  /\ pending' = FALSE
  \* An ingest whose batch this sync covered is acknowledged.
  /\ acked' = acked \cup toAck
  \* None is left waiting.
  /\ toAck' = {}
  \* Nothing else changes.
  /\ UNCHANGED <<seq, mem, memLog, logs, onDisk, frozen, nextId, files, man,
                 flushing>> \* (the list goes on to here)

\* RetiredLogs::retire: once the table's batch is synced, the frozen
\* memtable retires and its log is unlinked, with any left below it; any
\* of those unlinks may fail and leave its file.
FlushRetire ==
  \* The table's batch is in.
  /\ flushing.stage = "installed"
  \* And synced: apply returned only after its sync.
  /\ flushing.at <= synced
  \* Some of the flushed logs go; the rest failed to unlink and stay.
  /\ \E gone \in SUBSET {l \in onDisk : l <= flushing.log} :
       onDisk' = onDisk \ gone \* those files leave the wal/ folder
  \* The frozen memtable is retired.
  /\ frozen' = NoFrozen
  \* The flush is over.
  /\ flushing' = Idle
  \* Nothing else changes.
  /\ UNCHANGED <<seq, mem, memLog, logs, nextId, files, man, synced, pending,
                 toAck, acked>> \* (the list goes on to here)

\* An ingest of key k beside the memtables: a new table at the next
\* sequence, made durable by its own synced batch. The engine flushes a
\* memtable holding a key of the file first, so here no memtable holds k.
Ingest(k) ==
  \* There is a sequence left to take.
  /\ seq < MaxSeq
  \* No memtable holds k.
  /\ ~\E w \in mem \cup frozen.w : w[1] = k
  \* The manifest writer is free.
  /\ CanAppend
  \* There is room for the reservation and the table's batch.
  /\ Len(man) + 2 <= MaxBatches
  \* Reserve the table's number, then add the table; the second needs a sync.
  /\ man' = man \o <<Reserve, [Reserve EXCEPT !.sync = TRUE, !.table = nextId]>>
  \* The table file holds the one ingested write.
  /\ files' = files @@ (nextId :> {<<k, seq + 1>>})
  \* That number is used.
  /\ nextId' = nextId + 1
  \* The ingest takes the next sequence.
  /\ seq' = seq + 1
  \* A sync is pending.
  /\ pending' = TRUE
  \* The ingest is acknowledged once that sync finishes.
  /\ toAck' = toAck \cup {<<k, seq + 1>>}
  \* Nothing else changes.
  /\ UNCHANGED <<mem, memLog, logs, onDisk, frozen, synced, acked, flushing>>

\* Every step the engine can take.
Next ==
  \/ \E k \in Keys : Put(k)    \* a caller writes some key
  \/ Seal                       \* the memtable freezes behind a new log
  \/ FlushTable                 \* the flush writes its table file
  \/ FlushInstall               \* the flush appends its table's batch
  \/ SyncManifest               \* the pending manifest sync finishes
  \/ FlushRetire                \* the flush retires its memtable and logs
  \/ \E k \in Keys : Ingest(k) \* a caller ingests a table of some key

\* Every run: start in Init, then take steps or stutter.
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Invariants, each checked against every crash image of every state.

\* Every variable holds the kind of value its comment says.
TypeOK ==
  \* The sequence stays within the bound.
  /\ seq \in 0..MaxSeq
  \* Writes are key and sequence pairs.
  /\ mem \subseteq Writes
  \* The synced prefix lies within the manifest.
  /\ synced \in 0..Len(man)
  \* The manifest stays within its bound.
  /\ Len(man) <= MaxBatches
  \* Acknowledged writes are writes.
  /\ acked \subseteq Writes

\* E29. The open accepts every state a crash leaves. It rules out the old
\* refusal of a first flush cut while its table was being added.
RecoveryOpens == \A img \in CrashImages : ~Refuses(img)

\* E29. Whatever a crash left, an open that accepts brings back every
\* acknowledged write. It rules out a log unlinked before the table's batch
\* was synced, and a min_wal_id durable without its table.
AckedSurvive ==
  \* For every crash image the open accepts, nothing acknowledged is missing.
  \A img \in CrashImages : ~Refuses(img) => acked \subseteq Recovered(img)

\* E30. Reading the memtable first, then tables newest first, returns the
\* newest version recovered, for every key. It rules out a flushed log
\* replayed above a newer table.
ReadsNewest ==
  \* For every crash image the open accepts,
  \A img \in CrashImages : ~Refuses(img) =>
    \* every key reads as its newest recovered version.
    \A k \in Keys : ReadOf(img, k) = NewestOf(img, k)

\* E29, the refusal side. When rot mangles a synced batch and a later batch
\* proves that, the open refuses or loses nothing acknowledged. It rules out
\* a judge that drops every damaged end, which here drops a flushed table
\* whose log is gone.
RotSafe ==
  \* For every synced batch rot could mangle,
  \A i \in 1..synced :
    \* if a later batch proves it synced, the open refuses or keeps every
    \* acknowledged write.
    Proof(Rot(i)) => (Refuses(Rot(i)) \/ acked \subseteq Recovered(Rot(i)))

\* The witness: the open never refuses rot. The fix must break it, or it
\* keeps RotSafe by never meeting the case.
NeverRefusesRot == \A i \in 1..synced : ~Refuses(Rot(i))

====
