---- MODULE IngestDurability ----
\* D48: what a power cut leaves of an ingest that is not rewritten.
\*
\* Under `Eventual` durability a power cut must leave a gap-free prefix of
\* commit order (plan 4.2). An ingest is a commit in that order: it draws
\* the next sequence under the commit pipeline's mutex like any commit.
\* It is made durable by its own channel, the synced manifest edit that
\* installs its table, not by the log. Before D48 the ingest flushed every
\* memtable first, which made every earlier commit durable on the way. It
\* now flushes only a memtable holding a key of its file's range, so the
\* commits in the other memtables may still be only in the log, unsynced.
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/IngestDurability.lean:
\*   step_inv, reachable_inv        the fixed protocol keeps its invariant:
\*                                  once installed, every commit before the
\*                                  ingest's place is synced
\*   surviving_ingest_keeps_prefix  so an ingest that survives a power cut
\*                                  keeps every commit before it, and what
\*                                  survives is a gap-free prefix (GapFreePrefix
\*                                  here, for any number of commits)
\*   no_log_sync_loses_commit       RED NoLogSync, as a counterexample
\*
\* THE ENGINE.
\*   RegolithEngine::install            src/engine/ingest.rs
\*     Under the pipeline mutex: sync the active log
\*     (`sync_active_wal`), draw the sequence, apply the manifest edit
\*     (synced), publish. A commit appends its record to the log under the
\*     same mutex; under `Eventual` nothing syncs the log except a rotation,
\*     a group with an `Immediate` member, and the ingest.
\*
\* THE DEFECT. Mutant "NoLogSync": the ingest's manifest record becomes
\* durable while earlier commits are only in the unsynced log. A power cut
\* then recovers the ingest and loses a commit ordered before it.
\*
\* THE FIX. The ingest syncs the log before its manifest record, under the
\* mutex, so every commit ordered before it is durable first.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - Sequences: the mutex serializes the writers, so their order of
\*     arrival is commit order.
\*   - The memtable flushes: a flush makes a commit durable through an
\*     SSTable instead of the log, which only adds to what survives; the
\*     prefix it leaves is the one the log sync leaves.
\*   - Sealed logs: a rotation syncs the log it seals (E2, WalRotation.tla),
\*     so only the active log can hold unsynced records.
\*   - The crash itself: the durable sets only grow, so checking the
\*     invariant in every state checks a power cut in every state.
\*
\* CONFIGURATIONS.
\*   MC_IngestDurability_Green            Mutant = "none"
\*   MC_IngestDurability_Red_NoLogSync    GapFreePrefix fails.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Commits,  \* commit ids, strings; each commits once
  Mutant    \* "none" or "NoLogSync"

\* The ingest's id.
Ingest == "ingest"

ASSUME Ingest \notin Commits
ASSUME Mutant \in {"none", "NoLogSync"}

\* Everyone who commits.
Writers == Commits \cup {Ingest}

VARIABLES
  order,     \* the writers that committed, in commit order (a sequence)
  logged,    \* the commits whose record is in the log, synced or not
  synced,    \* the commits whose record the log has synced
  installed, \* whether the ingest's manifest record is durable
  holding    \* whether the ingest is between its log sync and its record,
             \* holding the pipeline mutex

\* Every variable, so a step that changes none of them is a stutter.
vars == <<order, logged, synced, installed, holding>>

\* The writers that have committed, as a set.
Committed == {order[i] : i \in 1..Len(order)}

\* The start: nothing committed, logged, synced or installed.
Init ==
  /\ order     = <<>>
  /\ logged    = {}
  /\ synced    = {}
  /\ installed = FALSE
  /\ holding   = FALSE

\* Commit c takes the mutex, appends its record to the log, unsynced
\* under `Eventual`, and is next in commit order. It waits while the ingest
\* holds the mutex.
Commit(c) ==
  /\ c \notin Committed
  /\ ~holding
  /\ order'  = Append(order, c)
  /\ logged' = logged \cup {c}
  /\ UNCHANGED <<synced, installed, holding>>

\* The log is synced: a rotation, or a group with an `Immediate` member.
\* Every logged record becomes durable.
SyncLog ==
  /\ ~holding
  /\ synced' = logged
  /\ UNCHANGED <<order, logged, installed, holding>>

\* The ingest takes the mutex and, in the fix, syncs the log. The mutant
\* skips the sync.
IngestSync ==
  /\ Ingest \notin Committed
  /\ ~holding
  /\ holding' = TRUE
  /\ synced'  = IF Mutant = "NoLogSync" THEN synced ELSE logged
  /\ UNCHANGED <<order, logged, installed>>

\* Still under the mutex, the ingest draws its place in commit order and
\* its synced manifest edit makes it durable; then it releases the mutex.
IngestInstall ==
  /\ holding
  /\ order'     = Append(order, Ingest)
  /\ installed' = TRUE
  /\ holding'   = FALSE
  /\ UNCHANGED <<logged, synced>>

\* Every step the system can take.
Next ==
  \/ \E c \in Commits : Commit(c)
  \/ SyncLog
  \/ IngestSync
  \/ IngestInstall

\* Every behaviour: start in Init, then take Next steps or stutter.
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ order \in Seq(Writers)
  /\ logged \subseteq Commits
  /\ synced \subseteq logged
  /\ installed \in BOOLEAN
  /\ holding \in BOOLEAN

\* What a power cut now leaves: the synced commits, and the ingest once its
\* manifest record is durable.
Recovered == synced \cup (IF installed THEN {Ingest} ELSE {})

\* THE HEADLINE. A power cut in any state recovers the first n writers of
\* commit order, for some n: no writer survives while one before it is lost.
GapFreePrefix ==
  \E n \in 0..Len(order) : Recovered = {order[i] : i \in 1..n}

====
