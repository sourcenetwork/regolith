---- MODULE IngestPublication ----
\* E8: ingest publication. Commits and an ingest draw sequences from one
\* counter, and readers take snapshots at the visible sequence.
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/Publication.lean:
\*   step_inv, reachable_inv        the visible sequence stays below every
\*                                  pending slot
\*   repeatable_snapshot            a snapshot reads every key the same at
\*                                  every later step
\*   early_publication_breaks_snapshots
\*                                  the RED case, as a counterexample
\*   fixed_protocol_refuses_early_publication
\*                                  the fix refuses that publication
\* TLC checks the same invariant here over every interleaving of a few
\* commits, one ingest and two readers.
\*
\* THE ENGINE.
\*   RegolithEngine::install            src/engine/ingest.rs
\*     Under the commit pipeline's mutex, draws the sequence from
\*     `latest_seq`, installs the table in the version with a manifest edit
\*     recording that every entry of it reads at that sequence (D48), and
\*     only then publishes the sequence on the read horizon. A commit draws
\*     and publishes under the same mutex, so none publishes in between.
\*   ReadHorizon::publish               src/engine/read_horizon.rs
\*     A `fetch_max`: the horizon only rises. A commit that drew a later
\*     sequence publishes it as soon as its own data is applied.
\*   RegolithEngine::snapshot           src/engine/mod.rs
\*     A snapshot reads at `ReadHorizon::visible`.
\*
\* THE DEFECT. The ingest holds the compaction lock, not the write lock, so a
\* commit can draw a later sequence and publish it while the ingest's table
\* is still being written. The horizon then passes the ingest's sequence. A
\* snapshot taken in that window reads the ingested keys as absent, and the
\* same snapshot reads them as present once the table is installed. Two
\* mutants show it, one per way the horizon can pass the slot:
\*   CommitPassesSlot      a commit publishes past the pending ingest slot,
\*                         which is the engine today;
\*   IngestPublishesEarly  the ingest publishes its own sequence when it
\*                         draws it, before its table is installed.
\*
\* THE FIX. The ingest's sequence is a pending slot from the moment it is
\* drawn until its table is installed, and the visible sequence never passes
\* a pending slot: a publication waits until no pending slot is at or below
\* the sequence it publishes.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing. A read returns the
\* newest installed version at or below the snapshot. Over an ordered LSM
\* tree that is what the engine's read order returns (LsmOrder.tla, Lean
\* read_newest), so one set of installed versions stands for the memtables,
\* the levels and the ingested table.
\*
\* CONFIGURATIONS.
\*   MC_IngestPublication_Green                     Mutant = "none"
\*     RepeatableSnapshot and NoPendingAtOrBelowVisible hold.
\*   MC_IngestPublication_Red_CommitPassesSlot      RepeatableSnapshot fails.
\*   MC_IngestPublication_Red_IngestPublishesEarly  RepeatableSnapshot fails.

EXTENDS Naturals, FiniteSets

CONSTANTS
  Commits,     \* commit ids, strings; each commit writes CommitKey once
  CommitKey,   \* the key every commit writes, a natural
  IngestKeys,  \* the keys the ingested table holds, naturals
  Readers,     \* reader ids, strings; each reader takes one snapshot
  Mutant       \* "none", "CommitPassesSlot" or "IngestPublishesEarly"

\* The ingest's id.
Ingest == "ingest"

ASSUME Ingest \notin Commits
ASSUME CommitKey \in Nat /\ IngestKeys \subseteq Nat
ASSUME Mutant \in {"none", "CommitPassesSlot", "IngestPublishesEarly"}

\* Everyone who draws a sequence.
Writers == Commits \cup {Ingest}

\* Every key anyone writes.
Keys == {CommitKey} \cup IngestKeys

\* The keys writer w writes, every one at the sequence it drew.
KeysOf(w) == IF w = Ingest THEN IngestKeys ELSE {CommitKey}

VARIABLES
  next,       \* the last sequence the shared counter handed out (latest_seq)
  pending,    \* the pending slots: sequences drawn whose data is not installed
  installed,  \* the installed versions <<key, sequence>>
  visible,    \* the read horizon a new snapshot reads at
  phase,      \* [Writers -> {"idle", "drawn", "installed", "published"}]
  wseq,       \* [Writers -> Nat] the sequence each writer drew, 0 before
  taken,      \* the readers that have taken their snapshot
  snap,       \* [Readers -> Nat] the sequence each reader's snapshot reads at
  seen        \* [Readers -> [Keys -> Nat]] what each snapshot read when taken

\* Every variable, so a step that changes none of them is a stutter.
vars == <<next, pending, installed, visible, phase, wseq, taken, snap, seen>>

\* The greatest element of a finite, nonempty set of naturals.
Max(S) == CHOOSE m \in S : \A n \in S : n <= m

\* A read of key k at snapshot s: the newest installed version at or below
\* s, or 0 for absent (sequences start at 1).
ReadAt(s, k) ==
  LET vs == {v[2] : v \in {x \in installed : x[1] = k /\ x[2] <= s}}
  IN IF vs = {} THEN 0 ELSE Max(vs)

\* The start: nothing drawn, installed or published, and no snapshot taken.
Init ==
  /\ next      = 0
  /\ pending   = {}
  /\ installed = {}
  /\ visible   = 0
  /\ phase     = [w \in Writers |-> "idle"]
  /\ wseq      = [w \in Writers |-> 0]
  /\ taken     = {}
  /\ snap      = [r \in Readers |-> 0]
  /\ seen      = [r \in Readers |-> [k \in Keys |-> 0]]

\* Writer w draws the next sequence. It is a pending slot until w installs
\* its data. Mutant IngestPublishesEarly: the ingest also publishes it now.
Draw(w) ==
  /\ phase[w] = "idle"
  /\ next'    = next + 1
  /\ wseq'    = [wseq EXCEPT ![w] = next + 1]
  /\ pending' = pending \cup {next + 1}
  /\ phase'   = [phase EXCEPT ![w] = "drawn"]
  /\ visible' = IF w = Ingest /\ Mutant = "IngestPublishesEarly"
                  THEN Max({visible, next + 1}) ELSE visible
  /\ UNCHANGED <<installed, taken, snap, seen>>

\* Writer w installs its versions: a commit's memtable insert, the ingest's
\* table added to the version. Its slot stops being pending.
Install(w) ==
  /\ phase[w]   = "drawn"
  /\ installed' = installed \cup {<<k, wseq[w]>> : k \in KeysOf(w)}
  /\ pending'   = pending \ {wseq[w]}
  /\ phase'     = [phase EXCEPT ![w] = "installed"]
  /\ UNCHANGED <<next, visible, wseq, taken, snap, seen>>

\* The fix's guard: no pending slot is at or below sequence s.
NoPendingAtOrBelow(s) == \A p \in pending : s < p

\* ReadHorizon::publish: writer w raises the horizon to its sequence, never
\* lowering it. The fix publishes only past no pending slot. Mutant
\* CommitPassesSlot: a commit publishes regardless.
Publish(w) ==
  /\ phase[w] = "installed"
  /\ \/ NoPendingAtOrBelow(wseq[w])
     \/ Mutant = "CommitPassesSlot" /\ w \in Commits
  /\ visible' = Max({visible, wseq[w]})
  /\ phase'   = [phase EXCEPT ![w] = "published"]
  /\ UNCHANGED <<next, pending, installed, wseq, taken, snap, seen>>

\* Reader r takes a snapshot at the horizon and records what it reads for
\* every key at that moment.
Snapshot(r) ==
  /\ r \notin taken
  /\ taken' = taken \cup {r}
  /\ snap'  = [snap EXCEPT ![r] = visible]
  /\ seen'  = [seen EXCEPT ![r] = [k \in Keys |-> ReadAt(visible, k)]]
  /\ UNCHANGED <<next, pending, installed, visible, phase, wseq>>

\* Every step the system can take.
Next ==
  \/ \E w \in Writers : Draw(w) \/ Install(w) \/ Publish(w)
  \/ \E r \in Readers : Snapshot(r)

\* Every behaviour: start in Init, then take Next steps or stutter.
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ next \in Nat
  /\ pending \subseteq 1..next
  /\ installed \subseteq Keys \X (1..next)
  /\ visible \in 0..next
  /\ phase \in [Writers -> {"idle", "drawn", "installed", "published"}]
  /\ wseq \in [Writers -> 0..next]
  /\ taken \subseteq Readers
  /\ snap \in [Readers -> 0..next]

\* THE HEADLINE. A snapshot reads every key the same at every step after it
\* was taken. Lean: repeatable_snapshot.
RepeatableSnapshot ==
  \A r \in taken : \A k \in Keys : ReadAt(snap[r], k) = seen[r][k]

\* The fix's invariant: the horizon is below every pending slot.
\* Lean: Inv.pending_above.
NoPendingAtOrBelowVisible == NoPendingAtOrBelow(visible)

====
