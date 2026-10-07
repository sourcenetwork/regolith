---- MODULE RepeatableRead ----
\* What an optimistic commit validates at each isolation level, transcribed
\* from the code, and checked against the workload DefraDB runs on it: appends
\* to a Merkle DAG whose head set is derived from keys, the sweep that reclaims
\* superseded heads, and a document write derived from a definition read.
\*
\* THE ENGINE, as implemented. Each operator below names the function it is
\* taken from, and the shape is kept so the two can be read side by side.
\*
\*   Transaction::observe            src/transaction.rs
\*     A point read records its key with the begin snapshot as its anchor
\*     (`read_horizon` is `snapshot_seq` for an optimistic transaction).
\*   TxnScanStream::yield_cursor     src/transaction.rs
\*     A scan records one stretch per unbroken run of snapshot keys it
\*     yields, its first and last key, at every level. It records each
\*     yielded key as a read only when `validates_scanned_keys` holds, which
\*     is `Serializable` alone.
\*   Transaction::validation_set     src/transaction.rs
\*     Which recorded reads the level validates: every one when
\*     `validates_every_read` (`RepeatableRead`, `Serializable`); the written ones
\*     at `ReadCommitted`; the written or `get_for_update` ones otherwise.
\*   scan_range::cover               src/transaction/scan_range.rs
\*     Every written key inside a stretch a scan walked is a read at the
\*     begin snapshot, so a scan-then-write is never elided as blind.
\*   Engine::commit_locked           src/engine/commit/mod.rs
\*     A read aborts when a newer write to its key exists. A written key not
\*     among the reads aborts on a newer write unless the write stores
\*     exactly what the key already holds (`write_matches_committed`,
\*     src/engine/mod.rs: byte equality, and a delete equals only an absent
\*     key). The writes then apply under one sequence.
\*
\* Reads are performed when a transaction begins. They are snapshot reads in
\* the engine, answered from the state at begin whenever they are issued, so
\* taking them at begin loses no interleaving. A commit takes one sequence
\* here where the engine gives a batch one per operation; every operation of
\* a commit after the snapshot sorts above it and every one before sorts at
\* or below, which is all the check reads. Range deletes, merge operands,
\* `get_for_update` and the pessimistic flavour do not occur in the workload;
\* the `get_for_update` term of `validation_set` is kept, with an empty set,
\* so the transcription stays complete.
\*
\* THE WORKLOAD, one transaction each.
\*   Appender  scans the head range and the marker range, derives the live
\*             heads, writes its own head key and one marker per live head
\*             naming itself. A branchable collection append.
\*   Pruner    scans the same two ranges, deletes one superseded head key and
\*             the markers against it that its scan yielded.
\*             prune_superseded_heads.
\*   Writer    point-reads the collection definition and writes a document
\*             carrying the definition it read.
\*   Patcher   replaces the definition.
\*
\* WHAT EACH LEVEL DECIDES.
\*   INV_AppendsCommit      no appender is refused. The pruner deletes keys the
\*                          appender's scan yielded; validating that scan per
\*                          key refuses the append although the head set it
\*                          derived did not change.
\*                          Serializable RED. RepeatableRead GREEN.
\*   INV_NoStaleDefinition  no document commits against a definition that was
\*                          replaced after the writer read it. The patcher
\*                          writes what the writer only read, so only a
\*                          validated point read can refuse the write.
\*                          ReadCommitted and SnapshotIsolation RED. RepeatableRead
\*                          and Serializable GREEN.
\*   INV_HeadsExact         the derived head set is the DAG's tips at every
\*                          level, reclamation included.
\*
\* RepeatableRead is the one level green on all three: Adya's PL-2.99 over
\* snapshot isolation, G2-item forbidden and predicate anti-dependencies
\* allowed. Every read a DefraDB DAG or CRDT merge path derives a decision
\* from is a point read, and the one read that is allowed to change
\* underneath a transaction is the head scan.
\*
\* DEFRALEVEL. RepeatableRead, relaxed in two places (src/transaction/policy.rs,
\* src/engine/commit/mod.rs):
\*   policy::run_is_commutative   a scan stretch wholly inside a range the
\*                                caller declares commutative is dropped
\*                                before scan_range::cover.
\*   Replaced / newest_terminator a key the commit only merges into, and did
\*                                not read, aborts only on a newer write that
\*                                replaced it, never on a newer merge operand.
\* Two more workloads exercise them. Mergers apply the same remote block, so
\* they write identical head and marker keys inside the stretches their head
\* scans walked. Incrementers blind-merge one counter that a Resetter
\* replaces.
\*   INV_DuplicateMergesCommit         no merger is refused over writes
\*                                     identical to its own.
\*                                     RepeatableRead RED. DefraLevel GREEN,
\*                                     and RED again without the policy.
\*   INV_IncrementsCommitUnlessReplaced an increment aborts only when a reset
\*                                     committed after it began.
\*                                     RepeatableRead RED. DefraLevel GREEN.
\*   INV_NoIncrementAcrossReset        no increment commits over a reset that
\*                                     committed after it began. Every level.
\* INV_HeadsExact is the check that dropping the head stretches is safe for
\* the head set: the derived heads stay the DAG's tips.

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  Appenders, \* naturals; an appender's id is also its block id
  Seed,      \* the block already established as the head, a natural
  Pruner,    \* transaction ids, naturals outside Appenders
  Writer,
  Patcher,
  Mergers,      \* transactions applying the remote block, possibly none
  Remote,       \* the remote block, a natural
  RemoteParents,\* the parents the remote block names, fixed by its content
  Incrementers, \* transactions blind-merging the counter, possibly none
  Resetters,    \* transactions replacing the counter, possibly none
  CommutativeRanges, \* ranges the KeyClassifier declares commutative
  Level      \* "ReadCommitted" | "SnapshotIsolation" | "RepeatableRead" | "Serializable" | "DefraLevel"

ASSUME Appenders # {} /\ Appenders \subseteq Nat
ASSUME Seed \in Nat /\ Seed \notin Appenders
ASSUME {Pruner, Writer, Patcher} \subseteq Nat
ASSUME Cardinality({Pruner, Writer, Patcher}) = 3
ASSUME {Pruner, Writer, Patcher} \cap Appenders = {}
ASSUME Level \in {"ReadCommitted", "SnapshotIsolation", "RepeatableRead", "Serializable",
                  "DefraLevel"}
ASSUME Remote \in Nat /\ Remote \notin Appenders \cup {Seed}
ASSUME RemoteParents \subseteq Appenders \cup {Seed}
ASSUME Mergers \cup Incrementers \cup Resetters \subseteq Nat
ASSUME (Mergers \cup Incrementers \cup Resetters) \cap (Appenders \cup {Pruner, Writer, Patcher}) = {}
ASSUME Mergers \cap Incrementers = {} /\ Mergers \cap Resetters = {} /\ Incrementers \cap Resetters = {}

Blocks == Appenders \cup {Seed} \cup (IF Mergers = {} THEN {} ELSE {Remote})
Txns   == Appenders \cup {Pruner, Writer, Patcher} \cup Mergers \cup Incrementers \cup Resetters

\* Keys are <<range, p, c>>. Ranges sort head < marker < def < doc, and inside
\* a range a key sorts by the blocks it names: the order a scan walks.
HeadRange    == 1
MarkerRange  == 2
DefRange     == 3
DocRange     == 4
CounterRange == 5
BlockRange   == 6
ASSUME CommutativeRanges \subseteq {HeadRange, MarkerRange}

HeadKey(b)      == <<HeadRange, b, b>>
MarkerKey(p, c) == <<MarkerRange, p, c>>
DefKey          == <<DefRange, 0, 0>>
DocKey          == <<DocRange, 0, 0>>
CounterKey      == <<CounterRange, 0, 0>>
\* A block's content-addressed key: written once, identically by anyone.
BlockKey(b)     == <<BlockRange, b, b>>

Keys == {HeadKey(b) : b \in Blocks}
        \cup {MarkerKey(p, c) : p \in Blocks, c \in Blocks}
        \cup {DefKey, DocKey, CounterKey}
        \cup {BlockKey(b) : b \in Blocks}

KeyLeq(a, b) ==
  \/ a[1] < b[1]
  \/ a[1] = b[1] /\ a[2] < b[2]
  \/ a[1] = b[1] /\ a[2] = b[2] /\ a[3] <= b[3]

MinKey(S) == CHOOSE k \in S : \A j \in S : KeyLeq(k, j)
MaxKey(S) == CHOOSE k \in S : \A j \in S : KeyLeq(j, k)

\* A value is a natural; 0 is an absent key, and a delete intends 0.
Absent == 0

VARIABLES
  clock,     \* the engine sequence, advanced by every commit that writes
  store,     \* [Keys -> Nat] what each key holds
  latest,    \* [Keys -> Nat] sequence of the last commit that wrote each key
  phase,     \* [Txns -> {"idle", "open", "committed", "aborted"}]
  snap,      \* [Txns -> Nat] begin snapshot
  tracked,   \* [Txns -> SUBSET Keys] keys recorded as reads
  runs,      \* [Txns -> SUBSET (Keys \X Keys)] stretches scans walked
  written,   \* [Txns -> SUBSET Keys] keys the commit puts or deletes
  merged,    \* [Txns -> SUBSET Keys] keys the commit merges an operand into
  replaced,  \* [Keys -> Nat] sequence of the last commit that put or deleted each key
  lostIncrement, \* TRUE once an increment aborted with no reset after it began
  acrossReset,   \* TRUE once an increment committed over a later reset
  dupRefused,    \* TRUE once a merger was refused over writes identical to its own
  intended,  \* [Txns -> [Keys -> Nat]] what each written key will hold
  parents,   \* [Blocks -> SUBSET Blocks] parents each committed block recorded
  defAtRead, \* the definition the writer read
  stale      \* TRUE once a document committed over a replaced definition

vars == <<clock, store, latest, phase, snap, tracked, runs, written, intended,
          parents, defAtRead, stale, merged, replaced, lostIncrement, acrossReset,
          dupRefused>>

Stored == {k \in Keys : store[k] # Absent}

\* The head set a scan of S derives: a stored head key no stored marker
\* names as a parent.
Heads(S) ==
  {b \in Blocks : HeadKey(b) \in S /\ ~\E c \in Blocks : MarkerKey(b, c) \in S}

Superseded(S) ==
  {b \in Blocks : HeadKey(b) \in S /\ \E c \in Blocks : MarkerKey(b, c) \in S}

----------------------------------------------------------------------------
\* One forward scan of a range over the snapshot S.

\* The keys it yields.
Yield(S, range) == {k \in S : k[1] = range}

\* TxnScanStream::yield_cursor: the stretch it records, first and last key,
\* none when it yields nothing.
Stretch(Y) == IF Y = {} THEN {} ELSE {<<MinKey(Y), MaxKey(Y)>>}

\* TxnScanStream::yield_cursor: the yielded keys it records as reads, only
\* where IsolationLevel::validates_scanned_keys holds.
ScanReads(Y) == IF Level = "Serializable" THEN Y ELSE {}

----------------------------------------------------------------------------
Init ==
  /\ clock     = 0
  /\ store     = [k \in Keys |-> IF k \in {HeadKey(Seed), DefKey, BlockKey(Seed)} THEN 1 ELSE Absent]
  /\ latest    = [k \in Keys |-> 0]
  /\ phase     = [t \in Txns |-> "idle"]
  /\ snap      = [t \in Txns |-> 0]
  /\ tracked   = [t \in Txns |-> {}]
  /\ runs      = [t \in Txns |-> {}]
  /\ written   = [t \in Txns |-> {}]
  /\ merged    = [t \in Txns |-> {}]
  /\ replaced  = [k \in Keys |-> 0]
  /\ lostIncrement = FALSE
  /\ acrossReset   = FALSE
  /\ dupRefused    = FALSE
  /\ intended  = [t \in Txns |-> [k \in Keys |-> Absent]]
  /\ parents   = [b \in Blocks |-> {}]
  /\ defAtRead = 0
  /\ stale     = FALSE

\* The remote block's parents are fixed by its content, not by the local
\* heads; the scan is the head-set read the merge path makes. A block already
\* stored is not merged again.
BeginMerger(m) ==
  LET heads   == Yield(Stored, HeadRange)
      markers == Yield(Stored, MarkerRange)
      keys    == IF BlockKey(Remote) \in Stored THEN {}
                 ELSE {HeadKey(Remote), BlockKey(Remote)}
                      \cup {MarkerKey(p, Remote) : p \in RemoteParents}
  IN /\ tracked'  = [tracked EXCEPT ![m] = ScanReads(heads) \cup ScanReads(markers)]
     /\ runs'     = [runs EXCEPT ![m] = Stretch(heads) \cup Stretch(markers)]
     /\ written'  = [written EXCEPT ![m] = keys]
     /\ intended' = [intended EXCEPT ![m] = [k \in Keys |-> IF k \in keys THEN 1 ELSE Absent]]
     /\ UNCHANGED <<merged, defAtRead>>

BeginIncrementer(i) ==
  /\ merged' = [merged EXCEPT ![i] = {CounterKey}]
  /\ UNCHANGED <<tracked, runs, written, intended, defAtRead>>

BeginResetter(r) ==
  /\ written'  = [written EXCEPT ![r] = {CounterKey}]
  /\ intended' = [intended EXCEPT ![r] = [k \in Keys |-> Absent]]
  /\ UNCHANGED <<tracked, runs, merged, defAtRead>>

BeginAppender(a) ==
  LET heads   == Yield(Stored, HeadRange)
      markers == Yield(Stored, MarkerRange)
      keys    == {HeadKey(a), BlockKey(a)} \cup {MarkerKey(h, a) : h \in Heads(Stored)}
  IN /\ tracked'  = [tracked EXCEPT ![a] = ScanReads(heads) \cup ScanReads(markers)]
     /\ runs'     = [runs EXCEPT ![a] = Stretch(heads) \cup Stretch(markers)]
     /\ written'  = [written EXCEPT ![a] = keys]
     /\ intended' = [intended EXCEPT ![a] = [k \in Keys |-> IF k \in keys THEN 1 ELSE Absent]]
     /\ UNCHANGED <<merged, defAtRead>>

\* Enabled once something is reclaimable, as the real sweep is a no-op
\* otherwise. One head per pass, chosen freely, with the markers against it
\* the scan yielded: a marker an open append is about to write is not in
\* the snapshot and is not touched.
BeginPruner ==
  LET heads   == Yield(Stored, HeadRange)
      markers == Yield(Stored, MarkerRange)
  IN /\ \E b \in Superseded(Stored) :
          written' = [written EXCEPT ![Pruner] =
                       {HeadKey(b)} \cup {m \in markers : m[2] = b}]
     /\ intended' = [intended EXCEPT ![Pruner] = [k \in Keys |-> Absent]]
     /\ tracked'  = [tracked EXCEPT ![Pruner] = ScanReads(heads) \cup ScanReads(markers)]
     /\ runs'     = [runs EXCEPT ![Pruner] = Stretch(heads) \cup Stretch(markers)]
     /\ UNCHANGED <<merged, defAtRead>>

\* Transaction::observe on the definition, then a document carrying it.
BeginWriter ==
  /\ tracked'   = [tracked EXCEPT ![Writer] = {DefKey}]
  /\ written'   = [written EXCEPT ![Writer] = {DocKey}]
  /\ intended'  = [intended EXCEPT ![Writer] =
                    [k \in Keys |-> IF k = DocKey THEN store[DefKey] ELSE Absent]]
  /\ defAtRead' = store[DefKey]
  /\ UNCHANGED <<runs, merged>>

BeginPatcher ==
  /\ written'  = [written EXCEPT ![Patcher] = {DefKey}]
  /\ intended' = [intended EXCEPT ![Patcher] =
                   [k \in Keys |-> IF k = DefKey THEN store[DefKey] + 1 ELSE Absent]]
  /\ UNCHANGED <<tracked, runs, merged, defAtRead>>

Begin(t) ==
  /\ phase[t] = "idle"
  /\ phase' = [phase EXCEPT ![t] = "open"]
  /\ snap'  = [snap EXCEPT ![t] = clock]
  /\ CASE t \in Appenders -> BeginAppender(t)
       [] t = Pruner       -> BeginPruner
       [] t = Writer       -> BeginWriter
       [] t = Patcher      -> BeginPatcher
       [] t \in Mergers      -> BeginMerger(t)
       [] t \in Incrementers -> BeginIncrementer(t)
       [] t \in Resetters    -> BeginResetter(t)
  /\ UNCHANGED <<clock, store, latest, parents, stale, replaced, lostIncrement, acrossReset,
                 dupRefused>>

----------------------------------------------------------------------------
\* The commit, transcribed.

\* IsolationLevel::validates_every_read.
EveryRead == Level \in {"RepeatableRead", "Serializable", "DefraLevel"}

\* No get_for_update in this workload.
ForUpdate(t) == {}

\* Transaction::validation_set: the recorded reads the level validates.
ValidatedReads(t) ==
  {k \in tracked[t] :
     IF EveryRead THEN TRUE
     ELSE IF Level = "ReadCommitted" THEN k \in written[t]
     ELSE k \in ForUpdate(t) \/ k \in written[t]}

\* scan_range::cover: every written key inside a stretch a scan walked joins
\* the reads. Each read is already anchored at the begin snapshot, so the
\* re-anchoring `cover` also performs is the identity here.
\* policy::run_is_commutative: at DefraLevel a stretch inside one declared
\* range is dropped before cover sees it.
Commutative(s) == Level = "DefraLevel" /\ s[1][1] = s[2][1] /\ s[1][1] \in CommutativeRanges
CoveredRuns(t) == {s \in runs[t] : ~Commutative(s)}

Walked(t, k) == \E s \in CoveredRuns(t) : KeyLeq(s[1], k) /\ KeyLeq(k, s[2])

Reads(t) == ValidatedReads(t) \cup {k \in (written[t] \cup merged[t]) : Walked(t, k)}

\* Engine::commit_locked, the read loop: a read aborts on any newer write.
ReadConflict(t) == \E k \in Reads(t) : latest[k] > snap[t]

\* Engine::commit_locked, the write loop with `writes_at` the begin snapshot:
\* a written key not among the reads aborts on a newer write, unless the
\* write stores what the key already holds (write_matches_committed).
WriteConflict(t) ==
  \E k \in written[t] \ Reads(t) : latest[k] > snap[t] /\ intended[t][k] # store[k]

\* The same loop for a key the commit only merges into: a merge is never
\* elided. At DefraLevel (IsolationLevel::blind_merges_commute) it aborts only
\* on a newer write that replaced the key, walking past newer operands.
MergeConflict(t) ==
  \E k \in merged[t] \ (Reads(t) \cup written[t]) :
     IF Level = "DefraLevel" THEN replaced[k] > snap[t] ELSE latest[k] > snap[t]

Conflicts(t) == ReadConflict(t) \/ WriteConflict(t) \/ MergeConflict(t)

Commit(t) ==
  /\ phase[t] = "open"
  /\ IF Conflicts(t)
       THEN /\ phase' = [phase EXCEPT ![t] = "aborted"]
            /\ lostIncrement' = (lostIncrement \/
                                 (t \in Incrementers /\ replaced[CounterKey] <= snap[t]))
            /\ dupRefused' = (dupRefused \/
                              (t \in Mergers /\ \A k \in written[t] :
                                  latest[k] > snap[t] => store[k] = intended[t][k]))
            /\ UNCHANGED <<clock, store, latest, parents, stale, replaced, acrossReset>>
       ELSE /\ phase'   = [phase EXCEPT ![t] = "committed"]
            /\ clock'   = clock + 1
            /\ store'   = [k \in Keys |->
                             IF k \in written[t] THEN intended[t][k]
                             ELSE IF k \in merged[t] THEN store[k] + 1
                             ELSE store[k]]
            /\ latest'  = [k \in Keys |->
                             IF k \in written[t] \cup merged[t] THEN clock + 1 ELSE latest[k]]
            /\ replaced' = [k \in Keys |-> IF k \in written[t] THEN clock + 1 ELSE replaced[k]]
            /\ parents' = IF t \in Appenders
                            THEN [parents EXCEPT ![t] = {h \in Blocks : MarkerKey(h, t) \in written[t]}]
                            ELSE IF t \in Mergers /\ written[t] # {}
                            THEN [parents EXCEPT ![Remote] = RemoteParents]
                            ELSE parents
            /\ stale'   = (stale \/ (t = Writer /\ store[DefKey] # defAtRead))
            /\ acrossReset' = (acrossReset \/
                               (t \in Incrementers /\ replaced[CounterKey] > snap[t]))
            /\ UNCHANGED <<lostIncrement, dupRefused>>
  /\ UNCHANGED <<snap, tracked, runs, written, intended, defAtRead, merged>>

Next == \E t \in Txns : Begin(t) \/ Commit(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----------------------------------------------------------------------------
TypeOK ==
  /\ clock \in Nat
  /\ store \in [Keys -> Nat]
  /\ latest \in [Keys -> Nat]
  /\ phase \in [Txns -> {"idle", "open", "committed", "aborted"}]
  /\ \A t \in Txns : tracked[t] \subseteq Keys /\ written[t] \subseteq Keys /\ merged[t] \subseteq Keys
  /\ \A t \in Txns : \A s \in runs[t] : s \in Keys \X Keys /\ KeyLeq(s[1], s[2])
  /\ stale \in BOOLEAN

\* THE HEADLINE for the head set. An append that did its scan, built its
\* block and asked to commit is never turned away by a sweep that reclaimed
\* keys its scan yielded: the live set it derived was unchanged by that.
INV_AppendsCommit == \A a \in Appenders : phase[a] # "aborted"

\* THE HEADLINE for point reads. A document never commits against a
\* definition that was replaced after the writer read it.
INV_NoStaleDefinition == ~stale

\* The derived head set is the DAG's tips: the committed blocks no committed
\* block names as a parent. Holds at every level.
CommittedBlocks == {Seed} \cup {a \in Appenders : phase[a] = "committed"}
                   \cup (IF \E m \in Mergers : phase[m] = "committed" /\ written[m] # {}
                         THEN {Remote} ELSE {})
DagHeads == {b \in CommittedBlocks : ~\E c \in CommittedBlocks : b \in parents[c]}
INV_HeadsExact == Heads(Stored) = DagHeads

\* A merger is never refused when every newer write to its keys stored
\* exactly what it writes: applying a block another transaction already
\* applied lands. One whose keys a sweep reclaimed meanwhile is refused, and
\* must be, or it would write the reclaimed marker back.
INV_DuplicateMergesCommit == ~dupRefused

\* A blind increment is refused only by a reset that committed after it began.
INV_IncrementsCommitUnlessReplaced == ~lostIncrement

\* No increment commits over a reset that committed after it began.
INV_NoIncrementAcrossReset == ~acrossReset

\* A state constraint for the counter configs: the head-set transactions stay
\* idle, so the check spends its states on the counter alone.
CounterWorkloadOnly == \A t \in Appenders \cup {Pruner, Writer, Patcher} : phase[t] = "idle"

\* Under the level that refuses no append, every append lands.
EventuallyAllAppendsCommit == <>[](\A a \in Appenders : phase[a] = "committed")

====
