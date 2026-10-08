---- MODULE RepeatableRead ----
\* What an optimistic commit validates at each isolation level, transcribed
\* from the code, and checked against the workload a Merkle-DAG CRDT store runs on it: appends
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
\*     `validates_every_read` (`RepeatableRead`, `Serializable`,
\*     `DefraLevel`); the written ones at `ReadCommitted`; the written or
\*     `get_for_update` ones otherwise.
\*   scan_range::cover               src/transaction/scan_range.rs
\*     Every written or merged key inside a stretch a scan walked is a read
\*     at the begin snapshot, so a scan-then-write is never elided as blind.
\*   Engine::commit_locked           src/engine/commit/mod.rs
\*     A read aborts when a newer write to its key exists. A written key not
\*     among the reads aborts on a newer write unless the write stores
\*     exactly what the key already holds (`write_matches_committed`,
\*     src/engine/mod.rs: byte equality, a delete equals only an absent key,
\*     and never for a key the batch also merges into, since the merge on
\*     top makes the key hold something else). A merged key is never
\*     elided. The writes then apply under one sequence, a put before a
\*     merge into the same key.
\*
\* Reads are performed when a transaction begins. They are snapshot reads in
\* the engine, answered from the state at begin whenever they are issued, so
\* taking them at begin loses no interleaving. A commit takes one sequence
\* here where the engine gives a batch one per operation; every operation of
\* a commit after the snapshot sorts above it and every one before sorts at
\* or below, which is all the check reads. `get_for_update` and the
\* pessimistic flavour do not occur in the workload; the `get_for_update`
\* term of `validation_set` is kept, with an empty set, so the transcription
\* stays complete. A range delete occurs only as a plain write,
\* `Db::delete_range`: `Transaction::delete_range` refuses one, so no commit
\* batch carries it. `write_matches_committed` also refuses an elision when
\* the key's newest entry is an unresolved merge operand. That is not
\* modeled, because here it cannot change an outcome: a counter with an
\* operand on top holds at least one, which a reset's delete never equals,
\* and a rebase's put is already refused elision by the merge its own batch
\* carries.
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
\* allowed. Every read a Merkle-DAG CRDT merge path derives a decision
\* from is a point read, and the one read that is allowed to change
\* underneath a transaction is the head scan.
\*
\* DEFRALEVEL. RepeatableRead, relaxed in three places for an optimistic
\* transaction (src/transaction/policy.rs, src/engine/commit/mod.rs):
\*   policy::run_is_commutative   a scan stretch whose first and last key lie
\*                                in one prefix the caller declares
\*                                commutative is dropped before
\*                                scan_range::cover. A stretch that leaves the
\*                                prefix is kept, as at RepeatableRead.
\*   KeyClass::ContentAddressed   a key in a prefix the caller declares
\*                                content-addressed is validated nowhere: a
\*                                read of it records nothing, and a put,
\*                                delete or merge of it is never checked
\*                                against a newer write. Sound only where the
\*                                key determines the bytes, as for a block.
\*   Replaced / newest_terminator a key the commit only merges into (it
\*                                neither read it nor puts or deletes it)
\*                                aborts only on a newer put, delete or range
\*                                delete, never on a newer merge operand.
\*                                Operands apply in commit order.
\* For a key merged into blind this is not snapshot isolation: two
\* transactions merging into it concurrently both commit. What the model
\* checks for such a key is the value it ends up holding.
\*
\* More workloads exercise DefraLevel, each in configs of its own.
\*   Mergers       apply the same remote block, so they write identical head
\*                 and marker keys inside the stretches their head scans
\*                 walked, and each reads whether the block is stored before
\*                 putting it.
\*   Incrementers  merge an increment into a counter, reading nothing.
\*   ReadMergers   point-read the counter, merge an increment, and record a
\*                 receipt: the count they read plus one.
\*   Rebasers      put the counter to 1 and merge an increment on top, reading
\*                 nothing: one key put and merged in one batch.
\*   Resetters     delete the counter.
\*   Clearers      range-delete the counter's range with Db::delete_range.
\*   Migrators     scan from the head range through the definition in one
\*                 stream, a stretch that leaves the head prefix, and write the
\*                 definition one version up.
\* They are checked against these invariants.
\*   INV_DuplicateMergesCommit  no merger is refused over writes identical to
\*                              its own. RepeatableRead RED. DefraLevel GREEN
\*                              with the head and marker prefixes commutative
\*                              and the blocks content-addressed, and RED
\*                              again without either declaration.
\*   INV_CounterExact           the counter holds what its contract says (the
\*                              ghost below): no increment lost, none counted
\*                              twice, and a reset really resets.
\*                              DefraLevel GREEN.
\*   INV_ReceiptsExact          every receipt is the count its merge produced.
\*                              DefraLevel GREEN.
\*   INV_IncrementsCommitUnlessReplaced  a blind increment is refused only
\*                              when committing it would break the counter, so
\*                              concurrent increments never refuse each other.
\*                              RepeatableRead RED. DefraLevel GREEN.
\*   INV_NoStaleDefinition      also covers a migration, whose definition
\*                              write derives from the definition its scan
\*                              yielded. DefraLevel GREEN.
\*   INV_HeadsExact             the check that dropping the head stretches is
\*                              safe for the head set. DefraLevel GREEN.
\* Declaring a mutable key content-addressed breaks the class's precondition:
\* Red_DefinitionContentAddressed declares the definition, whose bytes change
\* under one key, and INV_NoStaleDefinition fails.
\*
\* MUTANTS. `Mutant` breaks one line of the transcription, and each has a RED
\* config: that is what shows the line keeps a GREEN config green.
\*   ReadMergeBlind             a merged key the transaction read is
\*                              validated as a blind merge.
\*                              INV_ReceiptsExact RED.
\*   PutMergeBlind              a merged key the batch also puts is validated
\*                              as a blind merge.  INV_CounterExact RED.
\*                              The engine also checks the put on its own, so
\*                              there this takes losing that check as well as
\*                              `Replaced`.
\*   PutMergeElides             an identical put is elided although its batch
\*                              merges on top.     INV_CounterExact RED.
\*   MergeIgnoresReplacement    a blind merge conflicts with nothing.
\*                              INV_CounterExact RED.
\*   RangeDeleteNotReplacement  a range tombstone does not replace the keys it
\*                              covers.            INV_CounterExact RED.
\*   PolicyIgnoresRange         a stretch is dropped when either end lies in a
\*                              commutative prefix, wherever it runs.
\*                              INV_NoStaleDefinition RED.

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
  ReadMergers,  \* transactions reading the counter and merging into it, possibly none
  Rebasers,     \* transactions putting the counter and merging into it, possibly none
  Resetters,    \* transactions deleting the counter, possibly none
  Clearers,     \* plain range deletes over the counter's range, possibly none
  Migrators,    \* transactions rewriting the definition after a scan, possibly none
  CommutativeRanges, \* ranges the KeyClassifier declares commutative
  ContentAddressedRanges, \* ranges the KeyClassifier declares content-addressed
  Level,     \* "ReadCommitted" | "SnapshotIsolation" | "RepeatableRead" | "Serializable" | "DefraLevel"
  Mutant     \* "none", or the line a RED config breaks (MUTANTS above)

CounterTxns == Incrementers \cup ReadMergers \cup Rebasers \cup Resetters \cup Clearers
ExtraTxns   == Mergers \cup CounterTxns \cup Migrators

ASSUME Appenders # {} /\ Appenders \subseteq Nat
ASSUME Seed \in Nat /\ Seed \notin Appenders
ASSUME {Pruner, Writer, Patcher} \subseteq Nat
ASSUME Cardinality({Pruner, Writer, Patcher}) = 3
ASSUME {Pruner, Writer, Patcher} \cap Appenders = {}
ASSUME Level \in {"ReadCommitted", "SnapshotIsolation", "RepeatableRead", "Serializable",
                  "DefraLevel"}
ASSUME Mutant \in {"none", "ReadMergeBlind", "PutMergeBlind", "PutMergeElides",
                   "MergeIgnoresReplacement", "RangeDeleteNotReplacement",
                   "PolicyIgnoresRange"}
ASSUME Remote \in Nat /\ Remote \notin Appenders \cup {Seed}
ASSUME RemoteParents \subseteq Appenders \cup {Seed}
ASSUME ExtraTxns \subseteq Nat
ASSUME ExtraTxns \cap (Appenders \cup {Pruner, Writer, Patcher}) = {}
\* The extra workloads are pairwise disjoint.
ASSUME Cardinality(ExtraTxns) =
         Cardinality(Mergers) + Cardinality(Incrementers) + Cardinality(ReadMergers)
         + Cardinality(Rebasers) + Cardinality(Resetters) + Cardinality(Clearers)
         + Cardinality(Migrators)

Blocks == Appenders \cup {Seed} \cup (IF Mergers = {} THEN {} ELSE {Remote})
Txns   == Appenders \cup {Pruner, Writer, Patcher} \cup ExtraTxns

\* Keys are <<range, p, c>>. Ranges sort head < marker < def < doc < counter
\* < block, and inside a range a key sorts by the blocks it names: the order a
\* scan walks. A range is also the prefix a KeyClassifier declares.
HeadRange    == 1
MarkerRange  == 2
DefRange     == 3
DocRange     == 4
CounterRange == 5
BlockRange   == 6
ASSUME CommutativeRanges \subseteq {HeadRange, MarkerRange}
\* A key has one class.
ASSUME /\ ContentAddressedRanges \subseteq {HeadRange, MarkerRange, DefRange, DocRange,
                                             CounterRange, BlockRange}
       /\ ContentAddressedRanges \cap CommutativeRanges = {}

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

\* A value is a natural; 0 is an absent key, and a delete intends 0. The
\* counter's value is its count, so an absent counter counts 0.
Absent == 0

VARIABLES
  clock,     \* the engine sequence, advanced by every commit that writes
  store,     \* [Keys -> Nat] what each key holds
  latest,    \* [Keys -> Nat] sequence of the last commit that wrote each key
  replaced,  \* [Keys -> Nat] sequence of the last put, delete or range delete of each key
  phase,     \* [Txns -> {"idle", "open", "committed", "aborted"}]
  snap,      \* [Txns -> Nat] begin snapshot
  tracked,   \* [Txns -> SUBSET Keys] keys recorded as reads
  runs,      \* [Txns -> SUBSET (Keys \X Keys)] stretches scans walked
  written,   \* [Txns -> SUBSET Keys] keys the commit puts or deletes
  merged,    \* [Txns -> SUBSET Keys] keys the commit merges an operand into
  intended,  \* [Txns -> [Keys -> Nat]] what each put or deleted key is set to
  seen,      \* [Txns -> Nat] the value a write was derived from: the definition
             \* the writer or a migrator read, the count a read-merger read
  parents,   \* [Blocks -> SUBSET Blocks] parents each committed block recorded
  stale,     \* TRUE once a write committed over a definition replaced after it was read
  dupRefused,    \* TRUE once a merger was refused over writes identical to its own
  wrongReceipt,  \* TRUE once a read-merger committed over a count that moved
  needlessRefusal, \* TRUE once a blind increment was refused that could have committed
  cbase,     \* ghost: what the last put, delete or range delete stored in the counter
  cepoch,    \* ghost: the sequence it committed at
  cinc       \* ghost: commit sequences of the increments counted on top of it

vars == <<clock, store, latest, replaced, phase, snap, tracked, runs, written, merged,
          intended, seen, parents, stale, dupRefused, wrongReceipt, needlessRefusal,
          cbase, cepoch, cinc>>

Stored == {k \in Keys : store[k] # Absent}

\* The head set a scan of S derives: a stored head key no stored marker
\* names as a parent.
Heads(S) ==
  {b \in Blocks : HeadKey(b) \in S /\ ~\E c \in Blocks : MarkerKey(b, c) \in S}

Superseded(S) ==
  {b \in Blocks : HeadKey(b) \in S /\ \E c \in Blocks : MarkerKey(b, c) \in S}

----------------------------------------------------------------------------
\* One forward scan over the snapshot S, from the first key of range lo
\* through the last key of range hi.

\* The keys it yields.
Yield(S, lo, hi) == {k \in S : lo <= k[1] /\ k[1] <= hi}

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
  /\ replaced  = [k \in Keys |-> 0]
  /\ phase     = [t \in Txns |-> "idle"]
  /\ snap      = [t \in Txns |-> 0]
  /\ tracked   = [t \in Txns |-> {}]
  /\ runs      = [t \in Txns |-> {}]
  /\ written   = [t \in Txns |-> {}]
  /\ merged    = [t \in Txns |-> {}]
  /\ intended  = [t \in Txns |-> [k \in Keys |-> Absent]]
  /\ seen      = [t \in Txns |-> 0]
  /\ parents   = [b \in Blocks |-> {}]
  /\ stale     = FALSE
  /\ dupRefused      = FALSE
  /\ wrongReceipt    = FALSE
  /\ needlessRefusal = FALSE
  /\ cbase     = Absent
  /\ cepoch    = 0
  /\ cinc      = {}

\* The remote block's parents are fixed by its content, not by the local
\* heads; the scan is the head-set read the merge path makes. A block already
\* stored is not merged again, which a point read of its key decides: the
\* blockstore reads whether a block is stored in the transaction that puts
\* it.
BeginMerger(m) ==
  LET heads   == Yield(Stored, HeadRange, HeadRange)
      markers == Yield(Stored, MarkerRange, MarkerRange)
      keys    == IF BlockKey(Remote) \in Stored THEN {}
                 ELSE {HeadKey(Remote), BlockKey(Remote)}
                      \cup {MarkerKey(p, Remote) : p \in RemoteParents}
  IN /\ tracked'  = [tracked EXCEPT ![m] =
                      {BlockKey(Remote)} \cup ScanReads(heads) \cup ScanReads(markers)]
     /\ runs'     = [runs EXCEPT ![m] = Stretch(heads) \cup Stretch(markers)]
     /\ written'  = [written EXCEPT ![m] = keys]
     /\ intended' = [intended EXCEPT ![m] = [k \in Keys |-> IF k \in keys THEN 1 ELSE Absent]]
     /\ UNCHANGED <<merged, seen>>

BeginIncrementer(i) ==
  /\ merged' = [merged EXCEPT ![i] = {CounterKey}]
  /\ UNCHANGED <<tracked, runs, written, intended, seen>>

\* Transaction::get on the counter, then an increment merged into it. The
\* receipt, the count read plus one, is kept in `seen`: no other transaction
\* writes it, so as a key it would add no conflict.
BeginReadMerger(r) ==
  /\ tracked' = [tracked EXCEPT ![r] = {CounterKey}]
  /\ merged'  = [merged EXCEPT ![r] = {CounterKey}]
  /\ seen'    = [seen EXCEPT ![r] = store[CounterKey]]
  /\ UNCHANGED <<runs, written, intended>>

BeginRebaser(r) ==
  /\ written'  = [written EXCEPT ![r] = {CounterKey}]
  /\ merged'   = [merged EXCEPT ![r] = {CounterKey}]
  /\ intended' = [intended EXCEPT ![r] = [k \in Keys |-> IF k = CounterKey THEN 1 ELSE Absent]]
  /\ UNCHANGED <<tracked, runs, seen>>

BeginResetter(r) ==
  /\ written'  = [written EXCEPT ![r] = {CounterKey}]
  /\ intended' = [intended EXCEPT ![r] = [k \in Keys |-> Absent]]
  /\ UNCHANGED <<tracked, runs, merged, seen>>

\* One stream from the head range through the definition: its stretch starts
\* in the head prefix and ends on the definition.
BeginMigrator(g) ==
  LET walk == Yield(Stored, HeadRange, DefRange)
  IN /\ tracked'  = [tracked EXCEPT ![g] = ScanReads(walk)]
     /\ runs'     = [runs EXCEPT ![g] = Stretch(walk)]
     /\ written'  = [written EXCEPT ![g] = {DefKey}]
     /\ intended' = [intended EXCEPT ![g] =
                      [k \in Keys |-> IF k = DefKey THEN store[DefKey] + 1 ELSE Absent]]
     /\ seen'     = [seen EXCEPT ![g] = store[DefKey]]
     /\ UNCHANGED merged

BeginAppender(a) ==
  LET heads   == Yield(Stored, HeadRange, HeadRange)
      markers == Yield(Stored, MarkerRange, MarkerRange)
      keys    == {HeadKey(a), BlockKey(a)} \cup {MarkerKey(h, a) : h \in Heads(Stored)}
  IN /\ tracked'  = [tracked EXCEPT ![a] = ScanReads(heads) \cup ScanReads(markers)]
     /\ runs'     = [runs EXCEPT ![a] = Stretch(heads) \cup Stretch(markers)]
     /\ written'  = [written EXCEPT ![a] = keys]
     /\ intended' = [intended EXCEPT ![a] = [k \in Keys |-> IF k \in keys THEN 1 ELSE Absent]]
     /\ UNCHANGED <<merged, seen>>

\* Enabled once something is reclaimable, as the real sweep is a no-op
\* otherwise. One head per pass, chosen freely, with the markers against it
\* the scan yielded: a marker an open append is about to write is not in
\* the snapshot and is not touched.
BeginPruner ==
  LET heads   == Yield(Stored, HeadRange, HeadRange)
      markers == Yield(Stored, MarkerRange, MarkerRange)
  IN /\ \E b \in Superseded(Stored) :
          written' = [written EXCEPT ![Pruner] =
                       {HeadKey(b)} \cup {m \in markers : m[2] = b}]
     /\ intended' = [intended EXCEPT ![Pruner] = [k \in Keys |-> Absent]]
     /\ tracked'  = [tracked EXCEPT ![Pruner] = ScanReads(heads) \cup ScanReads(markers)]
     /\ runs'     = [runs EXCEPT ![Pruner] = Stretch(heads) \cup Stretch(markers)]
     /\ UNCHANGED <<merged, seen>>

\* Transaction::observe on the definition, then a document carrying it.
BeginWriter ==
  /\ tracked'  = [tracked EXCEPT ![Writer] = {DefKey}]
  /\ written'  = [written EXCEPT ![Writer] = {DocKey}]
  /\ intended' = [intended EXCEPT ![Writer] =
                   [k \in Keys |-> IF k = DocKey THEN store[DefKey] ELSE Absent]]
  /\ seen'     = [seen EXCEPT ![Writer] = store[DefKey]]
  /\ UNCHANGED <<runs, merged>>

BeginPatcher ==
  /\ written'  = [written EXCEPT ![Patcher] = {DefKey}]
  /\ intended' = [intended EXCEPT ![Patcher] =
                   [k \in Keys |-> IF k = DefKey THEN store[DefKey] + 1 ELSE Absent]]
  /\ UNCHANGED <<tracked, runs, merged, seen>>

Begin(t) ==
  /\ phase[t] = "idle"
  /\ phase' = [phase EXCEPT ![t] = "open"]
  /\ snap'  = [snap EXCEPT ![t] = clock]
  /\ CASE t \in Appenders    -> BeginAppender(t)
       [] t = Pruner         -> BeginPruner
       [] t = Writer         -> BeginWriter
       [] t = Patcher        -> BeginPatcher
       [] t \in Mergers      -> BeginMerger(t)
       [] t \in Incrementers -> BeginIncrementer(t)
       [] t \in ReadMergers  -> BeginReadMerger(t)
       [] t \in Rebasers     -> BeginRebaser(t)
       [] t \in Resetters    -> BeginResetter(t)
       [] t \in Migrators    -> BeginMigrator(t)
  /\ UNCHANGED <<clock, store, latest, replaced, parents, stale, dupRefused, wrongReceipt,
                 needlessRefusal, cbase, cepoch, cinc>>

----------------------------------------------------------------------------
\* The commit, transcribed.

\* IsolationLevel::validates_every_read.
EveryRead == Level \in {"RepeatableRead", "Serializable", "DefraLevel"}

\* No get_for_update in this workload.
ForUpdate(t) == {}

\* KeyClass::ContentAddressed, applied at DefraLevel: a key validated nowhere.
\* A read of it records nothing, and none of the checks below looks at it.
ContentAddressed(k) == Level = "DefraLevel" /\ k[1] \in ContentAddressedRanges

\* Transaction::validation_set: the recorded reads the level validates.
ValidatedReads(t) ==
  {k \in tracked[t] :
     /\ ~ContentAddressed(k)
     /\ IF EveryRead THEN TRUE
        ELSE IF Level = "ReadCommitted" THEN k \in written[t]
        ELSE k \in ForUpdate(t) \/ k \in written[t]}

\* scan_range::cover: every written or merged key inside a stretch a scan
\* walked joins the reads. Each read is already anchored at the begin
\* snapshot, so the re-anchoring `cover` also performs is the identity here.
\* policy::run_is_commutative: at DefraLevel a stretch whose two ends lie in
\* one declared range is dropped before cover sees it.
Commutative(s) ==
  /\ Level = "DefraLevel"
  /\ IF Mutant = "PolicyIgnoresRange"
       THEN s[1][1] \in CommutativeRanges \/ s[2][1] \in CommutativeRanges
       ELSE s[1][1] \in CommutativeRanges /\ s[2][1] = s[1][1]
CoveredRuns(t) == {s \in runs[t] : ~Commutative(s)}

Walked(t, k) == \E s \in CoveredRuns(t) : KeyLeq(s[1], k) /\ KeyLeq(k, s[2])

Reads(t) ==
  ValidatedReads(t) \cup {k \in (written[t] \cup merged[t]) : Walked(t, k) /\ ~ContentAddressed(k)}

\* Engine::commit_locked, the write loop: a merged key takes the blind-merge
\* path only when the transaction did not read it, the read loop having
\* validated it, and the batch neither puts nor deletes it (`Replaced`), its
\* put being validated in this loop and never elided. Here each key is
\* validated by exactly one of the three checks below; the engine checks a
\* put and the merge on top of it one after the other, to the same verdict.
BlindMerged(t) ==
  merged[t] \ ((IF Mutant = "ReadMergeBlind" THEN {} ELSE Reads(t))
               \cup (IF Mutant = "PutMergeBlind" THEN {} ELSE written[t]))

\* Engine::commit_locked, the read loop: a read aborts on any newer write.
ReadConflict(t) == \E k \in Reads(t) \ BlindMerged(t) : latest[k] > snap[t]

\* write_matches_committed: the write stores what the key already holds, and
\* the batch merges nothing on top of it.
Elided(t, k) ==
  /\ intended[t][k] = store[k]
  /\ k \notin merged[t] \/ Mutant = "PutMergeElides"

\* Engine::commit_locked, the write loop with `writes_at` the begin snapshot:
\* a written key not among the reads aborts on a newer write, unless the
\* write is elided.
WriteConflict(t) ==
  \E k \in written[t] \ (Reads(t) \cup BlindMerged(t)) :
     ~ContentAddressed(k) /\ latest[k] > snap[t] /\ ~Elided(t, k)

\* The same loop for a key the commit only merges into: a merge is never
\* elided. At DefraLevel (IsolationLevel::blind_merges_commute) it aborts only
\* on a newer write that replaced the key (newest_terminator_seq_above),
\* walking past newer operands.
MergeConflict(t) ==
  \E k \in BlindMerged(t) :
     /\ ~ContentAddressed(k)
     /\ IF Level = "DefraLevel"
          THEN Mutant # "MergeIgnoresReplacement" /\ replaced[k] > snap[t]
          ELSE latest[k] > snap[t]

Conflicts(t) == ReadConflict(t) \/ WriteConflict(t) \/ MergeConflict(t)

\* A put or delete first, then a merge on top of what it left.
Applied(t, k) ==
  IF k \in written[t] THEN intended[t][k] + (IF k \in merged[t] THEN 1 ELSE 0)
  ELSE IF k \in merged[t] THEN store[k] + 1
  ELSE store[k]

\* The counter's contract, kept apart from the engine's bookkeeping (latest,
\* replaced) so that a slip there shows up as a wrong value. A put or delete
\* of the counter starts an epoch at the value it stores, with the merge its
\* own batch puts on top counted in it, and discards only the increments it
\* saw: one committed after its snapshot stays counted although the put
\* erased it from the store. An increment counts if no put, delete or range
\* delete committed after it began.
Count(t, n) ==
  IF CounterKey \in written[t]
    THEN /\ cbase'  = intended[t][CounterKey]
         /\ cepoch' = n
         /\ cinc'   = {s \in cinc : s > snap[t]}
                      \cup (IF CounterKey \in merged[t] THEN {n} ELSE {})
  ELSE IF CounterKey \in merged[t]
    THEN /\ cinc' = IF snap[t] >= cepoch THEN cinc \cup {n} ELSE cinc
         /\ UNCHANGED <<cbase, cepoch>>
  ELSE UNCHANGED <<cbase, cepoch, cinc>>

Commit(t) ==
  /\ phase[t] = "open"
  /\ IF Conflicts(t)
       THEN /\ phase' = [phase EXCEPT ![t] = "aborted"]
            /\ needlessRefusal' = (needlessRefusal \/ (t \in Incrementers /\ snap[t] >= cepoch))
            /\ dupRefused' = (dupRefused \/
                              (t \in Mergers /\ \A k \in written[t] :
                                  latest[k] > snap[t] => store[k] = intended[t][k]))
            /\ UNCHANGED <<clock, store, latest, replaced, parents, stale, wrongReceipt,
                           cbase, cepoch, cinc>>
       ELSE /\ phase'    = [phase EXCEPT ![t] = "committed"]
            /\ clock'    = clock + 1
            /\ store'    = [k \in Keys |-> Applied(t, k)]
            /\ latest'   = [k \in Keys |->
                              IF k \in written[t] \cup merged[t] THEN clock + 1 ELSE latest[k]]
            /\ replaced' = [k \in Keys |-> IF k \in written[t] THEN clock + 1 ELSE replaced[k]]
            /\ parents'  = IF t \in Appenders
                             THEN [parents EXCEPT ![t] = {h \in Blocks : MarkerKey(h, t) \in written[t]}]
                             ELSE IF t \in Mergers /\ written[t] # {}
                             THEN [parents EXCEPT ![Remote] = RemoteParents]
                             ELSE parents
            /\ stale'    = (stale \/ ((t = Writer \/ t \in Migrators) /\ store[DefKey] # seen[t]))
            /\ wrongReceipt' = (wrongReceipt \/ (t \in ReadMergers /\ store[CounterKey] # seen[t]))
            /\ Count(t, clock + 1)
            /\ UNCHANGED <<needlessRefusal, dupRefused>>
  /\ UNCHANGED <<snap, tracked, runs, written, intended, merged, seen>>

\* Db::delete_range over the counter's range: a plain write, applied at once
\* and validated against nothing. A covering range tombstone is the newest
\* write of each key it covers (latest_version_in_view) and replaces each
\* one (newest_terminator_seq_above). Applied at once, it saw every
\* increment it discards.
Clear(c) ==
  LET covered == {k \in Keys : k[1] = CounterRange}
  IN /\ phase[c]  = "idle"
     /\ phase'    = [phase EXCEPT ![c] = "committed"]
     /\ clock'    = clock + 1
     /\ store'    = [k \in Keys |-> IF k \in covered THEN Absent ELSE store[k]]
     /\ latest'   = [k \in Keys |-> IF k \in covered THEN clock + 1 ELSE latest[k]]
     /\ replaced' = [k \in Keys |->
                       IF k \in covered /\ Mutant # "RangeDeleteNotReplacement"
                       THEN clock + 1 ELSE replaced[k]]
     /\ cbase'    = Absent
     /\ cepoch'   = clock + 1
     /\ cinc'     = {}
     /\ UNCHANGED <<snap, tracked, runs, written, intended, merged, seen, parents, stale,
                    dupRefused, wrongReceipt, needlessRefusal>>

Next == \/ \E t \in Txns \ Clearers : Begin(t) \/ Commit(t)
        \/ \E c \in Clearers : Clear(c)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----------------------------------------------------------------------------
TypeOK ==
  /\ clock \in Nat
  /\ store \in [Keys -> Nat]
  /\ latest \in [Keys -> Nat]
  /\ replaced \in [Keys -> Nat]
  /\ phase \in [Txns -> {"idle", "open", "committed", "aborted"}]
  /\ \A t \in Txns : tracked[t] \subseteq Keys /\ written[t] \subseteq Keys /\ merged[t] \subseteq Keys
  /\ \A t \in Txns : \A s \in runs[t] : s \in Keys \X Keys /\ KeyLeq(s[1], s[2])
  /\ seen \in [Txns -> Nat]
  /\ cbase \in Nat /\ cepoch \in Nat /\ cinc \subseteq Nat
  /\ stale \in BOOLEAN

\* THE HEADLINE for the head set. An append that did its scan, built its
\* block and asked to commit is never turned away by a sweep that reclaimed
\* keys its scan yielded: the live set it derived was unchanged by that.
INV_AppendsCommit == \A a \in Appenders : phase[a] # "aborted"

\* THE HEADLINE for point reads. No write derived from the definition (a
\* document, a migration) commits against a definition that was replaced
\* after it was read.
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
\* must be: an append may have superseded the block it applies and the sweep
\* reclaimed that head, so writing the head key back would resurrect a
\* superseded head (INV_HeadsExact).
INV_DuplicateMergesCommit == ~dupRefused

\* The counter holds the value the last put, delete or range delete stored,
\* plus one for every increment counted since (Count). A put or delete that
\* commits over an increment it did not see loses that increment; an
\* increment that commits over a reset it did not see survives the reset.
\* Either way the store and the contract part.
INV_CounterExact == store[CounterKey] = cbase + Cardinality(cinc)

\* A read-merger commits only while the count it read is still the count:
\* its receipt is then the count its own merge produced.
INV_ReceiptsExact == ~wrongReceipt

\* A blind increment is refused only when committing it would break the
\* counter, a put, delete or range delete having committed after it began,
\* so concurrent increments never refuse each other.
INV_IncrementsCommitUnlessReplaced == ~needlessRefusal

\* State constraints that spend a config's states on one workload: the
\* transactions of every other one stay idle.
CounterWorkloadOnly ==
  \A t \in Appenders \cup {Pruner, Writer, Patcher} \cup Mergers \cup Migrators :
     phase[t] = "idle"
DefinitionWorkloadOnly ==
  \A t \in Appenders \cup {Pruner} \cup Mergers \cup CounterTxns : phase[t] = "idle"
\* The writer and the patcher touch no key of the DAG and read none through a
\* scan, so idling them loses no interleaving of the head set.
HeadsWorkloadOnly ==
  \A t \in {Writer, Patcher} \cup CounterTxns \cup Migrators : phase[t] = "idle"

\* Under the level that refuses no append, every append lands.
EventuallyAllAppendsCommit == <>[](\A a \in Appenders : phase[a] = "committed")

====
