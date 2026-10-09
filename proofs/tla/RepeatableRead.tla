---- MODULE RepeatableRead ----
\* What an optimistic commit validates at each isolation level, and at
\* DefraLevel for each key class, checked against the workloads a Merkle-DAG
\* CRDT store and its callers run on it. The commit rule, the key layout and
\* the variables live in RepeatableReadCommit.tla, which says which rules are
\* transcribed from the code and which the plan specifies before code.
\*
\* Reads are performed when a transaction begins. They are snapshot reads in
\* the engine, answered from the state at begin whenever they are issued, so
\* taking them at begin loses no interleaving; the one read served later is
\* a pessimistic get_for_update past the snapshot (Promote). A commit takes
\* one sequence here where the engine gives a batch one per operation; every
\* operation of a commit after the snapshot sorts above it and every one
\* before sorts at or below, which is all the check reads. A range delete
\* occurs only as a plain write, `Db::delete_range`:
\* `Transaction::delete_range` refuses one, so no commit batch carries it.
\*
\* THE FIRST WORKLOADS (#237), one transaction each.
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
\* DEFRALEVEL. RepeatableRead, relaxed for an optimistic transaction:
\* commutative prefixes (a stretch inside one records nothing), the
\* content-addressed class (E17), blind merges (a key the commit only merges
\* into aborts only on a newer put, delete or range delete), and the PLAN
\* mechanisms below. For a key merged into blind this is not snapshot
\* isolation: two transactions merging into it concurrently both commit.
\* What the model checks for such a key is the value it ends up holding.
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
\* THE LATER WORKLOADS (docs/plans/defralevel.md, section 3), one per
\* mechanism, each with its own Extras record below and configs of its own.
\* Each decider writes its decision into an output key only it writes, so it
\* is a writing transaction and its reads are validated.
\*   ContentAddressedWorkload [3.2, E17]
\*     Collector  reads the shared block (present), scans the pins with a
\*                plain scan and point-reads every hold; when nothing refers
\*                to the block it deletes it. Garbage collection.
\*     Linkers    read the block, put it again (or merge its own bytes into
\*                it) and pin it: a reference that re-puts what it refers to.
\*     Holder     reads the block and records whether it is present: 1, a
\*                reference that relies on the block's presence, or 2.
\*     INV_NoDanglingReference  a stored pin or reference names a stored block.
\*     INV_LinksCommit          two creates of one block both commit.
\*     INV_HoldsCurrent         a holder's record matches the block at commit.
\*   PartsWorkload [3.3, 3.4]
\*     PartReader    get_parts(part key, {1}); its decision is whether the key
\*                   exists and what part 1 holds.
\*     PartRewriter  get_parts(part key, {1}), then puts the whole value it read
\*                   with part 1 bumped: a decision on every part.
\*     PartWriters   one blind write each: an identical put, a put changing
\*                   part 2, a delete, or an operand touching part 1 or part 2.
\*     INV_PartsCurrent  no projected reader commits on changed inputs.
\*     INV_PartsRelaxed  a reader that found the key is not refused when every
\*                       newer write is an operand touching only part 2.
\*   ValueWorkload [3.5]
\*     ValueReader     reads the version key and decides on its value.
\*     VersionWriters  rewrite it with the same bytes, or toggle it (1, 2),
\*                     so a value can come back (ABA).
\*     INV_ValueReadsCurrent        no reader commits over a different value.
\*     INV_IdenticalRewritesCommit  no reader is refused while the value is the
\*                                  one it read. A liveness property, kept as
\*                                  an invariant on refusals.
\*   WriteFreeWorkload [3.8]
\*     ReadOnly    optimistic, reads both skew keys at its snapshot, writes
\*                 nothing.
\*     Promoter    pessimistic, reads skew key A at its snapshot, then skew key
\*                 B with get_for_update at a later horizon, writes nothing.
\*                 Its lock on B is not modelled: dropping it only adds
\*                 interleavings, and the RED needs none of them.
\*     SkewWriter  writes both keys, one more each.
\*     INV_WriteFreeCommits     a write-free DefraLevel transaction never
\*                              conflicts.
\*     INV_WriteFreeConsistent  every committed write-free transaction read one
\*                              point in time.
\*   LogWorkload, LogDecisionWorkload [3.2, 3.6]
\*     LogAppenders  append one entry each.
\*     LogReader     reads the head, appends, and stores the head it read as
\*                   its cursor. It does not see its own append.
\*     LogDecider    misuse: decides on how many entries the log holds.
\*     INV_LogNeverConflicts    no appender or log reader is refused.
\*     INV_LogDense             the log holds entries 1..head and nothing more.
\*     INV_NoPhantomAppend      every entry a reader saw is in the log at its
\*                              commit, at the position it saw.
\*     INV_LogDecisionsCurrent  no decision on a log read went stale.
\*   TallyWorkload [3.2, E11]
\*     TallyMergers  merge into a key of a commutative prefix, then scan the
\*                   prefix: the merge stays blind inside the stretch.
\*     INV_TallyMergesCommit, INV_TallyExact  none is refused, none is lost.
\*   OwnWritesWorkload [3.9]
\*     OwnWriters  two operations on one key (merge, put, delete, in some
\*                 order), then a read of it.
\*     INV_ReadYourOwnWrites  the value a commit leaves is the value its
\*                            transaction read back.
\*   ScanWorkload [3.15]
\*     Checker  a validated scan of the grant range; it decides on the set
\*              of grants.
\*     Revoker  deletes the grant there; Granter puts a new one (a phantom).
\*     INV_ScanDecisionsCurrent  no checker commits over a changed range.
\*   Every GREEN, the first workloads' included:
\*     INV_ReasonsExact  every abort's reason names a key, what the
\*                       transaction did with it, and a write newer than
\*                       the anchor whose kind is `theirs`, whose sequence
\*                       is `latest_seq`, and which can decide that access
\*                       [3.14].
\*
\* MUTANTS. `Mutant` breaks one line of the rule, and each has a RED config:
\* that is what shows the line keeps a GREEN config green.
\*   ReadMergeBlind             a merged key the transaction read is
\*                              validated as a blind merge.
\*                              INV_ReceiptsExact RED.
\*   PutMergeBlind              a merged key the batch also puts is validated
\*                              as a blind merge.  INV_CounterExact RED.
\*   PutMergeElides             an identical put is elided although its batch
\*                              merges on top.     INV_CounterExact RED.
\*   MergeIgnoresReplacement    a blind merge conflicts with nothing.
\*                              INV_CounterExact RED.
\*   RangeDeleteNotReplacement  a range tombstone does not replace the keys it
\*                              covers.            INV_CounterExact RED.
\*   PolicyIgnoresRange         a stretch is dropped when either end lies in a
\*                              commutative prefix, wherever it runs.
\*                              INV_NoStaleDefinition RED.
\*   CaDeleteExempt             a content-addressed delete is not validated
\*                              (before E17): a collection races a pin.
\*                              INV_NoDanglingReference RED.
\*   PresenceReadFull           a content-addressed read that found the key is
\*                              validated in full by sequence, its own put
\*                              notwithstanding: two creates of one block.
\*                              INV_LinksCommit RED.
\*   PresenceUnchecked          a content-addressed read that found the key is
\*                              not validated (before E17).
\*                              INV_HoldsCurrent RED.
\*   PartsIgnorePut             a put or delete does not change the parts.
\*   PartsIgnoreTouch           an operand never changes them.
\*   PartsNoAbsentFallback      a projected read that found nothing stays
\*                              projected.
\*   PartsNoPutFallback         a projected read of a key the transaction puts
\*                              stays projected: a lost update.
\*   PartsNamesOther            the reader names part 2 and decides on part 1
\*                              (caller misuse).   All five INV_PartsCurrent RED.
\*   SeqOnlyValidation          DefraLevel compares sequences, not values.
\*                              INV_IdenticalRewritesCommit RED.
\*   WriteFreePessimistic       the write-free exemption applies to a
\*                              pessimistic transaction whose get_for_update
\*                              read past its snapshot (rejected by the plan).
\*                              INV_WriteFreeConsistent RED.
\*   OwnAppendVisible           a log reader sees its own append at the next
\*                              position.          INV_NoPhantomAppend RED.
\*   MergeBeforeScanReadsBase   a scan over a key the transaction merged into
\*                              records the base read (before E11).
\*                              INV_TallyMergesCommit RED.
\*   PutsBeforeMerges           a commit applies puts before merges whatever
\*                              their order (the 0.1.x engine).
\*   OwnMergesInvisible         a read ignores the transaction's own merges.
\*                              Both INV_ReadYourOwnWrites RED.
\*   ReasonNewestWrite          a reason names the key's newest write, not the
\*                              one that decided.  INV_ReasonsExact RED.
\*   PlainScanDecides           a checker decides on a plain scan.
\*                              INV_ScanDecisionsCurrent RED.
\* Two REDs are misuse, not mutants: Red_DecideOnLogRead (a decision on a
\* Log read, INV_LogDecisionsCurrent) and Red_Parts_RepeatableRead (get_parts
\* at RepeatableRead is a get, INV_PartsRelaxed).
\*
\* LEAN, for every size (proofs/lean/Regolith):
\*   Validation.lean     ordinary_serial, value_serial, contentAddressed_serial,
\*                       parts_serial, scan_serial, exempt_serial (Log reads,
\*                       commutative stretches, empty parts), blindMerge_serial,
\*                       and all_classes_serial: a history whose every commit
\*                       passed its class's rule equals the same transactions
\*                       run one at a time in commit order. Each rests on its
\*                       rule's soundness lemma: full_current, value_current,
\*                       presence_current, parts_current, scan_current; the
\*                       content-addressed one on ca_put_idempotent and
\*                       ca_commit_point.
\*   Relaxations.lean    blindMerge_commutes, identical_rewrite,
\*                       commutative_union, appends_advance_head and
\*                       appends_keep_dense (INV_LogDense),
\*                       writeFree_at_snapshot (INV_WriteFreeConsistent); the
\*                       REDs exempt_decision_breaks_serial
\*                       (Red_DecideOnLogRead, Red_PartsNamesOther) and
\*                       promoted_read_skew (Red_WriteFreePessimistic).
\*   MergeOperator.lean  fold_eq_grouping, fold_eq_any_grouping and
\*                       steps_preserve_fold (an exact partial_merge folds to
\*                       full_merge in any grouping), groupings_agree,
\*                       touches_law and touches_survives_compaction (an
\*                       operand touching no named part leaves those parts
\*                       unchanged), inexact_breaks_fold (the RED), and
\*                       part_operator_* (this model's part operand keeps the
\*                       contract).
\* What Lean does not cover: the interleavings (TLC does), and the
\* invariants that tie a workload's protocol together (INV_NoDanglingReference
\* needs the collector, the pins and the holds at once).

EXTENDS RepeatableReadCommit

\* The Extras a config names (Extras <- ...): which ids play which role.
NoExtras == [r \in RoleNames |-> {}]
\* The content-addressed collection: a collector, two linkers, a holder.
ContentAddressedWorkload ==
  [NoExtras EXCEPT !["Collectors"] = {20}, !["Linkers"] = {21, 22}, !["Holders"] = {23}]
\* Projected reads: a part reader, a rewriter, two part writers.
PartsWorkload ==
  [NoExtras EXCEPT !["PartReaders"] = {30}, !["PartRewriters"] = {31},
                   !["PartWriters"] = {32, 33}]
\* Value-validated reads: a reader and two version writers.
ValueWorkload ==
  [NoExtras EXCEPT !["ValueReaders"] = {40}, !["VersionWriters"] = {41, 42}]
\* Write-free transactions: a read-only, a promoter and a skew writer.
WriteFreeWorkload ==
  [NoExtras EXCEPT !["ReadOnlys"] = {50}, !["Promoters"] = {51}, !["SkewWriters"] = {52}]
\* The log: two appenders and a reader that appends too.
LogWorkload ==
  [NoExtras EXCEPT !["LogAppenders"] = {60, 61}, !["LogReaders"] = {62}]
\* The log misuse: an appender and a decider on the log's length.
LogDecisionWorkload ==
  [NoExtras EXCEPT !["LogAppenders"] = {60}, !["LogDeciders"] = {63}]
\* E11: two merges into one commutative key, each then scanning its prefix.
TallyWorkload ==
  [NoExtras EXCEPT !["TallyMergers"] = {70, 71}]
\* Read-your-own-writes: two transactions with two operations each.
OwnWritesWorkload ==
  [NoExtras EXCEPT !["OwnWriters"] = {80, 81}]
\* Validated scans: a checker, a revoker and a granter.
ScanWorkload ==
  [NoExtras EXCEPT !["Checkers"] = {90}, !["Revokers"] = {91}, !["Granters"] = {92}]

\* The head set a scan of S derives: a stored head key no stored marker
\* names as a parent.
Heads(S) ==
  {b \in Blocks : HeadKey(b) \in S /\ ~\E c \in Blocks : MarkerKey(b, c) \in S}

\* The blocks a scan of S finds superseded: a stored head some stored
\* marker names as a parent, which the sweep may reclaim.
Superseded(S) ==
  {b \in Blocks : HeadKey(b) \in S /\ \E c \in Blocks : MarkerKey(b, c) \in S}

----------------------------------------------------------------------------
\* The start: nothing committed, every transaction idle, every key at its
\* initial value (InitStore), no history and no flag.
Init ==
  /\ clock     = 0
  /\ store     = InitStore
  /\ hist      = {}
  /\ phase     = [t \in Txns |-> "idle"]
  /\ snap      = [t \in Txns |-> 0]
  /\ tracked   = [t \in Txns |-> {}]
  /\ runs      = [t \in Txns |-> {}]
  /\ written   = [t \in Txns |-> {}]
  /\ merged    = [t \in Txns |-> {}]
  /\ intended  = [t \in Txns |-> [k \in Keys |-> Absent]]
  /\ seen      = [t \in Txns |-> 0]
  /\ ops       = [t \in Txns |-> <<>>]
  /\ forUpdate = [t \in Txns |-> {}]
  /\ flags     = {}
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
     /\ UNCHANGED <<merged, seen, ops>>

\* An increment merged into the counter, reading nothing.
BeginIncrementer(i) ==
  /\ merged' = [merged EXCEPT ![i] = {CounterKey}]
  /\ UNCHANGED <<tracked, runs, written, intended, seen, ops>>

\* Transaction::get on the counter, then an increment merged into it. The
\* receipt, the count read plus one, is kept in `seen`: no other transaction
\* writes it, so as a key it would add no conflict.
BeginReadMerger(r) ==
  /\ tracked' = [tracked EXCEPT ![r] = {CounterKey}]
  /\ merged'  = [merged EXCEPT ![r] = {CounterKey}]
  /\ seen'    = [seen EXCEPT ![r] = store[CounterKey]]
  /\ UNCHANGED <<runs, written, intended, ops>>

\* The counter put to 1 and an increment merged on top, in one batch.
BeginRebaser(r) ==
  /\ written'  = [written EXCEPT ![r] = {CounterKey}]
  /\ merged'   = [merged EXCEPT ![r] = {CounterKey}]
  /\ intended' = [intended EXCEPT ![r] = [k \in Keys |-> IF k = CounterKey THEN 1 ELSE Absent]]
  /\ UNCHANGED <<tracked, runs, seen, ops>>

\* A delete of the counter.
BeginResetter(r) ==
  /\ written'  = [written EXCEPT ![r] = {CounterKey}]
  /\ intended' = [intended EXCEPT ![r] = [k \in Keys |-> Absent]]
  /\ UNCHANGED <<tracked, runs, merged, seen, ops>>

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
     /\ UNCHANGED <<merged, ops>>

\* Scan the heads and markers, then write its own head, its block, and a
\* marker naming itself against every live head.
BeginAppender(a) ==
  LET heads   == Yield(Stored, HeadRange, HeadRange)
      markers == Yield(Stored, MarkerRange, MarkerRange)
      keys    == {HeadKey(a), BlockKey(a)} \cup {MarkerKey(h, a) : h \in Heads(Stored)}
  IN /\ tracked'  = [tracked EXCEPT ![a] = ScanReads(heads) \cup ScanReads(markers)]
     /\ runs'     = [runs EXCEPT ![a] = Stretch(heads) \cup Stretch(markers)]
     /\ written'  = [written EXCEPT ![a] = keys]
     /\ intended' = [intended EXCEPT ![a] = [k \in Keys |-> IF k \in keys THEN 1 ELSE Absent]]
     /\ UNCHANGED <<merged, seen, ops>>

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
     /\ UNCHANGED <<merged, seen, ops>>

\* Transaction::observe on the definition, then a document carrying it.
BeginWriter ==
  /\ tracked'  = [tracked EXCEPT ![Writer] = {DefKey}]
  /\ written'  = [written EXCEPT ![Writer] = {DocKey}]
  /\ intended' = [intended EXCEPT ![Writer] =
                   [k \in Keys |-> IF k = DocKey THEN store[DefKey] ELSE Absent]]
  /\ seen'     = [seen EXCEPT ![Writer] = store[DefKey]]
  /\ UNCHANGED <<runs, merged, ops>>

\* The definition replaced by the next version.
BeginPatcher ==
  /\ written'  = [written EXCEPT ![Patcher] = {DefKey}]
  /\ intended' = [intended EXCEPT ![Patcher] =
                   [k \in Keys |-> IF k = DefKey THEN store[DefKey] + 1 ELSE Absent]]
  /\ UNCHANGED <<tracked, runs, merged, seen, ops>>

----------------------------------------------------------------------------
\* The later workloads' begins. Do(t, ...) records, in one step, the point
\* reads, scan stretches, written keys, merged keys and intended values of
\* transaction t; `it` maps each written key to what it stores.

\* No written key.
NoIntent == [k \in {} |-> Absent]
\* `it` as a function over every key, absent where it says nothing.
Intend(it) == [k \in Keys |-> IF k \in DOMAIN it THEN it[k] ELSE Absent]

\* Record t's reads, stretches, written and merged keys, and intended values.
Do(t, rd, rn, wr, mg, it) ==
  /\ tracked'  = [tracked EXCEPT ![t] = rd]
  /\ runs'     = [runs EXCEPT ![t] = rn]
  /\ written'  = [written EXCEPT ![t] = wr]
  /\ merged'   = [merged EXCEPT ![t] = mg]
  /\ intended' = [intended EXCEPT ![t] = Intend(it)]

\* Enabled once the shared block is stored and nothing refers to it at the
\* snapshot. The pin scan is a plain scan, and an empty one records no
\* stretch: the collector relies on every pinner putting the block again,
\* which its validated delete sees. A hold is a point read of a key the
\* collector must see change, so it is validated in full.
BeginCollector(c) ==
  /\ store[Shared] # Absent
  /\ Yield(Stored, PinRange, PinRange) = {}
  /\ \A h \in Holders : store[HoldKey(h)] # 1
  /\ Do(c, {Shared} \cup {HoldKey(h) : h \in Holders}, {}, {Shared}, {}, Shared :> Absent)
  /\ UNCHANGED <<seen, ops>>

\* A pin re-puts the block it refers to, or merges the block's own bytes
\* into it (an idempotent operand): either way the commit stores the block.
BeginLinker(l) ==
  \E how \in {"put", "merge"} :
    /\ Do(l, {Shared}, {},
          {PinKey(l)} \cup (IF how = "put" THEN {Shared} ELSE {}),
          IF how = "merge" THEN {Shared} ELSE {},
          (PinKey(l) :> 1) @@ (Shared :> 1))
    /\ ops' = [ops EXCEPT ![l] = <<how>>]
    /\ UNCHANGED seen

\* The holder's record: 1 refers to the block, 2 says it is missing.
BeginHolder(h) ==
  /\ Do(h, {Shared}, {}, {HoldKey(h)}, {},
        HoldKey(h) :> IF store[Shared] # Absent THEN 1 ELSE 2)
  /\ UNCHANGED <<seen, ops>>

\* The part reader's get_parts is recorded by role (PartRead); its decision,
\* part 1 as read, goes to its output key.
BeginPartReader(r) ==
  /\ Do(r, {}, {}, {OutKey(r)}, {}, OutKey(r) :> Part(store[PartKey], 1))
  /\ UNCHANGED <<seen, ops>>

\* The rewrite: part 1 one up, part 2 as read.
Rewrite(v) == PartValue(Part(v, 1) + 1, Part(v, 2))

\* get_parts(part key, {1}) (by role), then a put of the rewrite.
BeginPartRewriter(w) ==
  /\ Do(w, {}, {}, {PartKey}, {}, PartKey :> Rewrite(store[PartKey]))
  /\ UNCHANGED <<seen, ops>>

\* One blind write: the value read again ("same"), the value read with
\* part 2 one up ("other"), a delete, or an operand touching one part.
BeginPartWriter(w) ==
  \E op \in {"same", "other", "delete", "touch1", "touch2"} :
    /\ ops' = [ops EXCEPT ![w] = <<op>>]
    /\ IF op \in {"touch1", "touch2"}
         THEN Do(w, {}, {}, {}, {PartKey}, NoIntent)
         ELSE Do(w, {}, {}, {PartKey}, {},
                 PartKey :> CASE op = "same"   -> store[PartKey]
                              [] op = "other"  -> PartValue(Part(store[PartKey], 1),
                                                            Part(store[PartKey], 2) + 1)
                              [] op = "delete" -> Absent)
    /\ UNCHANGED seen

\* A read of the version key; its value goes to the output key.
BeginValueReader(r) ==
  /\ Do(r, {VersionKey}, {}, {OutKey(r)}, {}, OutKey(r) :> store[VersionKey])
  /\ UNCHANGED <<seen, ops>>

\* The version key holds 1 or 2; "other" toggles it.
BeginVersionWriter(w) ==
  \E op \in {"same", "other"} :
    /\ Do(w, {}, {}, {VersionKey}, {},
          VersionKey :> IF op = "same" THEN store[VersionKey] ELSE 3 - store[VersionKey])
    /\ UNCHANGED <<seen, ops>>

\* Both skew keys read at the snapshot, nothing written.
BeginReadOnly(r) ==
  /\ Do(r, {SkewA, SkewB}, {}, {}, {}, NoIntent)
  /\ UNCHANGED <<seen, ops>>

\* The read of B comes later, in Promote.
BeginPromoter(p) ==
  /\ Do(p, {SkewA}, {}, {}, {}, NoIntent)
  /\ UNCHANGED <<seen, ops>>

\* Both skew keys one more, blind.
BeginSkewWriter(w) ==
  /\ Do(w, {}, {}, {SkewA, SkewB}, {}, (SkewA :> store[SkewA] + 1) @@ (SkewB :> store[SkewB] + 1))
  /\ UNCHANGED <<seen, ops>>

\* An append records nothing at begin: its position is assigned at commit.
BeginLogAppender(a) ==
  /\ Do(a, {}, {}, {}, {}, NoIntent)
  /\ UNCHANGED <<seen, ops>>

\* The head it read becomes its cursor; its own append is not in the head.
BeginLogReader(r) ==
  /\ Do(r, {LogHead}, {}, {OutKey(r)}, {}, OutKey(r) :> store[LogHead])
  /\ UNCHANGED <<seen, ops>>

\* The head read (never validated) and written down as how many entries
\* the log holds: a decision on a Log read.
BeginLogDecider(d) ==
  /\ Do(d, {LogHead}, {}, {OutKey(d)}, {}, OutKey(d) :> store[LogHead])
  /\ UNCHANGED <<seen, ops>>

\* The merge comes first; the scan of the tally prefix then yields the key,
\* made visible by the transaction's own operand, as one stretch inside the
\* prefix. E11: the scan reads the operands-only key's base without
\* recording it (MUTANT MergeBeforeScanReadsBase records it).
BeginTallyMerger(m) ==
  /\ Do(m, IF Mutant = "MergeBeforeScanReadsBase" THEN {TallyKey} ELSE {},
        {<<TallyKey, TallyKey>>}, {}, {TallyKey}, NoIntent)
  /\ UNCHANGED <<seen, ops>>

\* The operation orders an own-writer may choose.
OpSeqs == {<<"merge", "put">>, <<"put", "merge">>, <<"delete", "merge">>,
           <<"merge", "merge">>, <<"merge", "delete">>}

\* An own-writer's buffered operations, as the commit sees them: the newest
\* put or delete decides what the key is set to, and the key is merged into
\* when the commit's last operation on it is a merge. Its read back depends
\* on the committed value only when it has no put or delete, and then it is
\* recorded as a read: reading a merged key makes the merge a
\* read-modify-write [3.9].
BeginOwnWriter(o) ==
  \E s \in OpSeqs :
    LET applied == IF Mutant = "PutsBeforeMerges" THEN PutsFirst(s) ELSE s
        reps    == SelectSeq(applied, LAMBDA x : x # "merge")
    IN /\ ops' = [ops EXCEPT ![o] = s]
       /\ Do(o, IF reps = <<>> THEN {OwnKey} ELSE {}, {},
             IF reps = <<>> THEN {} ELSE {OwnKey},
             IF applied[Len(applied)] = "merge" THEN {OwnKey} ELSE {},
             IF reps = <<>> THEN NoIntent
             ELSE OwnKey :> (IF reps[Len(reps)] = "put" THEN 5 ELSE Absent))
       /\ UNCHANGED seen

\* The checker's decision, the number of grants, goes to its output key. The
\* validated range is recorded by role (ScanDecider); the plain stretch is
\* recorded as for any scan.
BeginChecker(c) ==
  LET grants == Yield(Stored, AclRange, AclRange)
  IN /\ Do(c, {}, Stretch(grants), {OutKey(c)}, {}, OutKey(c) :> Cardinality(grants))
     /\ UNCHANGED <<seen, ops>>

\* The grant deleted.
BeginRevoker(r) ==
  /\ Do(r, {}, {}, {AclKey(1)}, {}, AclKey(1) :> Absent)
  /\ UNCHANGED <<seen, ops>>

\* A new grant put.
BeginGranter(g) ==
  /\ Do(g, {}, {}, {AclKey(2)}, {}, AclKey(2) :> 1)
  /\ UNCHANGED <<seen, ops>>

\* Transaction t begins: it takes its snapshot and records what its role
\* reads and writes.
Begin(t) ==
  /\ phase[t] = "idle"
  /\ phase' = [phase EXCEPT ![t] = "open"]
  /\ snap'  = [snap EXCEPT ![t] = clock]
  /\ CASE t \in Appenders      -> BeginAppender(t)
       [] t = Pruner           -> BeginPruner
       [] t = Writer           -> BeginWriter
       [] t = Patcher          -> BeginPatcher
       [] t \in Mergers        -> BeginMerger(t)
       [] t \in Incrementers   -> BeginIncrementer(t)
       [] t \in ReadMergers    -> BeginReadMerger(t)
       [] t \in Rebasers       -> BeginRebaser(t)
       [] t \in Resetters      -> BeginResetter(t)
       [] t \in Migrators      -> BeginMigrator(t)
       [] t \in Collectors     -> BeginCollector(t)
       [] t \in Linkers        -> BeginLinker(t)
       [] t \in Holders        -> BeginHolder(t)
       [] t \in PartReaders    -> BeginPartReader(t)
       [] t \in PartRewriters  -> BeginPartRewriter(t)
       [] t \in PartWriters    -> BeginPartWriter(t)
       [] t \in ValueReaders   -> BeginValueReader(t)
       [] t \in VersionWriters -> BeginVersionWriter(t)
       [] t \in ReadOnlys      -> BeginReadOnly(t)
       [] t \in Promoters      -> BeginPromoter(t)
       [] t \in SkewWriters    -> BeginSkewWriter(t)
       [] t \in LogAppenders   -> BeginLogAppender(t)
       [] t \in LogReaders     -> BeginLogReader(t)
       [] t \in LogDeciders    -> BeginLogDecider(t)
       [] t \in TallyMergers   -> BeginTallyMerger(t)
       [] t \in OwnWriters     -> BeginOwnWriter(t)
       [] t \in Checkers       -> BeginChecker(t)
       [] t \in Revokers       -> BeginRevoker(t)
       [] t \in Granters       -> BeginGranter(t)
  /\ UNCHANGED <<clock, store, hist, forUpdate, flags, parents, stale, dupRefused,
                 wrongReceipt, needlessRefusal, cbase, cepoch, cinc>>

\* A pessimistic promoter reads skew key B with get_for_update at the
\* current horizon, past its snapshot [3.8].
Promote(p) ==
  /\ phase[p] = "open"
  /\ forUpdate[p] = {}
  /\ forUpdate' = [forUpdate EXCEPT ![p] = {<<SkewB, clock>>}]
  /\ UNCHANGED <<clock, store, hist, phase, snap, tracked, runs, written, merged, intended,
                 seen, ops, flags, parents, stale, dupRefused, wrongReceipt,
                 needlessRefusal, cbase, cepoch, cinc>>

----------------------------------------------------------------------------
\* The ghosts the later workloads' invariants read, computed when a
\* transaction ends, from the history: what it read is the value at its
\* snapshot (ValueAt), what holds now is `store`.

\* What an own-writer read back: its operations folded onto the value at its
\* snapshot, in operation order [3.9]. MUTANT OwnMergesInvisible skips its
\* merges.
OwnRead(t) ==
  LET s == IF Mutant = "OwnMergesInvisible" THEN SelectSeq(ops[t], LAMBDA o : o # "merge")
           ELSE ops[t]
  IN Fold(s, ValueAt(OwnKey, snap[t]))

\* A part reader's decision inputs: whether the key exists, and part 1.
PartDecision(v) == <<v # Absent, Part(v, 1)>>

\* What a write-free transaction read of the two skew keys, B at the horizon
\* its get_for_update was served at, if any.
SkewSeen(t) ==
  <<ValueAt(SkewA, snap[t]),
    IF forUpdate[t] = {} THEN ValueAt(SkewB, snap[t])
    ELSE ValueAt(SkewB, (CHOOSE f \in forUpdate[t] : TRUE)[2])>>

\* Some single point in time between its snapshot and now shows both values
\* it read.
Consistent(t) ==
  \E s \in snap[t]..clock : <<ValueAt(SkewA, s), ValueAt(SkewB, s)>> = SkewSeen(t)

\* What a log reader saw of the log: positions 1..head at its snapshot, and,
\* under MUTANT OwnAppendVisible, its own entry at the next position.
LogSeen(t) ==
  LET h == ValueAt(LogHead, snap[t])
  IN [p \in 1..(h + IF Mutant = "OwnAppendVisible" THEN 1 ELSE 0) |->
        IF p <= h THEN ValueAt(LogEntry(p), snap[t]) ELSE t]

\* The grants present at sequence s.
GrantsAt(s) == {i \in {1, 2} : ValueAt(AclKey(i), s) # Absent}

\* [3.14] What the transaction did with the reason's key is what `mine`
\* says.
Did(t, mine, k) ==
  CASE mine \in {"Read", "ReadPresence"} -> k \in tracked[t] \/ (k = PartKey /\ t \in PartTxns)
    [] mine = "ReadParts"        -> k = PartKey /\ t \in PartTxns
    [] mine = "ReadForUpdate"    -> \E f \in forUpdate[t] : f[1] = k
    [] mine = "ScannedThenWrote" -> k \in written[t] \cup merged[t]
    [] mine = "ScannedRange"     -> t \in Checkers /\ k[1] = AclRange
    [] mine = "Put"              -> k \in written[t] /\ intended[t][k] # Absent
    [] mine = "Delete"           -> k \in written[t] /\ intended[t][k] = Absent
    [] mine = "Merge"            -> k \in merged[t]
    [] OTHER                     -> FALSE

\* [3.14] A write of kind w.kind can decide a race for access `mine`: a
\* presence read loses only to a removal, a projected read only to a
\* replacement or an operand touching its parts, a blind merge only to a
\* replacement; any write can decide the others.
Decides(mine, w, parts) ==
  CASE mine = "ReadPresence" -> w.kind \in {"Delete", "RangeDelete"}
    [] mine = "ReadParts"    -> w.kind \in Replacing \/ w.touch \cap parts # {}
    [] mine = "Merge"        -> w.kind \in Replacing
    [] OTHER                 -> TRUE

\* The reason r of t's abort holds against the history at the abort: what
\* t did with the key is what `mine` says, and a write of the key newer than
\* the anchor, of kind `theirs` at sequence `latest`, can decide that race.
ReasonHolds(t, r) ==
  /\ r \in [key : Keys, mine : Accesses, theirs : Kinds, observed : Nat, latest : Nat,
            parts : SUBSET Parts]
  /\ Did(t, r.mine, r.key)
  /\ \E w \in hist : /\ w.key = r.key /\ w.seq = r.latest /\ w.kind = r.theirs
                     /\ w.seq > r.observed /\ Decides(r.mine, w, r.parts)

\* A refusal the relaxations promise never happens, or a reason that does not
\* hold.
AbortFlags(t) ==
  (IF ReasonHolds(t, ReasonOf(t)) THEN {} ELSE {"BadReason"})
  \cup (IF /\ t \in PartReaders
           /\ Found(PartKey, snap[t])
           /\ \A w \in After(PartKey, snap[t]) : w.kind = "Merge" /\ 1 \notin w.touch
        THEN {"PartsRefusedNeedlessly"} ELSE {})
  \cup (IF /\ t \in ValueReaders
           /\ store[VersionKey] = ValueAt(VersionKey, snap[t])
           /\ ~NewestIsOperand(VersionKey)
        THEN {"IdenticalRewriteRefused"} ELSE {})

\* A committed decision on inputs that changed before the commit.
CommitFlags(t) ==
  (IF t \in Holders /\ (store[Shared] # Absent) # Found(Shared, snap[t])
   THEN {"HoldStale"} ELSE {})
  \cup (IF t \in PartReaders
           /\ PartDecision(store[PartKey]) # PartDecision(ValueAt(PartKey, snap[t]))
        THEN {"PartsStale"} ELSE {})
  \cup (IF t \in PartRewriters /\ store[PartKey] # ValueAt(PartKey, snap[t])
        THEN {"PartsStale"} ELSE {})
  \cup (IF t \in ValueReaders /\ store[VersionKey] # ValueAt(VersionKey, snap[t])
        THEN {"ValueStale"} ELSE {})
  \cup (IF t \in ReadOnlys \cup Promoters /\ ~Consistent(t) THEN {"Skew"} ELSE {})
  \cup (IF t \in LogDeciders /\ store[LogHead] # ValueAt(LogHead, snap[t])
        THEN {"LogDecisionStale"} ELSE {})
  \cup (IF t \in LogReaders /\ \E p \in DOMAIN LogSeen(t) : NewValue(t, LogEntry(p)) # LogSeen(t)[p]
        THEN {"PhantomAppend"} ELSE {})
  \cup (IF t \in OwnWriters /\ NewValue(t, OwnKey) # OwnRead(t) THEN {"OwnMismatch"} ELSE {})
  \cup (IF t \in Checkers /\ GrantsAt(clock) # GrantsAt(snap[t]) THEN {"ScanStale"} ELSE {})

\* The counter's contract, kept apart from the engine's bookkeeping (the
\* history) so that a slip there shows up as a wrong value. A put or delete
\* of the counter starts an epoch at the value it stores, with the merge its
\* own batch puts on top counted in it, and discards only the increments it
\* saw: one committed after its snapshot stays counted although the put
\* erased it from the store. An increment counts if no put, delete or range
\* delete committed after it began, or if it was derived from a read of the
\* counter that still holds the count it read: that read is current, so the
\* increment serializes at its commit, after every reset.
Count(t, n) ==
  IF CounterKey \in written[t]
    THEN /\ cbase'  = intended[t][CounterKey]
         /\ cepoch' = n
         /\ cinc'   = {s \in cinc : s > snap[t]}
                      \cup (IF CounterKey \in merged[t] THEN {n} ELSE {})
  ELSE IF CounterKey \in merged[t]
    THEN /\ cinc' = IF \/ snap[t] >= cepoch
                       \/ CounterKey \in tracked[t] /\ store[CounterKey] = seen[t]
                    THEN cinc \cup {n} ELSE cinc
         /\ UNCHANGED <<cbase, cepoch>>
  ELSE UNCHANGED <<cbase, cepoch, cinc>>

\* The commit: abort with a reason when a check fails (Conflicts), or apply
\* every write at the next sequence and add it to the history. A promoter
\* commits only after its get_for_update.
Commit(t) ==
  /\ phase[t] = "open"
  /\ t \in Promoters => forUpdate[t] # {}
  /\ IF Conflicts(t)
       THEN /\ phase'  = [phase EXCEPT ![t] = "aborted"]
            /\ flags'  = flags \cup AbortFlags(t)
            /\ needlessRefusal' = (needlessRefusal \/ (t \in Incrementers /\ snap[t] >= cepoch))
            /\ dupRefused' = (dupRefused \/
                              (t \in Mergers /\ \A k \in written[t] :
                                  After(k, snap[t]) # {} => store[k] = intended[t][k]))
            /\ hist'   = Prune(hist, phase', clock)
            /\ UNCHANGED <<clock, store, parents, stale, wrongReceipt, cbase, cepoch, cinc>>
       ELSE /\ phase'    = [phase EXCEPT ![t] = "committed"]
            /\ clock'    = clock + 1
            /\ store'    = [k \in Keys |-> NewValue(t, k)]
            /\ hist'     = Prune(hist \cup Records(t, clock + 1), phase', clock + 1)
            /\ flags'    = flags \cup CommitFlags(t)
            /\ parents'  = IF t \in Appenders
                             THEN [parents EXCEPT ![t] = {h \in Blocks : MarkerKey(h, t) \in written[t]}]
                             ELSE IF t \in Mergers /\ written[t] # {}
                             THEN [parents EXCEPT ![Remote] = RemoteParents]
                             ELSE parents
            /\ stale'    = (stale \/ ((t = Writer \/ t \in Migrators) /\ store[DefKey] # seen[t]))
            /\ wrongReceipt' = (wrongReceipt \/ (t \in ReadMergers /\ store[CounterKey] # seen[t]))
            /\ Count(t, clock + 1)
            /\ UNCHANGED <<needlessRefusal, dupRefused>>
  /\ UNCHANGED <<snap, tracked, runs, written, intended, merged, seen, ops, forUpdate>>

\* Db::delete_range over the counter's range: a plain write, applied at once
\* and validated against nothing. A covering range tombstone is the newest
\* write of each key it covers (latest_version_in_view) and replaces each
\* one (newest_terminator_seq_above; MUTANT RangeDeleteNotReplacement
\* forgets that, in MergeDecider). Applied at once, it saw every increment
\* it discards.
Clear(c) ==
  LET covered == {k \in Keys : k[1] = CounterRange}
  IN /\ phase[c]  = "idle"
     /\ phase'    = [phase EXCEPT ![c] = "committed"]
     /\ clock'    = clock + 1
     /\ store'    = [k \in Keys |-> IF k \in covered THEN Absent ELSE store[k]]
     /\ hist'     = Prune(hist \cup {[seq |-> clock + 1, key |-> k, kind |-> "RangeDelete",
                                      val |-> Absent, touch |-> Parts] : k \in covered},
                          phase', clock + 1)
     /\ cbase'    = Absent
     /\ cepoch'   = clock + 1
     /\ cinc'     = {}
     /\ UNCHANGED <<snap, tracked, runs, written, intended, merged, seen, ops, forUpdate,
                    flags, parents, stale, dupRefused, wrongReceipt, needlessRefusal>>

\* Every step: a begin, a commit, a promotion or a range delete.
Next == \/ \E t \in Txns \ Clearers : Begin(t) \/ Commit(t)
        \/ \E p \in Promoters : Promote(p)
        \/ \E c \in Clearers : Clear(c)

\* Every behaviour, with weak fairness so every enabled step is taken.
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----------------------------------------------------------------------------
\* The shape of a history record.
Records_ == [seq : Nat, key : Keys, kind : Kinds, val : Nat, touch : SUBSET Parts]

\* Every variable holds what its comment says.
TypeOK ==
  /\ clock \in Nat
  /\ store \in [Keys -> Nat]
  /\ hist \subseteq Records_
  /\ phase \in [Txns -> {"idle", "open", "committed", "aborted"}]
  /\ \A t \in Txns : tracked[t] \subseteq Keys /\ written[t] \subseteq Keys /\ merged[t] \subseteq Keys
  /\ \A t \in Txns : \A s \in runs[t] : s \in Keys \X Keys /\ KeyLeq(s[1], s[2])
  /\ seen \in [Txns -> Nat]
  /\ \A t \in Txns : forUpdate[t] \subseteq Keys \X Nat
  /\ flags \subseteq FlagNames
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

\* E17. Every stored pin or holder reference names a stored block: a
\* collection never deletes a block from under a reference.
INV_NoDanglingReference ==
  (\E l \in Linkers : store[PinKey(l)] # Absent) \/ (\E h \in Holders : store[HoldKey(h)] = 1)
    => store[Shared] # Absent

\* Two creates of one block both commit: a linker is never refused.
INV_LinksCommit == \A l \in Linkers : phase[l] # "aborted"

\* A holder's record (present or missing) is still true at its commit.
INV_HoldsCurrent == "HoldStale" \notin flags

\* No projected reader commits after the key's existence or a part its
\* decision used changed.
INV_PartsCurrent == "PartsStale" \notin flags

\* A part reader that found the key is not refused when every newer write is
\* an operand that touches only part 2: the relaxation projected reads exist
\* for.
INV_PartsRelaxed == "PartsRefusedNeedlessly" \notin flags

\* No value reader commits after the value it read changed.
INV_ValueReadsCurrent == "ValueStale" \notin flags

\* No value reader is refused while the key holds the value it read, the
\* newest write being a put: an identical rewrite, or a value that came back.
INV_IdenticalRewritesCommit == "IdenticalRewriteRefused" \notin flags

\* A write-free DefraLevel transaction never conflicts.
INV_WriteFreeCommits == \A r \in ReadOnlys : phase[r] # "aborted"

\* Every committed write-free transaction read the state of one point in
\* time: no read skew.
INV_WriteFreeConsistent == "Skew" \notin flags

\* Appends and log reads are never validated, so no appender or log reader
\* is refused.
INV_LogNeverConflicts == \A t \in LogAppenders \cup LogReaders : phase[t] # "aborted"

\* The log holds entries 1..head, and nothing beyond: positions are dense.
INV_LogDense ==
  \A p \in LogPositions : (store[LogEntry(p)] # Absent) <=> p <= store[LogHead]

\* Every entry a log reader saw is in the log at its commit, at the position
\* it saw: a reader never sees a position its own append did not get.
INV_NoPhantomAppend == "PhantomAppend" \notin flags

\* No decision on the log's length went stale. Log reads are exempt, so a
\* caller must not decide on them [3.1]: this fails by design.
INV_LogDecisionsCurrent == "LogDecisionStale" \notin flags

\* A merge before a commutative scan stays blind: no tally merger is
\* refused, and no increment is lost.
INV_TallyMergesCommit == \A m \in TallyMergers : phase[m] # "aborted"
INV_TallyExact == store[TallyKey] = Cardinality({m \in TallyMergers : phase[m] = "committed"})

\* The value a commit leaves on the own key is the value its transaction
\* read back through its own writes.
INV_ReadYourOwnWrites == "OwnMismatch" \notin flags

\* No checker commits after a grant was revoked or a new one appeared.
INV_ScanDecisionsCurrent == "ScanStale" \notin flags

\* [3.14] Every abort's reason names a key the transaction did what `mine`
\* says with, and a committed write of that key newer than the anchor, with
\* the kind `theirs` and the sequence `latest`, that can decide such a race
\* (ReasonHolds, checked when the transaction aborts).
INV_ReasonsExact == "BadReason" \notin flags

\* State constraints that spend a config's states on one workload: the
\* transactions of every other one stay idle.
CounterWorkloadOnly ==
  \A t \in Appenders \cup {Pruner, Writer, Patcher} \cup Mergers \cup Migrators :
     phase[t] = "idle"
\* The writer, the patcher and the migrators only.
DefinitionWorkloadOnly ==
  \A t \in Appenders \cup {Pruner} \cup Mergers \cup CounterTxns : phase[t] = "idle"
\* The writer and the patcher touch no key of the DAG and read none through a
\* scan, so idling them loses no interleaving of the head set.
HeadsWorkloadOnly ==
  \A t \in {Writer, Patcher} \cup CounterTxns \cup Migrators : phase[t] = "idle"
\* The later workloads touch no key of the first ones.
NewWorkloadOnly == \A t \in OldTxns : phase[t] = "idle"

\* Under the level that refuses no append, every append lands.
EventuallyAllAppendsCommit == <>[](\A a \in Appenders : phase[a] = "committed")

====
