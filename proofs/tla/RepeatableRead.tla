---- MODULE RepeatableRead ----
\* ===========================================================================
\* THE STORY
\* ===========================================================================
\* Many transactions run against one database at the same time. None of them
\* locks anything. Each reads from a frozen picture taken when it began (its
\* snapshot), and when it asks to commit, the engine checks whether somebody
\* else has since changed what it relied on. If so, it is refused and the
\* caller runs it again. How much is checked is the "isolation level"
\* (IsolationLevel, src/transaction.rs).
\*
\* Tiny example 1, checking too little. The writer reads "definition,
\* version 1" and builds a document from it. Before the writer commits, the
\* patcher commits "definition, version 2". If the writer's commit is let
\* through, the database holds a document built from a definition that is no
\* longer there. Snapshot isolation lets it through, because the writer
\* never wrote the definition, it only read it. RepeatableRead checks every
\* key read one by one, and refuses the writer.
\*
\* Tiny example 2, checking too much. An appender scans the list of heads,
\* finds {seed}, and adds its own block on top. Meanwhile a sweep deletes an
\* old head key that a newer block had already replaced. The set of live
\* heads the appender worked out is the same before and after the sweep, yet
\* a level that checks every key a scan returned (Serializable) refuses the
\* append. RepeatableRead does not check what a scan returned, and lets it
\* through.
\*
\* What this model shows: which level refuses which of these, for the
\* workloads a Merkle-DAG CRDT store runs, and that DefraLevel (RepeatableRead
\* with relaxations the caller declares key by key) refuses every stale
\* commit and no harmless one. TLC runs every interleaving of a handful of
\* transactions; the Lean files named at the end prove the per-key rules for
\* any number.
\*
\* The commit rule, the key layout and the variables live in
\* RepeatableReadCommit.tla, which also names the code each rule mirrors.
\*
\* HOW THE MODEL SIMPLIFIES, and why that loses nothing.
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
\*             the markers against it that its scan yielded: the store's
\*             sweep of superseded heads.
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
\* into aborts only on a newer put, delete or range delete), and the
\* mechanisms of the later workloads below. For a key merged into blind this is not snapshot
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
\*   WriteFreeWorkload [3.8, E50], run at every level
\*     ReadOnly    optimistic, reads both skew keys at its snapshot, writes
\*                 nothing.
\*     ForUpdateReader  optimistic, reads skew key A plainly and skew key B
\*                 with get_for_update, both at its snapshot, writes nothing.
\*     Promoter    pessimistic, reads skew key A at its snapshot, then skew key
\*                 B with get_for_update at a later horizon, writes nothing.
\*                 Its lock on B is not modelled: dropping it only adds
\*                 interleavings, and the RED needs none of them.
\*     SkewWriter  writes both keys, one more each.
\*     Latcher     a failure that latches the database read-only at any
\*                 moment: every later commit that writes is refused.
\*     A commit that writes nothing takes no part in the commit pipeline: it
\*     is the step CommitWriteFree, which takes no sequence and checks what
\*     the level checks against the newest state (the published horizon).
\*     INV_WriteFreeCommits     a write-free transaction whose level checks
\*                              none of its reads (ReadCommitted,
\*                              SnapshotIsolation, DefraLevel's relaxation)
\*                              never conflicts.
\*     INV_WriteFreeConsistent  every committed write-free transaction read one
\*                              point in time, but a pessimistic one at
\*                              ReadCommitted or SnapshotIsolation, whose
\*                              get_for_update reads the newest value by design.
\*     INV_WriteFreeAtHorizon   every read the level promises to check still
\*                              holds its value when the commit is made: the
\*                              commit is placed at the published horizon.
\*     INV_WriteFreeTakesNoSequence  the sequence counts the commits that
\*                              wrote, and nothing else.
\*     INV_WriteFreeReceipt     a write-free commit's receipt is its snapshot.
\*     INV_LatchRefusesOnlyWrites  a latched database refuses only commits
\*                              that write.
\*   ReadOnlyAnomalyWorkload [E50; Fekete, O'Neil and O'Neil 2004]
\*     Withdrawer  SnapshotIsolation. Reads balances A and B, puts A to A + B.
\*     Depositor   SnapshotIsolation. Reads balance B, puts it one higher.
\*     Reporter    the configuration's Level. Reads both, writes nothing.
\*     The anomaly: the withdrawal reads (1, 1); the deposit commits B = 2;
\*     the report reads (1, 2); the withdrawal commits A = 2, the sum it
\*     read. The final (2, 2) puts the withdrawal before the deposit, and the
\*     report's (1, 2) puts the deposit before the withdrawal: no order of
\*     the three gives what the report saw.
\*     INV_NoReadOnlyAnomaly    no report commits a pair that no serial order
\*                              of the writers committed before it passes
\*                              through. A report at RepeatableRead or
\*                              Serializable checks its reads at its commit,
\*                              so one committed after the withdrawal is
\*                              refused. One committed before it cannot be,
\*                              at any level: only the writers' own level
\*                              prevents that (IsolationLevel's docs).
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
\*   RosterWorkload, ClaimWorkload [3.1 exempt reads, 3.2]
\*     Joiners   scan the roster, a commutative prefix, and each adds a key
\*               of its own and rewrites the seat with the bytes every joiner
\*               writes: the use the prefix is declared for.
\*     Claimers  misuse: scan the roster and, when the scan showed the seat
\*               free, take it and record "the seat is mine". An exclusive
\*               outcome decided on a scan inside a commutative prefix.
\*     INV_JoinsCommit   no joiner is refused.
\*     INV_RosterIsUnion the roster holds exactly the keys of the joiners
\*                       that committed: concurrent writers leave the union.
\*     INV_SeatExclusive at most one claimer's record says the seat is its.
\*   PeekWorkload, NoPartDecisionWorkload [3.1 exempt reads, 3.4]
\*     Peekers         get_parts(part key, {}), naming no part, and decide on
\*                     nothing they read, beside the part writers.
\*     NoPartDeciders  misuse: get_parts(part key, {}), then decide on part 1.
\*     INV_PeeksCommit  no peeker is refused, whatever is written under it.
\*     INV_PartsCurrent also covers a no-part decider: its decision went
\*                      stale when the key's existence or part 1 changed.
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
\*   WriteFreeUnchecked         a write-free commit checks nothing at any
\*                              level. INV_NoReadOnlyAnomaly RED at
\*                              Serializable, INV_WriteFreeAtHorizon RED at
\*                              RepeatableRead.
\*   WriteFreeRefusedWhenLatched  a latched database refuses a write-free
\*                              commit too (the 0.1.x engine).
\*                              INV_LatchRefusesOnlyWrites RED.
\*   WriteFreeTakesSequence     a write-free commit takes a sequence.
\*                              INV_WriteFreeTakesNoSequence RED.
\*   ReceiptAtHorizon           a write-free commit's receipt names the
\*                              horizon it was checked at, not its snapshot.
\*                              INV_WriteFreeReceipt RED.
\*   WriteFreeChecksPlainReads  a write-free commit checks every plain read
\*                              whatever its level. INV_WriteFreeCommits RED at
\*                              SnapshotIsolation.
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
\* Four REDs are misuse, not mutants: the engine runs its real rule in them
\* and the caller decides on a read the contract exempts [3.1].
\*   Red_DecideOnLogRead          a decision on a Log read.
\*                                INV_LogDecisionsCurrent RED.
\*   Red_DecideOnCommutativeScan  an exclusive outcome decided on a scan
\*                                inside a commutative prefix: two claimers
\*                                both take the one seat. INV_SeatExclusive
\*                                RED. Green_CommutativeScan is the same
\*                                prefix used as declared, and
\*                                Green_ClaimUndeclared the same claimers
\*                                with the prefix not declared, where the
\*                                seat each writes inside its recorded
\*                                stretch is validated as read and the
\*                                second claimer is refused: that check is
\*                                what the declaration gives up.
\*   Red_DecideOnNoParts          a decision on part 1 after
\*                                get_parts(key, {}). INV_PartsCurrent RED.
\*                                Green_NoParts is the same read deciding on
\*                                nothing, and Green_Parts the same decision
\*                                with part 1 named.
\* A fifth RED, Red_Parts_RepeatableRead, runs the real rule at another
\* level: get_parts at RepeatableRead is a get (INV_PartsRelaxed). A sixth,
\* MC_SnapshotIsolation_Red_ReadOnlyAnomaly, runs the real rule with the
\* report at SnapshotIsolation, which checks nothing: the anomaly the type's
\* docs warn about (INV_NoReadOnlyAnomaly).
\*
\* THE WRITE-FREE COMMIT, PIECE BY PIECE AGAINST THE CODE (E50). Line numbers
\* are those of commit f03e5e5 on perf/e50-readonly. Each row says what the
\* model piece stands for in the running program, in everyday words.
\*
\*   A transaction "writes nothing"                  WriteFree(t)
\*     The commit drains the buffered writes; when no put, delete, merge or
\*     append is left, it takes the write-free road.
\*     Transaction::drain_for_commit, `write_free`   src/transaction.rs:2037
\*     (a transaction never carries a range delete: delete_range refuses one)
\*   Which road the commit takes                    Commit(t): IF WriteFree(t)
\*     Writes nothing: the write-free check. Writes: a slot of the pipeline.
\*     Transaction::commit_inner                     src/transaction.rs:1994-1996
\*     Transaction::commit_nowait_inner              src/transaction/nowait.rs:294-297
\*   The write-free check itself                     CommitWriteFree(t)
\*     RegolithEngine::commit_write_free             src/engine/commit/mod.rs:545-615
\*     - "the database is open" is all it asks, so a latched database
\*       commits it (no LATCH branch unless the planted bug)
\*                                                   mod.rs:550, ensure_open (engine/mod.rs:1158)
\*     - it looks at the newest published state: the clock in the model
\*                                                   mod.rs:553, `horizon`
\*     - a read made at or after that point cannot have been written over;
\*       no read below it means nothing to look up    mod.rs:555-560
\*     - each read the level checks: refused when a newer write changed it
\*       (Conflicts(t) through ReadCands and ReadDecider)
\*                                                   mod.rs:564-591, read_changed (commit/read_rules.rs:42)
\*     - each validated scan: refused when anything was written in its range
\*       (ScanCands, ScanDecider)                     mod.rs:594-613, written_in_range (commit/range_rule.rs:31)
\*     - a refusal names the key, what the transaction did with it and the
\*       newer write (Abort(t), ReasonOf(t))          mod.rs:583, 605, Conflict::new (src/conflict.rs:128)
\*     - it takes no sequence: clock unchanged        mod.rs:614, CommitOutcome::Ok { seq: None }
\*     - its receipt is its snapshot: receipt' = snap  receipt_of (src/transaction.rs:2460)
\*   Which reads a level checks                      KeptReads(t), ValidatedReads(t), ForUpdateKept(t)
\*     Every point read at RepeatableRead, Serializable and DefraLevel; at
\*     SnapshotIsolation only get_for_update reads; at ReadCommitted only
\*     keys the commit writes, so none here.
\*     Transaction::validation_set                   src/transaction.rs:2191-2278 (filter at 2210-2221)
\*     scan stretches folded over the reads          scan_range::cover (src/transaction/scan_range.rs:294)
\*     validated ranges                              validated_range::checks (src/transaction/validated_range.rs:57)
\*   DefraLevel's write-free relaxation              ValidatesNothing(t)
\*     An optimistic DefraLevel transaction that writes nothing keeps only
\*     its get_for_update reads and no scan.
\*     drain_for_commit, `relaxed` and the `retain`  src/transaction.rs:2054-2059, 2076, 2095
\*   The transaction's level and flavour             LevelOf(t), Pessimistic(t), Classified(t)
\*     Transaction::isolation, Transaction::mode, Transaction::projects
\*                                                   src/transaction.rs (fields), src/transaction/projection.rs:259
\*   A get_for_update read                           ReadForUpdate(r) (optimistic), Promote(p) (pessimistic)
\*     Served at the snapshot when optimistic, at the newest published state
\*     with the key's lock held when pessimistic; marked to be checked.
\*     Transaction::read_for_update, read_horizon    src/transaction.rs:1488-1504, 2301-2311
\*   A failure that latches the database             Latch(l), latched
\*     RegolithEngine::latch, is_latched             src/engine/mod.rs:1208, 1214
\*   A commit that writes, on a latched database     CommitWriting(t), the `latched` branch
\*     request_commit's ensure_writable              src/engine/commit/mod.rs:417 (engine/mod.rs:1170)
\*
\* Code steps with no step of their own here, and why none is needed:
\*   - F2, the short road for a level that checks no read
\*     (checks_no_read_written_free, src/transaction.rs:2041, 2132): it
\*     builds the same set as the long road (no read), so the model's one
\*     KeptReads stands for both; the property test
\*     a_scan_validates_like_gets_of_what_it_walked compares them.
\*   - The horizon is sampled before the view is loaded, and a version above
\*     the horizon found in the view fails the read (mod.rs:553-577). In the
\*     model a commit is one step, so no commit lands between the sample and
\*     the look-up: the extra refusal only adds refusals, which no GREEN
\*     invariant forbids for a read that is checked at all (a level that
\*     checks nothing looks nothing up). Lean: full_ok_of_later,
\*     scan_ok_of_later; Rust tests a_commit_published_into_a_new_memtable_is_not_missed
\*     and a_version_folded_under_a_newer_one_still_fails_the_check.
\*   - The cache-only scope of commit_nowait (mod.rs:561): the model has no
\*     cache; Rust test a_cache_only_commit_that_writes_nothing_never_reads_the_device.
\*   - The conflict counter (Ticker::CommitConflictsOnRead) changes no outcome.
\* Model steps with no code of their own: PromisedChecks, FitsSerialOrder and
\* the flags are bookkeeping that watches the run; the engine has none of it.
\*
\* LEAN, for every size (proofs/lean/Regolith):
\*   Validation.lean     writeFree_at_horizon (INV_WriteFreeAtHorizon: a
\*                       write-free commit whose checks passed at the
\*                       published horizon read the serial state there),
\*                       full_ok_of_later and scan_ok_of_later (a check that
\*                       also counts writes above the horizon refuses more,
\*                       never less),
\*                       ordinary_serial, value_serial, contentAddressed_serial,
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
\*                       writeFree_at_snapshot (INV_WriteFreeConsistent),
\*                       read_only_anomaly (MC_Serializable_Red_ReadOnlyAnomaly); the
\*                       REDs exempt_decision_breaks_serial
\*                       (Red_DecideOnLogRead, Red_PartsNamesOther,
\*                       Red_DecideOnCommutativeScan, Red_DecideOnNoParts:
\*                       each decides on a read its class exempts) and
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

\* Everything in RepeatableReadCommit.tla (the keys, the variables, the commit rule) is in scope
\* here.
EXTENDS RepeatableReadCommit

\* The Extras a config names (Extras <- ...): which ids play which role.
NoExtras == [r \in RoleNames |-> {}]
\* The content-addressed collection: a collector, two linkers, a holder.
ContentAddressedWorkload ==
  \* Transaction 20 collects; 21 and 22 link; 23 holds.
  [NoExtras EXCEPT !["Collectors"] = {20}, !["Linkers"] = {21, 22}, !["Holders"] = {23}]
\* Projected reads: a part reader, a rewriter, two part writers. The REDs
\* run this whole workload; the two GREEN runs each take half of it.
PartsWorkload ==
  \* Transaction 30 reads by parts, 31 rewrites, 32 and 33 write the part key.
  [NoExtras EXCEPT !["PartReaders"] = {30}, !["PartRewriters"] = {31},
                   !["PartWriters"] = {32, 33}]
\* The part reader beside two part writers, without the rewriter
\* (MC_DefraLevel_Green_Parts).
PartsWritersWorkload ==
  \* Transaction 30 reads by parts; 32 and 33 write the part key. Nobody rewrites.
  [NoExtras EXCEPT !["PartReaders"] = {30}, !["PartWriters"] = {32, 33}]
\* The part reader beside the rewriter and one part writer
\* (MC_DefraLevel_Green_Parts_Rewriter).
PartsRewriterWorkload ==
  \* Transaction 30 reads by parts, 31 rewrites, and only 32 writes the part key.
  [NoExtras EXCEPT !["PartReaders"] = {30}, !["PartRewriters"] = {31},
                   !["PartWriters"] = {32}]
\* Value-validated reads: a reader and two version writers.
ValueWorkload ==
  \* Transaction 40 reads the version key; 41 and 42 rewrite it.
  [NoExtras EXCEPT !["ValueReaders"] = {40}, !["VersionWriters"] = {41, 42}]
\* Write-free transactions: a read-only, a for-update reader, a promoter, a skew writer, and a
\* failure that latches the database read-only.
WriteFreeWorkload ==
  \* Transaction 50 only reads, 51 promotes a read, 52 writes both skew keys, 53 reads B with
  \* get_for_update, and failure 57 latches the database.
  [NoExtras EXCEPT !["ReadOnlys"] = {50}, !["Promoters"] = {51}, !["SkewWriters"] = {52},
                   !["ForUpdateReaders"] = {53}, !["Latchers"] = {57}]
\* The read-only anomaly: a withdrawal and a deposit at SnapshotIsolation, and a report.
ReadOnlyAnomalyWorkload ==
  \* Transaction 54 withdraws, 55 deposits, 56 reports.
  [NoExtras EXCEPT !["Withdrawers"] = {54}, !["Depositors"] = {55}, !["Reporters"] = {56}]
\* The log: two appenders and a reader that appends too.
LogWorkload ==
  \* Transactions 60 and 61 append; 62 reads the head and appends.
  [NoExtras EXCEPT !["LogAppenders"] = {60, 61}, !["LogReaders"] = {62}]
\* The log misuse: an appender and a decider on the log's length.
LogDecisionWorkload ==
  \* Transaction 60 appends; 63 decides on the log's length.
  [NoExtras EXCEPT !["LogAppenders"] = {60}, !["LogDeciders"] = {63}]
\* E11: two merges into one commutative key, each then scanning its prefix.
TallyWorkload ==
  \* Transactions 70 and 71 merge into the tally key.
  [NoExtras EXCEPT !["TallyMergers"] = {70, 71}]
\* Read-your-own-writes: two transactions with two operations each.
OwnWritesWorkload ==
  \* Transactions 80 and 81 each make two operations on the own key.
  [NoExtras EXCEPT !["OwnWriters"] = {80, 81}]
\* Validated scans: a checker, a revoker and a granter.
ScanWorkload ==
  \* Transaction 90 checks the grants, 91 revokes one, 92 grants a new one.
  [NoExtras EXCEPT !["Checkers"] = {90}, !["Revokers"] = {91}, !["Granters"] = {92}]
\* A scan inside a commutative prefix, used as declared: three joiners.
RosterWorkload ==
  \* Transactions 100, 101 and 102 each scan the roster and add a key of their own.
  [NoExtras EXCEPT !["Joiners"] = {100, 101, 102}]
\* The same scan misused: two claimers of the one seat.
ClaimWorkload ==
  \* Transactions 110 and 111 each scan the roster and take the seat when it looked free.
  [NoExtras EXCEPT !["Claimers"] = {110, 111}]
\* A read by no parts, used as declared: a peeker beside two part writers.
PeekWorkload ==
  \* Transaction 34 reads the part key by no parts; 32 and 33 write the part key.
  [NoExtras EXCEPT !["Peekers"] = {34}, !["PartWriters"] = {32, 33}]
\* The same read misused: a decider on part 1 beside one part writer.
NoPartDecisionWorkload ==
  \* Transaction 35 reads the part key by no parts and decides on part 1; 32 writes the part key.
  [NoExtras EXCEPT !["NoPartDeciders"] = {35}, !["PartWriters"] = {32}]

\* The head set a scan of S derives: a stored head key no stored marker
\* names as a parent.
Heads(S) ==
  \* The blocks b whose head key is stored while no stored marker says some block c has b as a
  \* parent.
  {b \in Blocks : HeadKey(b) \in S /\ ~\E c \in Blocks : MarkerKey(b, c) \in S}

\* The blocks a scan of S finds superseded: a stored head some stored
\* marker names as a parent, which the sweep may reclaim.
Superseded(S) ==
  \* The blocks b whose head key is stored although some stored marker says a block c has b as a
  \* parent.
  {b \in Blocks : HeadKey(b) \in S /\ \E c \in Blocks : MarkerKey(b, c) \in S}

----------------------------------------------------------------------------
\* The start: nothing committed, every transaction idle, every key at its
\* initial value (InitStore), no history and no flag.
Init ==
  \* No commit yet: the sequence is 0.
  /\ clock     = 0
  \* Every key holds its starting value.
  /\ store     = InitStore
  \* No committed write is remembered.
  /\ hist      = {}
  \* No transaction has begun.
  /\ phase     = [t \in Txns |-> "idle"]
  \* No transaction has a snapshot yet.
  /\ snap      = [t \in Txns |-> 0]
  \* Nobody has read anything.
  /\ tracked   = [t \in Txns |-> {}]
  \* Nobody has scanned anything.
  /\ runs      = [t \in Txns |-> {}]
  \* Nobody plans a put or a delete.
  /\ written   = [t \in Txns |-> {}]
  \* Nobody plans a merge.
  /\ merged    = [t \in Txns |-> {}]
  \* No key has an intended value.
  /\ intended  = [t \in Txns |-> [k \in Keys |-> Absent]]
  \* Nobody has built a write from a value yet.
  /\ seen      = [t \in Txns |-> 0]
  \* Nobody has chosen operations yet.
  /\ ops       = [t \in Txns |-> <<>>]
  \* No get_for_update was served.
  /\ forUpdate = [t \in Txns |-> {}]
  \* No anomaly was noticed.
  /\ flags     = {}
  \* No block has recorded parents.
  /\ parents   = [b \in Blocks |-> {}]
  \* No stale write has committed.
  /\ stale     = FALSE
  \* No duplicate merge was refused.
  /\ dupRefused      = FALSE
  \* No wrong receipt was issued.
  /\ wrongReceipt    = FALSE
  \* No increment was refused needlessly.
  /\ needlessRefusal = FALSE
  \* The counter's contract starts from an absent counter,
  /\ cbase     = Absent
  \* set at sequence 0,
  /\ cepoch    = 0
  \* with no increment counted on top.
  /\ cinc      = {}
  \* No commit has a receipt yet.
  /\ receipt   = [t \in Txns |-> 0]
  \* No failure has latched the database.
  /\ latched   = FALSE

\* The remote block's parents are fixed by its content, not by the local
\* heads; the scan is the head-set read the merge path makes. A block already
\* stored is not merged again, which a point read of its key decides: the
\* blockstore reads whether a block is stored in the transaction that puts
\* it.
BeginMerger(m) ==
  \* heads: what a scan of the whole head range yields at this moment.
  LET heads   == Yield(Stored, HeadRange, HeadRange)
      \* markers: what a scan of the whole marker range yields.
      markers == Yield(Stored, MarkerRange, MarkerRange)
      \* keys: what the merger will write. Nothing when the remote block is already stored;
      keys    == IF BlockKey(Remote) \in Stored THEN {}
                 \* otherwise the remote block's head key and block key,
                 ELSE {HeadKey(Remote), BlockKey(Remote)}
                      \* and one marker per parent the remote block names.
                      \cup {MarkerKey(p, Remote) : p \in RemoteParents}
  \* Its recorded point reads: whether the block is stored, plus the scanned keys where the level
  \* records those.
  IN /\ tracked'  = [tracked EXCEPT ![m] =
                      {BlockKey(Remote)} \cup ScanReads(heads) \cup ScanReads(markers)]
     \* Its stretches: one per scan that yielded something.
     /\ runs'     = [runs EXCEPT ![m] = Stretch(heads) \cup Stretch(markers)]
     \* The keys it will put.
     /\ written'  = [written EXCEPT ![m] = keys]
     \* Each of them will hold 1 (present).
     /\ intended' = [intended EXCEPT ![m] = [k \in Keys |-> IF k \in keys THEN 1 ELSE Absent]]
     \* It merges nothing and builds nothing from a value.
     /\ UNCHANGED <<merged, seen, ops>>

\* An increment merged into the counter, reading nothing.
BeginIncrementer(i) ==
  \* It will merge one operand into the counter.
  /\ merged' = [merged EXCEPT ![i] = {CounterKey}]
  \* Nothing else is recorded: no read, no scan, no put.
  /\ UNCHANGED <<tracked, runs, written, intended, seen, ops>>

\* Transaction::get on the counter, then an increment merged into it. The
\* receipt, the count read plus one, is kept in `seen`: no other transaction
\* writes it, so as a key it would add no conflict.
BeginReadMerger(r) ==
  \* It read the counter, a recorded point read.
  /\ tracked' = [tracked EXCEPT ![r] = {CounterKey}]
  \* It will merge an increment into it.
  /\ merged'  = [merged EXCEPT ![r] = {CounterKey}]
  \* It remembers the count it read, for its receipt.
  /\ seen'    = [seen EXCEPT ![r] = store[CounterKey]]
  \* No scan and no put.
  /\ UNCHANGED <<runs, written, intended, ops>>

\* The counter put to 1 and an increment merged on top, in one batch.
BeginRebaser(r) ==
  \* It will put the counter
  /\ written'  = [written EXCEPT ![r] = {CounterKey}]
  \* and merge an increment into it, in the same commit.
  /\ merged'   = [merged EXCEPT ![r] = {CounterKey}]
  \* The put stores 1.
  /\ intended' = [intended EXCEPT ![r] = [k \in Keys |-> IF k = CounterKey THEN 1 ELSE Absent]]
  \* No read and no scan.
  /\ UNCHANGED <<tracked, runs, seen, ops>>

\* A delete of the counter.
BeginResetter(r) ==
  \* It will write the counter:
  /\ written'  = [written EXCEPT ![r] = {CounterKey}]
  \* a delete (every intended value is absent).
  /\ intended' = [intended EXCEPT ![r] = [k \in Keys |-> Absent]]
  \* No read, no scan, no merge.
  /\ UNCHANGED <<tracked, runs, merged, seen, ops>>

\* One stream from the head range through the definition: its stretch starts
\* in the head prefix and ends on the definition.
BeginMigrator(g) ==
  \* walk: what one scan from the head range through the definition range yields.
  LET walk == Yield(Stored, HeadRange, DefRange)
  \* Its recorded reads: the scanned keys, where the level records those.
  IN /\ tracked'  = [tracked EXCEPT ![g] = ScanReads(walk)]
     \* Its stretch: from the first head key to the definition, so it leaves the head prefix.
     /\ runs'     = [runs EXCEPT ![g] = Stretch(walk)]
     \* It will put the definition,
     /\ written'  = [written EXCEPT ![g] = {DefKey}]
     \* one version up from the one it read.
     /\ intended' = [intended EXCEPT ![g] =
                      [k \in Keys |-> IF k = DefKey THEN store[DefKey] + 1 ELSE Absent]]
     \* It remembers the definition it read.
     /\ seen'     = [seen EXCEPT ![g] = store[DefKey]]
     \* No merge.
     /\ UNCHANGED <<merged, ops>>

\* Scan the heads and markers, then write its own head, its block, and a
\* marker naming itself against every live head.
BeginAppender(a) ==
  \* heads: what a scan of the head range yields.
  LET heads   == Yield(Stored, HeadRange, HeadRange)
      \* markers: what a scan of the marker range yields.
      markers == Yield(Stored, MarkerRange, MarkerRange)
      \* keys: its own head key, its own block, and one marker per live head naming itself as the
      \* child.
      keys    == {HeadKey(a), BlockKey(a)} \cup {MarkerKey(h, a) : h \in Heads(Stored)}
  \* Its recorded reads: the scanned keys, where the level records those.
  IN /\ tracked'  = [tracked EXCEPT ![a] = ScanReads(heads) \cup ScanReads(markers)]
     \* Its stretches: one per scan that yielded something.
     /\ runs'     = [runs EXCEPT ![a] = Stretch(heads) \cup Stretch(markers)]
     \* The keys it will put.
     /\ written'  = [written EXCEPT ![a] = keys]
     \* Each will hold 1 (present).
     /\ intended' = [intended EXCEPT ![a] = [k \in Keys |-> IF k \in keys THEN 1 ELSE Absent]]
     \* No merge, nothing built from a value.
     /\ UNCHANGED <<merged, seen, ops>>

\* Enabled once something is reclaimable, as the real sweep is a no-op
\* otherwise. One head per pass, chosen freely, with the markers against it
\* the scan yielded: a marker an open append is about to write is not in
\* the snapshot and is not touched.
BeginPruner ==
  \* heads: what a scan of the head range yields.
  LET heads   == Yield(Stored, HeadRange, HeadRange)
      \* markers: what a scan of the marker range yields.
      markers == Yield(Stored, MarkerRange, MarkerRange)
  \* Pick any superseded head b.
  IN /\ \E b \in Superseded(Stored) :
          \* The pruner will delete b's head key and the markers against b that its scan yielded.
          written' = [written EXCEPT ![Pruner] =
                       {HeadKey(b)} \cup {m \in markers : m[2] = b}]
     \* Every key it writes is a delete.
     /\ intended' = [intended EXCEPT ![Pruner] = [k \in Keys |-> Absent]]
     \* Its recorded reads: the scanned keys, where the level records those.
     /\ tracked'  = [tracked EXCEPT ![Pruner] = ScanReads(heads) \cup ScanReads(markers)]
     \* Its stretches: one per scan that yielded something.
     /\ runs'     = [runs EXCEPT ![Pruner] = Stretch(heads) \cup Stretch(markers)]
     \* No merge, nothing built from a value.
     /\ UNCHANGED <<merged, seen, ops>>

\* Transaction::observe on the definition, then a document carrying it.
BeginWriter ==
  \* It read the definition, a recorded point read.
  /\ tracked'  = [tracked EXCEPT ![Writer] = {DefKey}]
  \* It will put the document,
  /\ written'  = [written EXCEPT ![Writer] = {DocKey}]
  \* holding the definition's value as it read it.
  /\ intended' = [intended EXCEPT ![Writer] =
                   [k \in Keys |-> IF k = DocKey THEN store[DefKey] ELSE Absent]]
  \* It remembers the definition it read.
  /\ seen'     = [seen EXCEPT ![Writer] = store[DefKey]]
  \* No scan and no merge.
  /\ UNCHANGED <<runs, merged, ops>>

\* The definition replaced by the next version.
BeginPatcher ==
  \* It will put the definition,
  /\ written'  = [written EXCEPT ![Patcher] = {DefKey}]
  \* one version up.
  /\ intended' = [intended EXCEPT ![Patcher] =
                   [k \in Keys |-> IF k = DefKey THEN store[DefKey] + 1 ELSE Absent]]
  \* It reads nothing.
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
  \* its recorded point reads,
  /\ tracked'  = [tracked EXCEPT ![t] = rd]
  \* its scan stretches,
  /\ runs'     = [runs EXCEPT ![t] = rn]
  \* the keys it puts or deletes,
  /\ written'  = [written EXCEPT ![t] = wr]
  \* the keys it merges into,
  /\ merged'   = [merged EXCEPT ![t] = mg]
  \* and what each written key will hold.
  /\ intended' = [intended EXCEPT ![t] = Intend(it)]

\* Enabled once the shared block is stored and nothing refers to it at the
\* snapshot. The pin scan is a plain scan, and an empty one records no
\* stretch: the collector relies on every pinner putting the block again,
\* which its validated delete sees. A hold is a point read of a key the
\* collector must see change, so it is validated in full.
BeginCollector(c) ==
  \* The shared block is stored.
  /\ store[Shared] # Absent
  \* A scan of the pin range finds no pin.
  /\ Yield(Stored, PinRange, PinRange) = {}
  \* No holder's note says the block is present.
  /\ \A h \in Holders : store[HoldKey(h)] # 1
  \* It reads the block and every hold, and will delete the block.
  /\ Do(c, {Shared} \cup {HoldKey(h) : h \in Holders}, {}, {Shared}, {}, Shared :> Absent)
  \* Nothing built from a value, no operations chosen.
  /\ UNCHANGED <<seen, ops>>

\* A pin re-puts the block it refers to, or merges the block's own bytes
\* into it (an idempotent operand): either way the commit stores the block.
BeginLinker(l) ==
  \* It picks how to store the block again: with a put or with a merge.
  \E how \in {"put", "merge"} :
    \* It reads the block. It will write its pin, and the block too when it chose a put; it merges
    \* into the block when it chose a merge. Both the pin and the block hold 1.
    /\ Do(l, {Shared}, {},
          {PinKey(l)} \cup (IF how = "put" THEN {Shared} ELSE {}),
          IF how = "merge" THEN {Shared} ELSE {},
          (PinKey(l) :> 1) @@ (Shared :> 1))
    \* It remembers which way it chose.
    /\ ops' = [ops EXCEPT ![l] = <<how>>]
    \* Nothing built from a value.
    /\ UNCHANGED seen

\* The holder's record: 1 refers to the block, 2 says it is missing.
BeginHolder(h) ==
  \* It reads the block and will write its note: 1 when the block is present, 2 when it is missing.
  /\ Do(h, {Shared}, {}, {HoldKey(h)}, {},
        HoldKey(h) :> IF store[Shared] # Absent THEN 1 ELSE 2)
  \* Nothing built from a value, no operations chosen.
  /\ UNCHANGED <<seen, ops>>

\* The part reader's get_parts is recorded by role (PartRead); its decision,
\* part 1 as read, goes to its output key.
BeginPartReader(r) ==
  \* It will write part 1 of the part key, as it read it, to its output key.
  /\ Do(r, {}, {}, {OutKey(r)}, {}, OutKey(r) :> Part(store[PartKey], 1))
  \* Nothing built from a value, no operations chosen.
  /\ UNCHANGED <<seen, ops>>

\* The rewrite: part 1 one up, part 2 as read.
Rewrite(v) == PartValue(Part(v, 1) + 1, Part(v, 2))

\* get_parts(part key, {1}) (by role), then a put of the rewrite.
BeginPartRewriter(w) ==
  \* It will put the part key with part 1 one up.
  /\ Do(w, {}, {}, {PartKey}, {}, PartKey :> Rewrite(store[PartKey]))
  \* Nothing built from a value, no operations chosen.
  /\ UNCHANGED <<seen, ops>>

\* One blind write: the value read again ("same"), the value read with
\* part 2 one up ("other"), a delete, or an operand touching one part.
BeginPartWriter(w) ==
  \* It picks one of five writes.
  \E op \in {"same", "other", "delete", "touch1", "touch2"} :
    \* It remembers the pick.
    /\ ops' = [ops EXCEPT ![w] = <<op>>]
    \* An operand:
    /\ IF op \in {"touch1", "touch2"}
         \* it merges into the part key and puts nothing.
         THEN Do(w, {}, {}, {}, {PartKey}, NoIntent)
         \* A put or a delete of the part key, which stores:
         ELSE Do(w, {}, {}, {PartKey}, {},
                 \* the same value again;
                 PartKey :> CASE op = "same"   -> store[PartKey]
                              \* the value with part 2 one up;
                              [] op = "other"  -> PartValue(Part(store[PartKey], 1),
                                                            Part(store[PartKey], 2) + 1)
                              \* or nothing (a delete).
                              [] op = "delete" -> Absent)
    \* Nothing built from a value.
    /\ UNCHANGED seen

\* A read of the version key; its value goes to the output key.
BeginValueReader(r) ==
  \* It reads the version key and will write the value it read to its output key.
  /\ Do(r, {VersionKey}, {}, {OutKey(r)}, {}, OutKey(r) :> store[VersionKey])
  \* Nothing built from a value, no operations chosen.
  /\ UNCHANGED <<seen, ops>>

\* The version key holds 1 or 2; "other" toggles it.
BeginVersionWriter(w) ==
  \* It picks: the same value again, or the other one.
  \E op \in {"same", "other"} :
    \* It will put the version key: the value it holds, or 3 minus it (1 becomes 2, 2 becomes 1).
    /\ Do(w, {}, {}, {VersionKey}, {},
          VersionKey :> IF op = "same" THEN store[VersionKey] ELSE 3 - store[VersionKey])
    \* Nothing built from a value, no operations chosen.
    /\ UNCHANGED <<seen, ops>>

\* Both skew keys read at the snapshot, nothing written.
BeginReadOnly(r) ==
  \* It reads both skew keys and writes nothing.
  /\ Do(r, {SkewA, SkewB}, {}, {}, {}, NoIntent)
  \* Nothing built from a value, no operations chosen.
  /\ UNCHANGED <<seen, ops>>

\* The read of B comes later, in Promote.
BeginPromoter(p) ==
  \* It reads skew key A at its snapshot and writes nothing.
  /\ Do(p, {SkewA}, {}, {}, {}, NoIntent)
  \* Nothing built from a value, no operations chosen.
  /\ UNCHANGED <<seen, ops>>

\* Skew key A read plainly at the snapshot; the get_for_update of B comes later, in ReadForUpdate.
BeginForUpdateReader(r) ==
  \* It reads skew key A at its snapshot and writes nothing.
  /\ Do(r, {SkewA}, {}, {}, {}, NoIntent)
  \* Nothing built from a value, no operations chosen.
  /\ UNCHANGED <<seen, ops>>

\* The bank's withdrawal: both balances read, balance A put to A + B, a value that tells which B it
\* read.
BeginWithdrawer(w) ==
  \* It reads both balances and will put A to their sum, as they are at its snapshot.
  /\ Do(w, {SkewA, SkewB}, {}, {SkewA}, {}, SkewA :> store[SkewA] + store[SkewB])
  \* Nothing else built from a value, no operations chosen.
  /\ UNCHANGED <<seen, ops>>

\* The bank's deposit: balance B read and put one higher.
BeginDepositor(d) ==
  \* It reads balance B and will put it one higher than it is at its snapshot.
  /\ Do(d, {SkewB}, {}, {SkewB}, {}, SkewB :> store[SkewB] + 1)
  \* Nothing else built from a value, no operations chosen.
  /\ UNCHANGED <<seen, ops>>

\* The report: both balances read at the snapshot, nothing written.
BeginReporter(r) ==
  \* It reads both balances and writes nothing.
  /\ Do(r, {SkewA, SkewB}, {}, {}, {}, NoIntent)
  \* Nothing built from a value, no operations chosen.
  /\ UNCHANGED <<seen, ops>>

\* Both skew keys one more, blind.
BeginSkewWriter(w) ==
  \* It will put both skew keys, each one more than it holds now, reading neither.
  /\ Do(w, {}, {}, {SkewA, SkewB}, {}, (SkewA :> store[SkewA] + 1) @@ (SkewB :> store[SkewB] + 1))
  \* Nothing built from a value, no operations chosen.
  /\ UNCHANGED <<seen, ops>>

\* An append records nothing at begin: its position is assigned at commit.
BeginLogAppender(a) ==
  \* Nothing is recorded: no read and no write. The append itself is added at commit.
  /\ Do(a, {}, {}, {}, {}, NoIntent)
  \* Nothing built from a value, no operations chosen.
  /\ UNCHANGED <<seen, ops>>

\* The head it read becomes its cursor; its own append is not in the head.
BeginLogReader(r) ==
  \* It reads the log's head and will write that head to its output key.
  /\ Do(r, {LogHead}, {}, {OutKey(r)}, {}, OutKey(r) :> store[LogHead])
  \* Nothing built from a value, no operations chosen.
  /\ UNCHANGED <<seen, ops>>

\* The head read (never validated) and written down as how many entries
\* the log holds: a decision on a Log read.
BeginLogDecider(d) ==
  \* It reads the log's head and will write it down as the number of entries.
  /\ Do(d, {LogHead}, {}, {OutKey(d)}, {}, OutKey(d) :> store[LogHead])
  \* Nothing built from a value, no operations chosen.
  /\ UNCHANGED <<seen, ops>>

\* The merge comes first; the scan of the tally prefix then yields the key,
\* made visible by the transaction's own operand, as one stretch inside the
\* prefix. E11: the scan reads the operands-only key's base without
\* recording it (MUTANT MergeBeforeScanReadsBase records it).
BeginTallyMerger(m) ==
  \* It merges into the tally key and records one stretch, from the tally key to itself. Under the
  \* planted bug it also records the key as read.
  /\ Do(m, IF Mutant = "MergeBeforeScanReadsBase" THEN {TallyKey} ELSE {},
        {<<TallyKey, TallyKey>>}, {}, {TallyKey}, NoIntent)
  \* Nothing built from a value, no operations chosen.
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
  \* It picks one of the five orders.
  \E s \in OpSeqs :
    \* applied: the order the commit will apply (puts first under the planted bug PutsBeforeMerges).
    LET applied == IF Mutant = "PutsBeforeMerges" THEN PutsFirst(s) ELSE s
        \* reps: the puts and deletes among them.
        reps    == SelectSeq(applied, LAMBDA x : x # "merge")
    \* It remembers the order it chose.
    IN /\ ops' = [ops EXCEPT ![o] = s]
       \* It records: a read of the own key only when it has no put or delete; a write of it when it
       \* has one; a merge into it when the last applied operation is a merge; and the value its
       \* last put or delete leaves (5 for a put, absent for a delete).
       /\ Do(o, IF reps = <<>> THEN {OwnKey} ELSE {}, {},
             IF reps = <<>> THEN {} ELSE {OwnKey},
             IF applied[Len(applied)] = "merge" THEN {OwnKey} ELSE {},
             IF reps = <<>> THEN NoIntent
             ELSE OwnKey :> (IF reps[Len(reps)] = "put" THEN 5 ELSE Absent))
       \* Nothing built from a value.
       /\ UNCHANGED seen

\* The checker's decision, the number of grants, goes to its output key. The
\* validated range is recorded by role (ScanDecider); the plain stretch is
\* recorded as for any scan.
BeginChecker(c) ==
  \* grants: what a scan of the grant range yields.
  LET grants == Yield(Stored, AclRange, AclRange)
  \* It records the scan's stretch and will write the number of grants to its output key.
  IN /\ Do(c, {}, Stretch(grants), {OutKey(c)}, {}, OutKey(c) :> Cardinality(grants))
     \* Nothing built from a value, no operations chosen.
     /\ UNCHANGED <<seen, ops>>

\* The grant deleted.
BeginRevoker(r) ==
  \* It will delete grant 1.
  /\ Do(r, {}, {}, {AclKey(1)}, {}, AclKey(1) :> Absent)
  \* Nothing built from a value, no operations chosen.
  /\ UNCHANGED <<seen, ops>>

\* A new grant put.
BeginGranter(g) ==
  \* It will put grant 2.
  /\ Do(g, {}, {}, {AclKey(2)}, {}, AclKey(2) :> 1)
  \* Nothing built from a value, no operations chosen.
  /\ UNCHANGED <<seen, ops>>

\* A scan of the roster, then a key of its own and the seat, both inside the
\* stretch the scan walked. Every joiner writes the seat with the same
\* bytes and decides nothing on what it scanned: unique keys and identical
\* rewrites, the two writes a commutative prefix is declared for [3.2].
BeginJoiner(j) ==
  \* roster: what a scan of the whole roster yields. The first and the last key are always there.
  LET roster == Yield(Stored, RosterRange, RosterRange)
  \* It records the scan's stretch and will put its own key and the seat, each holding 1.
  IN /\ Do(j, ScanReads(roster), Stretch(roster), {MemberKey(j), SeatKey}, {},
           (MemberKey(j) :> 1) @@ (SeatKey :> 1))
     \* Nothing built from a value, no operations chosen.
     /\ UNCHANGED <<seen, ops>>

\* The misuse: the same scan, and the seat taken only when the scan showed it
\* free, with "the seat is mine" written to its output key outside the
\* prefix. The seat is written with the bytes any claimer writes. A claimer
\* that finds the seat taken writes nothing.
BeginClaimer(c) ==
  \* roster: what a scan of the whole roster yields.
  LET roster == Yield(Stored, RosterRange, RosterRange)
      \* free: the scan did not yield the seat.
      free   == SeatKey \notin roster
  \* It records the scan's stretch. When the seat looked free it will put the seat and its own
  \* record, each holding 1; otherwise it writes nothing.
  IN /\ Do(c, ScanReads(roster), Stretch(roster),
           IF free THEN {SeatKey, OutKey(c)} ELSE {}, {},
           IF free THEN (SeatKey :> 1) @@ (OutKey(c) :> 1) ELSE NoIntent)
     \* Nothing built from a value, no operations chosen.
     /\ UNCHANGED <<seen, ops>>

\* get_parts(part key, {}) is recorded by role (PartRead): it names no part,
\* so the commit validates nothing of it. The peeker writes a fixed mark to
\* its output key: nothing it read went into what it wrote.
BeginPeeker(p) ==
  \* It will write 1 to its output key, whatever the part key held.
  /\ Do(p, {}, {}, {OutKey(p)}, {}, OutKey(p) :> 1)
  \* Nothing built from a value, no operations chosen.
  /\ UNCHANGED <<seen, ops>>

\* The misuse: the same read by no parts, and part 1 as read written to its
\* output key. Its decision uses what the read exempted.
BeginNoPartDecider(d) ==
  \* It will write part 1 of the part key, as it read it, to its output key.
  /\ Do(d, {}, {}, {OutKey(d)}, {}, OutKey(d) :> Part(store[PartKey], 1))
  \* Nothing built from a value, no operations chosen.
  /\ UNCHANGED <<seen, ops>>

\* Transaction t begins: it takes its snapshot and records what its role
\* reads and writes.
Begin(t) ==
  \* It has not begun yet.
  /\ phase[t] = "idle"
  \* It is open from now on.
  /\ phase' = [phase EXCEPT ![t] = "open"]
  \* Its snapshot is the newest committed sequence.
  /\ snap'  = [snap EXCEPT ![t] = clock]
  \* What it records depends on its role. An appender:
  /\ CASE t \in Appenders      -> BeginAppender(t)
       \* the pruner:
       [] t = Pruner           -> BeginPruner
       \* the writer:
       [] t = Writer           -> BeginWriter
       \* the patcher:
       [] t = Patcher          -> BeginPatcher
       \* a merger:
       [] t \in Mergers        -> BeginMerger(t)
       \* an incrementer:
       [] t \in Incrementers   -> BeginIncrementer(t)
       \* a read-merger:
       [] t \in ReadMergers    -> BeginReadMerger(t)
       \* a rebaser:
       [] t \in Rebasers       -> BeginRebaser(t)
       \* a resetter:
       [] t \in Resetters      -> BeginResetter(t)
       \* a migrator:
       [] t \in Migrators      -> BeginMigrator(t)
       \* a collector:
       [] t \in Collectors     -> BeginCollector(t)
       \* a linker:
       [] t \in Linkers        -> BeginLinker(t)
       \* a holder:
       [] t \in Holders        -> BeginHolder(t)
       \* a part reader:
       [] t \in PartReaders    -> BeginPartReader(t)
       \* a part rewriter:
       [] t \in PartRewriters  -> BeginPartRewriter(t)
       \* a part writer:
       [] t \in PartWriters    -> BeginPartWriter(t)
       \* a value reader:
       [] t \in ValueReaders   -> BeginValueReader(t)
       \* a version writer:
       [] t \in VersionWriters -> BeginVersionWriter(t)
       \* a read-only transaction:
       [] t \in ReadOnlys      -> BeginReadOnly(t)
       \* a promoter:
       [] t \in Promoters      -> BeginPromoter(t)
       \* a skew writer:
       [] t \in SkewWriters    -> BeginSkewWriter(t)
       \* a for-update reader:
       [] t \in ForUpdateReaders -> BeginForUpdateReader(t)
       \* the bank's withdrawal:
       [] t \in Withdrawers    -> BeginWithdrawer(t)
       \* the bank's deposit:
       [] t \in Depositors     -> BeginDepositor(t)
       \* the report:
       [] t \in Reporters      -> BeginReporter(t)
       \* a log appender:
       [] t \in LogAppenders   -> BeginLogAppender(t)
       \* a log reader:
       [] t \in LogReaders     -> BeginLogReader(t)
       \* a log decider:
       [] t \in LogDeciders    -> BeginLogDecider(t)
       \* a tally merger:
       [] t \in TallyMergers   -> BeginTallyMerger(t)
       \* an own-writer:
       [] t \in OwnWriters     -> BeginOwnWriter(t)
       \* a checker:
       [] t \in Checkers       -> BeginChecker(t)
       \* a revoker:
       [] t \in Revokers       -> BeginRevoker(t)
       \* a granter:
       [] t \in Granters       -> BeginGranter(t)
       \* a joiner:
       [] t \in Joiners        -> BeginJoiner(t)
       \* a claimer:
       [] t \in Claimers       -> BeginClaimer(t)
       \* a peeker:
       [] t \in Peekers        -> BeginPeeker(t)
       \* a no-part decider:
       [] t \in NoPartDeciders -> BeginNoPartDecider(t)
  \* A begin commits nothing: the store, the history and the bookkeeping stay as they were.
  /\ UNCHANGED <<clock, store, hist, forUpdate, flags, parents, stale, dupRefused,
                 wrongReceipt, needlessRefusal, cbase, cepoch, cinc, receipt, latched>>

\* A pessimistic promoter reads skew key B with get_for_update at the
\* current horizon, past its snapshot [3.8].
Promote(p) ==
  \* The promoter is open,
  /\ phase[p] = "open"
  \* and has not made this read yet.
  /\ forUpdate[p] = {}
  \* It reads skew key B as of the newest committed sequence, which is later than its snapshot.
  /\ forUpdate' = [forUpdate EXCEPT ![p] = {<<SkewB, clock>>}]
  \* Nothing else changes.
  /\ UNCHANGED <<clock, store, hist, phase, snap, tracked, runs, written, merged, intended,
                 seen, ops, flags, parents, stale, dupRefused, wrongReceipt,
                 needlessRefusal, cbase, cepoch, cinc, receipt, latched>>

\* An optimistic for-update reader reads skew key B with get_for_update. An optimistic transaction
\* reads every key at its snapshot (Transaction::read_horizon), so this read is served there too; what
\* makes it different from a plain read is that the commit checks it, at SnapshotIsolation and above
\* (KeyState::for_update).
ReadForUpdate(r) ==
  \* The reader is open,
  /\ phase[r] = "open"
  \* and has not made this read yet.
  /\ forUpdate[r] = {}
  \* It reads skew key B as of its own snapshot.
  /\ forUpdate' = [forUpdate EXCEPT ![r] = {<<SkewB, snap[r]>>}]
  \* Nothing else changes.
  /\ UNCHANGED <<clock, store, hist, phase, snap, tracked, runs, written, merged, intended,
                 seen, ops, flags, parents, stale, dupRefused, wrongReceipt,
                 needlessRefusal, cbase, cepoch, cinc, receipt, latched>>

----------------------------------------------------------------------------
\* The ghosts the later workloads' invariants read, computed when a
\* transaction ends, from the history: what it read is the value at its
\* snapshot (ValueAt), what holds now is `store`.

\* What an own-writer read back: its operations folded onto the value at its
\* snapshot, in operation order [3.9]. MUTANT OwnMergesInvisible skips its
\* merges.
OwnRead(t) ==
  \* s: its operations, without the merges under the planted bug OwnMergesInvisible,
  LET s == IF Mutant = "OwnMergesInvisible" THEN SelectSeq(ops[t], LAMBDA o : o # "merge")
           \* and all of them otherwise.
           ELSE ops[t]
  \* Folded onto what the own key held at its snapshot.
  IN Fold(s, ValueAt(OwnKey, snap[t]))

\* A part reader's decision inputs: whether the key exists, and part 1.
PartDecision(v) == <<v # Absent, Part(v, 1)>>

\* What a write-free transaction read of the two skew keys, B at the horizon
\* its get_for_update was served at, if any.
SkewSeen(t) ==
  \* A pair: key A as of its snapshot, and key B as of its snapshot or, after a get_for_update, as
  \* of the sequence that read was served at.
  <<ValueAt(SkewA, snap[t]),
    IF forUpdate[t] = {} THEN ValueAt(SkewB, snap[t])
    ELSE ValueAt(SkewB, (CHOOSE f \in forUpdate[t] : TRUE)[2])>>

\* Some single point in time between its snapshot and now shows both values
\* it read.
Consistent(t) ==
  \* There is a sequence s, from its snapshot up to now, at which both keys held exactly what it
  \* read.
  \E s \in snap[t]..clock : <<ValueAt(SkewA, s), ValueAt(SkewB, s)>> = SkewSeen(t)

\* The write-free transactions that read the skew keys.
SkewReaders == ReadOnlys \cup Promoters \cup ForUpdateReaders \cup Reporters

\* Whether t's level promises that what it read is one point in time. Every optimistic transaction
\* reads one snapshot. A pessimistic one at ReadCommitted or SnapshotIsolation does not: its
\* get_for_update reads the newest value by design, and that level checks nothing that would tie the
\* two reads together.
PromisesOnePoint(t) == ~(Pessimistic(t) /\ LevelOf(t) \in {"ReadCommitted", "SnapshotIsolation"})

\* The reads a write-free transaction's level promises to check, each as <<key, the sequence it was
\* served at>>: the commit must refuse when one of them no longer holds. This is the promise of
\* each level, written out apart from the commit rule (KeptReads) so a planted bug in the rule
\* cannot change it.
PromisedChecks(t) ==
  \* plain: every key it read plainly, at its snapshot.
  LET plain == {<<k, snap[t]>> : k \in tracked[t]}
  \* At RepeatableRead and Serializable, and for a pessimistic transaction at DefraLevel: every read.
  IN CASE LevelOf(t) \in {"RepeatableRead", "Serializable"} -> plain \cup forUpdate[t]
       \* (The pessimistic DefraLevel case, which validates as at RepeatableRead.)
       [] LevelOf(t) = "DefraLevel" /\ Pessimistic(t)        -> plain \cup forUpdate[t]
       \* At ReadCommitted: none.
       [] LevelOf(t) = "ReadCommitted"                        -> {}
       \* At SnapshotIsolation, and under DefraLevel's write-free relaxation: the get_for_update reads.
       [] OTHER                                               -> forUpdate[t]

\* THE READ-ONLY ANOMALY'S SERIAL ORDERS. A balance pair is <<A, B>>: skew key A and skew key B.

\* What running writer t alone does to the pair s: the deposit raises B by one, the withdrawal puts A
\* to A + B.
BankStep(t, s) == IF t \in Depositors THEN <<s[1], s[2] + 1>> ELSE <<s[1] + s[2], s[2]>>

\* Run the writers of list o one at a time, first first, from the pair s.
RECURSIVE BankRun(_, _)
\* (The run: with no writer left, the pair as it is; otherwise the first writer's step, then the
\* rest.)
BankRun(o, s) == IF o = <<>> THEN s ELSE BankRun(Tail(o), BankStep(Head(o), s))

\* The pair before any commit.
BankStart == <<InitStore[SkewA], InitStore[SkewB]>>

\* Every order of the bank's writers that committed so far: each a list naming each of them once.
BankOrders ==
  \* done: the withdrawals and deposits that committed.
  LET done == {t \in Withdrawers \cup Depositors : phase[t] = "committed"}
  \* The lists of length |done| over done that repeat no writer.
  IN {o \in [1..Cardinality(done) -> done] :
        \A i, j \in 1..Cardinality(done) : i # j => o[i] # o[j]}

\* What report r read fits a serial order of the writers committed so far: some order of them, run
\* one at a time, leaves exactly the balances the database holds (so each writer read in that order
\* what it really read), and passes, before or after one of its steps, through the pair r read.
FitsSerialOrder(r) ==
  \* Some order of the committed writers
  \E o \in BankOrders :
     \* reproduces the balances held now,
     /\ BankRun(o, BankStart) = <<store[SkewA], store[SkewB]>>
     \* and after its first i steps, for some i, shows the pair the report read.
     /\ \E i \in 0..Len(o) : BankRun(SubSeq(o, 1, i), BankStart) = SkewSeen(r)

\* What a log reader saw of the log: positions 1..head at its snapshot, and,
\* under MUTANT OwnAppendVisible, its own entry at the next position.
LogSeen(t) ==
  \* h: the head at its snapshot.
  LET h == ValueAt(LogHead, snap[t])
  \* A list: positions 1 to h hold the entries as of its snapshot; under the planted bug, position h
  \* + 1 holds its own id.
  IN [p \in 1..(h + IF Mutant = "OwnAppendVisible" THEN 1 ELSE 0) |->
        IF p <= h THEN ValueAt(LogEntry(p), snap[t]) ELSE t]

\* The grants present at sequence s.
GrantsAt(s) == {i \in {1, 2} : ValueAt(AclKey(i), s) # Absent}

\* [3.14] What the transaction did with the reason's key is what `mine`
\* says.
Did(t, mine, k) ==
  \* A read or a presence read: the key is one it recorded, or the part key for a transaction that
  \* reads by parts.
  CASE mine \in {"Read", "ReadPresence"} -> k \in tracked[t] \/ (k = PartKey /\ t \in PartTxns)
    \* A read by parts: the part key, for such a transaction.
    [] mine = "ReadParts"        -> k = PartKey /\ t \in PartTxns
    \* A get_for_update: one of the reads it was served.
    [] mine = "ReadForUpdate"    -> \E f \in forUpdate[t] : f[1] = k
    \* Scanned then wrote: a key it writes or merges into.
    [] mine = "ScannedThenWrote" -> k \in written[t] \cup merged[t]
    \* A scanned range: the transaction is a checker and the key lies in the grant range.
    [] mine = "ScannedRange"     -> t \in Checkers /\ k[1] = AclRange
    \* A put: a key it writes with a value.
    [] mine = "Put"              -> k \in written[t] /\ intended[t][k] # Absent
    \* A delete: a key it writes as absent.
    [] mine = "Delete"           -> k \in written[t] /\ intended[t][k] = Absent
    \* A merge: a key it merges into.
    [] mine = "Merge"            -> k \in merged[t]
    \* Any other name: no.
    [] OTHER                     -> FALSE

\* [3.14] A write of kind w.kind can decide a race for access `mine`: a
\* presence read loses only to a removal, a projected read only to a
\* replacement or an operand touching its parts, a blind merge only to a
\* replacement; any write can decide the others.
Decides(mine, w, parts) ==
  \* A presence read loses only to a removal.
  CASE mine = "ReadPresence" -> w.kind \in {"Delete", "RangeDelete"}
    \* A read by parts loses to a replacement, or to an operand touching one of its parts.
    [] mine = "ReadParts"    -> w.kind \in Replacing \/ w.touch \cap parts # {}
    \* A blind merge loses only to a replacement.
    [] mine = "Merge"        -> w.kind \in Replacing
    \* Every other access loses to any write.
    [] OTHER                 -> TRUE

\* The reason r of t's abort holds against the history at the abort: what
\* t did with the key is what `mine` says, and a write of the key newer than
\* the anchor, of kind `theirs` at sequence `latest`, can decide that race.
ReasonHolds(t, r) ==
  \* The reason has the right shape.
  /\ r \in [key : Keys, mine : Accesses, theirs : Kinds, observed : Nat, latest : Nat,
            parts : SUBSET Parts]
  \* The transaction did with the key what the reason says.
  /\ Did(t, r.mine, r.key)
  \* The history holds a write of that key, at that sequence, of that kind,
  /\ \E w \in hist : /\ w.key = r.key /\ w.seq = r.latest /\ w.kind = r.theirs
                     \* newer than where the transaction looked, and able to decide this kind of
                     \* race.
                     /\ w.seq > r.observed /\ Decides(r.mine, w, r.parts)

\* A refusal the relaxations promise never happens, or a reason that does not
\* hold.
AbortFlags(t) ==
  \* A reason that does not hold is flagged.
  (IF ReasonHolds(t, ReasonOf(t)) THEN {} ELSE {"BadReason"})
  \* A part reader that found the key and was refused although every newer write is an operand not
  \* touching part 1: a needless refusal.
  \cup (IF /\ t \in PartReaders
           /\ Found(PartKey, snap[t])
           /\ \A w \in After(PartKey, snap[t]) : w.kind = "Merge" /\ 1 \notin w.touch
        THEN {"PartsRefusedNeedlessly"} ELSE {})
  \* A value reader refused although the key holds the value it read and its newest write is not an
  \* operand: a needless refusal.
  \cup (IF /\ t \in ValueReaders
           /\ store[VersionKey] = ValueAt(VersionKey, snap[t])
           /\ ~NewestIsOperand(VersionKey)
        THEN {"IdenticalRewriteRefused"} ELSE {})

\* A committed decision on inputs that changed before the commit.
CommitFlags(t) ==
  \* A holder whose note no longer matches whether the block is stored.
  (IF t \in Holders /\ (store[Shared] # Absent) # Found(Shared, snap[t])
   THEN {"HoldStale"} ELSE {})
  \* A part reader whose decision inputs (does the key exist, what is part 1) changed since its
  \* snapshot.
  \cup (IF t \in PartReaders
           /\ PartDecision(store[PartKey]) # PartDecision(ValueAt(PartKey, snap[t]))
        THEN {"PartsStale"} ELSE {})
  \* A no-part decider whose decision inputs (does the key exist, what is part 1) changed since its
  \* snapshot: it decided on a read it had named no part of.
  \cup (IF t \in NoPartDeciders
           /\ PartDecision(store[PartKey]) # PartDecision(ValueAt(PartKey, snap[t]))
        THEN {"PartsStale"} ELSE {})
  \* A part rewriter whose key changed since its snapshot.
  \cup (IF t \in PartRewriters /\ store[PartKey] # ValueAt(PartKey, snap[t])
        THEN {"PartsStale"} ELSE {})
  \* A value reader whose key holds a different value now.
  \cup (IF t \in ValueReaders /\ store[VersionKey] # ValueAt(VersionKey, snap[t])
        THEN {"ValueStale"} ELSE {})
  \* A write-free transaction whose two reads fit no single point in time, where its level promises
  \* one.
  \cup (IF t \in SkewReaders /\ PromisesOnePoint(t) /\ ~Consistent(t) THEN {"Skew"} ELSE {})
  \* A write-free transaction one of whose reads its level promises to check no longer holds the
  \* value it read when it commits.
  \cup (IF WriteFree(t) /\ \E c \in PromisedChecks(t) : ValueAt(c[1], c[2]) # store[c[1]]
        THEN {"WriteFreeStale"} ELSE {})
  \* A report whose pair fits no serial order of the writers committed before it.
  \cup (IF t \in Reporters /\ ~FitsSerialOrder(t) THEN {"ReadOnlyAnomaly"} ELSE {})
  \* A log decider whose head moved.
  \cup (IF t \in LogDeciders /\ store[LogHead] # ValueAt(LogHead, snap[t])
        THEN {"LogDecisionStale"} ELSE {})
  \* A log reader one of whose seen entries is not what the log holds after its commit.
  \cup (IF t \in LogReaders /\ \E p \in DOMAIN LogSeen(t) : NewValue(t, LogEntry(p)) # LogSeen(t)[p]
        THEN {"PhantomAppend"} ELSE {})
  \* An own-writer whose commit leaves a value other than the one it read back.
  \cup (IF t \in OwnWriters /\ NewValue(t, OwnKey) # OwnRead(t) THEN {"OwnMismatch"} ELSE {})
  \* A checker whose range holds different grants now.
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
  \* The commit puts or deletes the counter:
  IF CounterKey \in written[t]
    \* the contract's base becomes what it stores,
    THEN /\ cbase'  = intended[t][CounterKey]
         \* at this commit's sequence;
         /\ cepoch' = n
         \* the increments it could not see (committed after its snapshot) stay counted,
         /\ cinc'   = {s \in cinc : s > snap[t]}
                      \* and its own merge on top counts too.
                      \cup (IF CounterKey \in merged[t] THEN {n} ELSE {})
  \* The commit only merges into the counter:
  ELSE IF CounterKey \in merged[t]
    \* the increment counts when no reset committed after it began,
    THEN /\ cinc' = IF \/ snap[t] >= cepoch
                       \* or when it read the counter and the count is still what it read;
                       \/ CounterKey \in tracked[t] /\ store[CounterKey] = seen[t]
                    \* otherwise it is not counted.
                    THEN cinc \cup {n} ELSE cinc
         \* The base and its sequence stay.
         /\ UNCHANGED <<cbase, cepoch>>
  \* A commit that does not touch the counter changes nothing here.
  ELSE UNCHANGED <<cbase, cepoch, cinc>>

\* An abort: a check failed (Conflicts), so the transaction is refused with a reason and writes
\* nothing. Shared by the two kinds of commit below.
Abort(t) ==
  \* The transaction ends refused.
  /\ phase'  = [phase EXCEPT ![t] = "aborted"]
  \* A bad reason or a needless refusal is flagged.
  /\ flags'  = flags \cup AbortFlags(t)
  \* A blind increment refused although no reset committed after it began: needless.
  /\ needlessRefusal' = (needlessRefusal \/ (t \in Incrementers /\ snap[t] >= cepoch))
  \* A merger refused although every newer write to its keys stored what it writes: a
  \* refused duplicate.
  /\ dupRefused' = (dupRefused \/
                    (t \in Mergers /\ \A k \in written[t] :
                        After(k, snap[t]) # {} => store[k] = intended[t][k]))
  \* The history drops what no open snapshot can read any more.
  /\ hist'   = Prune(hist, phase', clock)
  \* An abort writes nothing and takes no receipt.
  /\ UNCHANGED <<clock, store, parents, stale, wrongReceipt, cbase, cepoch, cinc, receipt>>

\* A commit that writes (RegolithEngine::commit_optimistic, src/engine/commit/mod.rs): a slot of
\* the commit pipeline, decided against everything committed before it. Abort with a reason when a
\* check fails, or apply every write at the next sequence and add it to the history. On a database
\* latched read-only it is refused before any check (ensure_writable) and writes nothing.
CommitWriting(t) ==
  \* A latched database refuses the commit:
  IF latched
    \* it ends failed,
    THEN /\ phase' = [phase EXCEPT ![t] = "failed"]
         \* the history drops what no open snapshot can read any more,
         /\ hist'  = Prune(hist, phase', clock)
         \* and nothing else changes: no write, no flag, no receipt.
         /\ UNCHANGED <<clock, store, flags, parents, stale, dupRefused, wrongReceipt,
                        needlessRefusal, cbase, cepoch, cinc, receipt>>
  \* A check failed: the transaction aborts.
  ELSE IF Conflicts(t) THEN Abort(t)
  \* Every check passed: the transaction commits.
  ELSE /\ phase'    = [phase EXCEPT ![t] = "committed"]
       \* It takes the next sequence.
       /\ clock'    = clock + 1
       \* Its receipt names that sequence.
       /\ receipt'  = [receipt EXCEPT ![t] = clock + 1]
       \* Every key gets its new value.
       /\ store'    = [k \in Keys |-> NewValue(t, k)]
       \* Its writes join the history, which is then pruned.
       /\ hist'     = Prune(hist \cup Records(t, clock + 1), phase', clock + 1)
       \* A decision on changed inputs is flagged.
       /\ flags'    = flags \cup CommitFlags(t)
       \* The DAG bookkeeping:
       /\ parents'  = IF t \in Appenders
                        \* an appender's block records the heads it marked as its parents;
                        THEN [parents EXCEPT ![t] = {h \in Blocks : MarkerKey(h, t) \in written[t]}]
                        \* a merger that wrote the remote block
                        ELSE IF t \in Mergers /\ written[t] # {}
                        \* records the parents the remote block names;
                        THEN [parents EXCEPT ![Remote] = RemoteParents]
                        \* anyone else changes nothing.
                        ELSE parents
       \* A write built from a definition that has since changed is noted as stale.
       /\ stale'    = (stale \/ ((t = Writer \/ t \in Migrators) /\ store[DefKey] # seen[t]))
       \* A read-merger whose count moved is noted as a wrong receipt.
       /\ wrongReceipt' = (wrongReceipt \/ (t \in ReadMergers /\ store[CounterKey] # seen[t]))
       \* The counter's contract is updated.
       /\ Count(t, clock + 1)
       \* No refusal happened.
       /\ UNCHANGED <<needlessRefusal, dupRefused>>

\* A commit that writes nothing (RegolithEngine::commit_write_free, src/engine/commit/mod.rs; routed
\* there by Transaction::drain_for_commit at every level): it takes no slot of the pipeline and no
\* sequence. It checks what its level checks (KeptReads, ScanDecider) against the newest published
\* state, the clock, in this one step, and is placed there: every commit made before it comes first,
\* every later one after it, and it writes nothing a later one could miss. A latched database
\* commits it too (ensure_open, not ensure_writable). Its receipt is its snapshot.
CommitWriteFree(t) ==
  \* Under the planted bug WriteFreeRefusedWhenLatched a latched database refuses it, as the 0.1.x
  \* engine did: it ends failed and nothing else changes.
  IF latched /\ Mutant = "WriteFreeRefusedWhenLatched"
    \* (It ends failed,
    THEN /\ phase' = [phase EXCEPT ![t] = "failed"]
         \* the history drops what no open snapshot can read any more,
         /\ hist'  = Prune(hist, phase', clock)
         \* and nothing else changes.)
         /\ UNCHANGED <<clock, store, flags, parents, stale, dupRefused, wrongReceipt,
                        needlessRefusal, cbase, cepoch, cinc, receipt>>
  \* A check failed: the transaction aborts.
  ELSE IF Conflicts(t) THEN Abort(t)
  \* Every check passed: the transaction commits.
  ELSE /\ phase'    = [phase EXCEPT ![t] = "committed"]
       \* It takes no sequence (under the planted bug WriteFreeTakesSequence it takes the next one).
       /\ clock'    = IF Mutant = "WriteFreeTakesSequence" THEN clock + 1 ELSE clock
       \* Its receipt names its snapshot (under the planted bug ReceiptAtHorizon, the horizon it was
       \* checked at).
       /\ receipt'  = [receipt EXCEPT ![t] = IF Mutant = "ReceiptAtHorizon" THEN clock
                                              ELSE snap[t]]
       \* The history drops what no open snapshot can read any more.
       /\ hist'     = Prune(hist, phase', clock')
       \* A decision on changed inputs is flagged.
       /\ flags'    = flags \cup CommitFlags(t)
       \* It writes nothing: the store and every piece of write bookkeeping stay as they were.
       /\ UNCHANGED <<store, parents, stale, dupRefused, wrongReceipt, needlessRefusal,
                      cbase, cepoch, cinc>>

\* The commit. A promoter and a for-update reader commit only after their get_for_update.
Commit(t) ==
  \* The transaction is open.
  /\ phase[t] = "open"
  \* A promoter has made its late read,
  /\ t \in Promoters => forUpdate[t] # {}
  \* and a for-update reader its read.
  /\ t \in ForUpdateReaders => forUpdate[t] # {}
  \* One that writes nothing takes the write-free commit; any other is a slot of the pipeline.
  /\ IF WriteFree(t) THEN CommitWriteFree(t) ELSE CommitWriting(t)
  \* The latch is not a commit's to set.
  /\ UNCHANGED latched
  \* What the transactions recorded stays as it was.
  /\ UNCHANGED <<snap, tracked, runs, written, intended, merged, seen, ops, forUpdate>>

\* Db::delete_range over the counter's range: a plain write, applied at once
\* and validated against nothing. A covering range tombstone is the newest
\* write of each key it covers (latest_version_in_view) and replaces each
\* one (RegolithEngine::landed_above; MUTANT RangeDeleteNotReplacement
\* forgets that, in MergeDecider). Applied at once, it saw every increment
\* it discards.
Clear(c) ==
  \* covered: every key of the counter's range.
  LET covered == {k \in Keys : k[1] = CounterRange}
  \* The range delete has not run yet.
  IN /\ phase[c]  = "idle"
     \* It is applied at once.
     /\ phase'    = [phase EXCEPT ![c] = "committed"]
     \* It takes the next sequence.
     /\ clock'    = clock + 1
     \* Every covered key becomes absent.
     /\ store'    = [k \in Keys |-> IF k \in covered THEN Absent ELSE store[k]]
     \* One RangeDelete record per covered key joins the history, which is then pruned.
     /\ hist'     = Prune(hist \cup {[seq |-> clock + 1, key |-> k, kind |-> "RangeDelete",
                                      val |-> Absent, touch |-> Parts] : k \in covered},
                          phase', clock + 1)
     \* The counter's contract restarts from an absent counter,
     /\ cbase'    = Absent
     \* at this sequence,
     /\ cepoch'   = clock + 1
     \* with nothing counted on top.
     /\ cinc'     = {}
     \* Its receipt names that sequence.
     /\ receipt'  = [receipt EXCEPT ![c] = clock + 1]
     \* Nothing else changes.
     /\ UNCHANGED <<snap, tracked, runs, written, intended, merged, seen, ops, forUpdate,
                    flags, parents, stale, dupRefused, wrongReceipt, needlessRefusal, latched>>

\* A failure latches the database read-only (RegolithEngine::latch, src/engine/mod.rs): a log write
\* that failed, a callback that panicked inside the ordered step. It can happen at any moment, and
\* once.
Latch(l) ==
  \* This failure has not happened yet.
  /\ phase[l]  = "idle"
  \* It happens now; "committed" here only means "has happened".
  /\ phase'    = [phase EXCEPT ![l] = "committed"]
  \* The database is latched read-only from now on.
  /\ latched'  = TRUE
  \* Nothing else changes: the store, the history and every transaction's record stay.
  /\ UNCHANGED <<clock, store, hist, snap, tracked, runs, written, intended, merged, seen, ops,
                 forUpdate, flags, parents, stale, dupRefused, wrongReceipt, needlessRefusal,
                 cbase, cepoch, cinc, receipt>>

\* Every step: a begin, a commit, a late read, a range delete or a latch.
Next == \/ \E t \in Txns \ (Clearers \cup Latchers) : Begin(t) \/ Commit(t)
        \* a promoter makes its late read,
        \/ \E p \in Promoters : Promote(p)
        \* a for-update reader makes its read,
        \/ \E r \in ForUpdateReaders : ReadForUpdate(r)
        \* a plain range delete runs,
        \/ \E c \in Clearers : Clear(c)
        \* or a failure latches the database.
        \/ \E l \in Latchers : Latch(l)

\* Every behaviour, with weak fairness so every enabled step is taken.
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----------------------------------------------------------------------------
\* The shape of a history record.
Records_ == [seq : Nat, key : Keys, kind : Kinds, val : Nat, touch : SUBSET Parts]

\* Every variable holds what its comment says.
TypeOK ==
  \* The sequence is a number.
  /\ clock \in Nat
  \* Every key holds a number.
  /\ store \in [Keys -> Nat]
  \* Every history entry has the record shape.
  /\ hist \subseteq Records_
  \* Every transaction is in one of the five phases.
  /\ phase \in [Txns -> {"idle", "open", "committed", "aborted", "failed"}]
  \* Reads, writes and merges name keys.
  /\ \A t \in Txns : tracked[t] \subseteq Keys /\ written[t] \subseteq Keys /\ merged[t] \subseteq Keys
  \* Every stretch is a pair of keys, the first at or before the last.
  /\ \A t \in Txns : \A s \in runs[t] : s \in Keys \X Keys /\ KeyLeq(s[1], s[2])
  \* What a write was built from is a number.
  /\ seen \in [Txns -> Nat]
  \* A get_for_update read is a key with a sequence.
  /\ \A t \in Txns : forUpdate[t] \subseteq Keys \X Nat
  \* Flags are known names.
  /\ flags \subseteq FlagNames
  \* The counter's contract holds numbers.
  /\ cbase \in Nat /\ cepoch \in Nat /\ cinc \subseteq Nat
  \* The stale mark is a yes or a no.
  /\ stale \in BOOLEAN
  \* Every receipt is a sequence number.
  /\ receipt \in [Txns -> Nat]
  \* The latch is a yes or a no.
  /\ latched \in BOOLEAN

\* THE HEADLINE for the head set. An append that did its scan, built its
\* block and asked to commit is never turned away by a sweep that reclaimed
\* keys its scan yielded: the live set it derived was unchanged by that.
\* Rules out, for example: appender 3 scans the heads, the pruner then deletes a head key that scan
\* yielded, and the append is refused for it. The store needs appends to land: under a busy sweep a
\* refused append would be retried without end.
INV_AppendsCommit == \A a \in Appenders : phase[a] # "aborted"

\* THE HEADLINE for point reads. No write derived from the definition (a
\* document, a migration) commits against a definition that was replaced
\* after it was read.
\* Rules out, for example: the writer reads definition version 1, the patcher commits version 2, and
\* the writer's document, built from version 1, still commits. The document would disagree with the
\* definition it claims to follow.
INV_NoStaleDefinition == ~stale

\* The derived head set is the DAG's tips: the committed blocks no committed
\* block names as a parent. Holds at every level.
\* The blocks that are part of the DAG now: the seed, each committed appender's block, and the
\* remote block once a merger wrote it.
CommittedBlocks == {Seed} \cup {a \in Appenders : phase[a] = "committed"}
                   \cup (IF \E m \in Mergers : phase[m] = "committed" /\ written[m] # {}
                         THEN {Remote} ELSE {})
\* The DAG's tips: the committed blocks that no committed block names as a parent.
DagHeads == {b \in CommittedBlocks : ~\E c \in CommittedBlocks : b \in parents[c]}
\* The promise: the head set a scan derives from the keys is exactly those tips. Rules out a
\* superseded block that still looks like a head, and a real head that is hidden. Every merge of the
\* CRDT starts from the head set, so it must be exact.
INV_HeadsExact == Heads(Stored) = DagHeads

\* A merger is never refused when every newer write to its keys stored
\* exactly what it writes: applying a block another transaction already
\* applied lands. One whose keys a sweep reclaimed meanwhile is refused, and
\* must be: an append may have superseded the block it applies and the sweep
\* reclaimed that head, so writing the head key back would resurrect a
\* superseded head (INV_HeadsExact).
\* Rules out, for example: two peers deliver the same block, transactions 7 and 8 both apply it, and
\* the second is refused although it writes byte for byte what the first wrote.
INV_DuplicateMergesCommit == ~dupRefused

\* The counter holds the value the last put, delete or range delete stored,
\* plus one for every increment counted since (Count). A put or delete that
\* commits over an increment it did not see loses that increment; an
\* increment that commits over a reset it did not see survives the reset.
\* Either way the store and the contract part.
\* Rules out, for example: an increment that commits over a reset it did not see and is lost, or one
\* that is counted twice. The counter must equal what running the commits one at a time would leave.
INV_CounterExact == store[CounterKey] = cbase + Cardinality(cinc)

\* A read-merger commits only while the count it read is still the count:
\* its receipt is then the count its own merge produced.
\* Rules out, for example: a read-merger reads 5, another increment commits, and the first still
\* commits with the receipt 6 although its merge really produced 7.
INV_ReceiptsExact == ~wrongReceipt

\* A blind increment is refused only when committing it would break the
\* counter, a put, delete or range delete having committed after it began,
\* so concurrent increments never refuse each other.
\* Rules out, for example: two blind increments run at once and one is refused. They commute, so a
\* refusal would only cost a retry.
INV_IncrementsCommitUnlessReplaced == ~needlessRefusal

\* E17. Every stored pin or holder reference names a stored block: a
\* collection never deletes a block from under a reference.
\* Rules out, for example: the collector sees no pin and deletes the block while a linker, who read
\* the block as present, commits a pin to it. The pin would point at nothing.
INV_NoDanglingReference ==
  \* If some pin is stored or some holder's note says present,
  (\E l \in Linkers : store[PinKey(l)] # Absent) \/ (\E h \in Holders : store[HoldKey(h)] = 1)
    \* then the shared block is stored.
    => store[Shared] # Absent

\* Two creates of one block both commit: a linker is never refused.
\* Rules out, for example: two transactions create the same block (same bytes, same key) and one is
\* refused.
INV_LinksCommit == \A l \in Linkers : phase[l] # "aborted"

\* A holder's record (present or missing) is still true at its commit.
\* Rules out, for example: a holder notes "present", the collector deletes the block, and the
\* holder's note still commits.
INV_HoldsCurrent == "HoldStale" \notin flags

\* No projected reader commits after the key's existence or a part its
\* decision used changed.
\* Rules out, for example: a reader decides on part 1, another commit changes part 1 or deletes the
\* key, and the reader still commits.
INV_PartsCurrent == "PartsStale" \notin flags

\* A part reader that found the key is not refused when every newer write is
\* an operand that touches only part 2: the relaxation projected reads exist
\* for.
\* Rules out, for example: a reader of part 1 is refused because somebody merged into part 2 only.
INV_PartsRelaxed == "PartsRefusedNeedlessly" \notin flags

\* No value reader commits after the value it read changed.
\* Rules out, for example: a reader decides on value 1, the key becomes 2, and the reader still
\* commits.
INV_ValueReadsCurrent == "ValueStale" \notin flags

\* No value reader is refused while the key holds the value it read, the
\* newest write being a put: an identical rewrite, or a value that came back.
\* Rules out, for example: a save rewrites the key with the same bytes and a concurrent reader is
\* refused for it.
INV_IdenticalRewritesCommit == "IdenticalRewriteRefused" \notin flags

\* A write-free transaction whose level checks none of its reads never conflicts: at ReadCommitted,
\* at SnapshotIsolation, and under DefraLevel's write-free relaxation, a transaction that only read
\* plainly is never refused.
\* Rules out, for example: a report that only reads is refused at SnapshotIsolation because a writer
\* changed what it read. It has nothing to lose: it read one snapshot and counts as having run there.
INV_WriteFreeCommits ==
  \* Every read-only transaction and every report whose level checks no plain read
  \A r \in ReadOnlys \cup Reporters :
     \* (ReadCommitted, SnapshotIsolation, or DefraLevel's optimistic rules)
     LevelOf(r) \in {"ReadCommitted", "SnapshotIsolation"} \/ Classified(r)
       \* is never refused.
       => phase[r] # "aborted"

\* Every committed write-free transaction read the state of one point in
\* time: no read skew. A pessimistic one at ReadCommitted or SnapshotIsolation is left out: its
\* get_for_update reads the newest value by design, and its level promises nothing more.
\* Rules out, for example: a write-free transaction reads key A before a commit and key B after it,
\* two values that no single moment ever showed together.
INV_WriteFreeConsistent == "Skew" \notin flags

\* E50. A write-free commit is placed at the published horizon: every read its level promises to
\* check (PromisedChecks) still holds, when it commits, the value it read.
\* Rules out, for example: at Serializable, a transaction reads key A, a writer commits a new A, and
\* the transaction still commits with the old A, as if no check had run.
INV_WriteFreeAtHorizon == "WriteFreeStale" \notin flags

\* E50, Fekete, O'Neil and O'Neil (2004). No report commits a pair of balances that no serial order
\* of the withdrawals and deposits committed before it passes through.
\* Rules out, for example: the withdrawal read (1, 1) and the deposit committed B = 2; the report
\* read (1, 2); the withdrawal committed A = 2 from the sum it read; then the report commits (1, 2),
\* a sheet that shows the deposit without the withdrawal although the withdrawal had to come first.
INV_NoReadOnlyAnomaly == "ReadOnlyAnomaly" \notin flags

\* E50. A commit that writes nothing takes no sequence: the clock counts exactly the commits that
\* wrote (and the plain range deletes).
\* Rules out, for example: two reports commit and the next writer's sequence is two higher than it
\* would be, as if the reports had written.
INV_WriteFreeTakesNoSequence ==
  \* The clock equals the number of
  clock = Cardinality({t \in Txns :
                       \* commits that have happened
                       /\ phase[t] = "committed"
                       \* and wrote: a plain range delete, or a transaction (not a latch) that is not
                       \* write-free.
                       /\ (t \in Clearers \/ (t \notin Latchers /\ ~WriteFree(t)))})

\* E50, the operator's decision (L59). A committed write-free transaction's receipt is the snapshot
\* it read at.
\* Rules out, for example: a report began at sequence 3, two writers committed, and its receipt
\* says 5.
INV_WriteFreeReceipt ==
  \* For every transaction that is not a range delete and not a latch:
  \A t \in Txns \ (Clearers \cup Latchers) :
     \* if it committed and wrote nothing,
     phase[t] = "committed" /\ WriteFree(t)
       \* has its snapshot as its receipt.
       => receipt[t] = snap[t]

\* E50, the operator's decision (L59). A database latched read-only refuses only commits that
\* write: a write-free commit writes nothing, so the latch never fails it.
\* Rules out, for example: a failure latches the database and a report that only read is then
\* refused although it would change nothing.
INV_LatchRefusesOnlyWrites == \A t \in Txns : phase[t] = "failed" => ~WriteFree(t)

\* Appends and log reads are never validated, so no appender or log reader
\* is refused.
\* Rules out, for example: two appends race and one is refused. The commit itself orders appends, so
\* none has to lose.
INV_LogNeverConflicts == \A t \in LogAppenders \cup LogReaders : phase[t] # "aborted"

\* The log holds entries 1..head, and nothing beyond: positions are dense.
INV_LogDense ==
  \* At every position: an entry is stored exactly when the position is at or below the head. Rules
  \* out an entry at position 3 with nothing at position 2, and a head pointing past the last entry.
  \A p \in LogPositions : (store[LogEntry(p)] # Absent) <=> p <= store[LogHead]

\* Every entry a log reader saw is in the log at its commit, at the position
\* it saw: a reader never sees a position its own append did not get.
\* Rules out, for example: a reader sees its own entry at position 2, another append commits first,
\* and the reader's entry really lands at position 3.
INV_NoPhantomAppend == "PhantomAppend" \notin flags

\* No decision on the log's length went stale. Log reads are exempt, so a
\* caller must not decide on them [3.1]: this fails by design.
\* Shows, for example: a decider reads "the log has 1 entry", an append commits, and the decider's
\* decision commits anyway.
INV_LogDecisionsCurrent == "LogDecisionStale" \notin flags

\* A merge before a commutative scan stays blind: no tally merger is
\* refused, and no increment is lost.
\* Rules out, for example: two tally mergers run at once and one is refused although merges commute.
INV_TallyMergesCommit == \A m \in TallyMergers : phase[m] # "aborted"
\* The tally key holds exactly the number of tally mergers that committed: no merge is lost and none
\* counts twice.
INV_TallyExact == store[TallyKey] = Cardinality({m \in TallyMergers : phase[m] = "committed"})

\* The value a commit leaves on the own key is the value its transaction
\* read back through its own writes.
\* Rules out, for example: a transaction merges, then puts 5, reads back 5, and its commit stores 6
\* because it applied the merge after the put.
INV_ReadYourOwnWrites == "OwnMismatch" \notin flags

\* No checker commits after a grant was revoked or a new one appeared.
\* Rules out, for example: a checker counts one grant, the grant is revoked (or a second one
\* appears), and the checker's decision still commits.
INV_ScanDecisionsCurrent == "ScanStale" \notin flags

\* A scan inside a commutative prefix records nothing, so a joiner's own key
\* and its rewrite of the seat are blind writes: no joiner is refused.
\* Rules out, for example: two joiners add themselves at once and one is refused over the seat,
\* which both wrote with the same bytes.
INV_JoinsCommit == \A j \in Joiners : phase[j] # "aborted"

\* Concurrent writers inside the prefix leave the union [3.1]: the roster
\* holds the key of every joiner that committed, and of no other.
INV_RosterIsUnion ==
  \* For every joiner: its key is stored exactly when it committed. Rules out a committed joiner
  \* whose key another joiner's commit wiped, and a key left by a joiner that was refused.
  \A j \in Joiners : (store[MemberKey(j)] # Absent) <=> phase[j] = "committed"

\* At most one claimer's record says the seat is its. A scan inside a
\* commutative prefix is exempt, so a caller must not decide an exclusive
\* outcome on it [3.1, 3.2]: with the prefix declared this fails by design.
\* Shows, for example: two claimers scan the roster, both see the seat free, both put the seat with
\* the same bytes and both commit, each believing the one seat is its own.
INV_SeatExclusive == Cardinality({c \in Claimers : store[OutKey(c)] # Absent}) <= 1

\* A read by no parts is never validated, so no peeker is refused, whatever
\* is written to the key it read.
\* Rules out, for example: a peeker looks at the part key, somebody deletes the key, and the peeker
\* is refused although it decided on nothing it saw.
INV_PeeksCommit == \A p \in Peekers : phase[p] # "aborted"

\* [3.14] Every abort's reason names a key the transaction did what `mine`
\* says with, and a committed write of that key newer than the anchor, with
\* the kind `theirs` and the sequence `latest`, that can decide such a race
\* (ReasonHolds, checked when the transaction aborts).
\* Rules out, for example: an abort that blames a write which could not have caused it, such as an
\* operand named as the reason a blind merge failed.
INV_ReasonsExact == "BadReason" \notin flags

\* State constraints that spend a config's states on one workload: the
\* transactions of every other one stay idle.
CounterWorkloadOnly ==
  \* Every transaction outside the counter workload
  \A t \in Appenders \cup {Pruner, Writer, Patcher} \cup Mergers \cup Migrators :
     \* never begins.
     phase[t] = "idle"
\* The writer, the patcher and the migrators only.
DefinitionWorkloadOnly ==
  \* Everything but the writer, the patcher and the migrators never begins.
  \A t \in Appenders \cup {Pruner} \cup Mergers \cup CounterTxns : phase[t] = "idle"
\* The writer and the patcher touch no key of the DAG and read none through a
\* scan, so idling them loses no interleaving of the head set.
HeadsWorkloadOnly ==
  \* The writer, the patcher, the counter transactions and the migrators never begin.
  \A t \in {Writer, Patcher} \cup CounterTxns \cup Migrators : phase[t] = "idle"
\* The later workloads touch no key of the first ones.
NewWorkloadOnly == \A t \in OldTxns : phase[t] = "idle"

\* Under the level that refuses no append, every append lands.
EventuallyAllAppendsCommit == <>[](\A a \in Appenders : phase[a] = "committed")

====
