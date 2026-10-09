---- MODULE RepeatableReadCommit ----
\* The state and the commit rule of the RepeatableRead model. The root
\* module, RepeatableRead.tla, extends this one with the workloads, the
\* actions and the invariants; read its header first. This module holds what
\* every workload shares: the constants, the key layout, the variables, the
\* write history, and the rule an optimistic commit applies at each level and
\* to each key class. It is split out only to keep each file readable.
\*
\* WHERE EACH RULE COMES FROM. Rules marked CODE are transcribed from the
\* engine and keep its shape; rules marked PLAN are specified from
\* docs/plans/defralevel.md before the code exists (section numbers in
\* brackets). A RED config per rule breaks it (RepeatableRead.tla, MUTANTS).
\*
\*   CODE  Transaction::observe, TxnScanStream::yield_cursor,
\*         Transaction::validation_set, scan_range::cover    src/transaction*
\*         Point reads, scan stretches, which reads a level validates, and
\*         the written keys a stretch covers. Unchanged from #237.
\*   CODE  policy::run_is_commutative                       src/transaction/policy.rs
\*         A stretch inside one commutative prefix records nothing.
\*   CODE  policy::exempt_content_addressed (E17, D7)       src/transaction/policy.rs
\*         A put or merge of a content-addressed key is never validated,
\*         and neither is any read of a key the commit puts or merges. A
\*         delete of one is validated as for any key. A read of one that
\*         found it is validated for presence only; one that found nothing
\*         is validated in full.
\*   CODE  Engine::commit_locked                            src/engine/commit/mod.rs
\*         The read loop, then the write loop. A presence-only read does
\*         not stand for a write of its key, so a deleted content-addressed
\*         key is checked by both. A blind merge at DefraLevel aborts only
\*         on a newer replacement. An identical blind write is elided,
\*         except under a merge of its own batch (write_matches_committed;
\*         its operand clause is left out, see Elided).
\*   PLAN  Value-validated reads [3.5]. At DefraLevel a read is current
\*         when the key's newest committed write is a put or a delete that
\*         leaves exactly the value the read returned. A newer operand on
\*         top is a change. Every other level compares sequences.
\*   PLAN  Projected reads, `get_parts` [3.3, 3.4]. Validated only against
\*         newer writes that change one of the named parts: a put, delete
\*         or range delete always does (unless it leaves exactly the bytes
\*         read), an operand does when `touches` says so. In full when the
\*         read found nothing or the transaction puts the key; never with
\*         no part named. Like any read but a presence read, it stands for
\*         a write of its key, which is why the put fallback is needed.
\*   PLAN  Write-free transactions [3.8]. An optimistic DefraLevel
\*         transaction with no put, delete, merge or append validates no
\*         plain read. A pessimistic one validates as at RepeatableRead.
\*   PLAN  Log keys [3.2, 3.6]. A read of a key of the log range is never
\*         validated at DefraLevel. Only `append` writes the log, in the
\*         ordered step: the position is assigned at commit, so the
\*         appending transaction never sees its own entry.
\*   PLAN  Validated scans [3.15]. Any newer write inside the range the scan
\*         covered conflicts, so a key that left the range (a revocation)
\*         and a key that appeared in it (a phantom) both abort the scan.
\*   PLAN  Read-your-own-writes in operation order [3.9]. A transaction's
\*         read applies its own puts, deletes and merges in operation order,
\*         and its commit applies them in the same order. CODE today applies
\*         a put before a merge whatever their order (MUTANT PutsBeforeMerges).
\*   CODE  E11 (#236). A merge made before a scan keeps the scan's stretch:
\*         the scan reads the operands-only key's base without recording it.
\*   PLAN  Conflict reasons [3.14]. An abort carries (key, mine, theirs,
\*         observed_seq, latest_seq): what this transaction did with the key,
\*         and the newer committed write that decided the race.
\*
\* THE HISTORY. `hist` holds every committed write as a record: the commit
\* sequence, the key, the kind (Put, Delete, RangeDelete, Merge, the
\* engine's WriteKind), the value the key held right after it, and for an
\* operand the parts it touches. A commit takes one sequence here where the
\* engine gives each operation its own; a key that one commit both puts and
\* merges gets a Put and a Merge record at that sequence, the Merge being the
\* newer (Newer). Every rule below reads the history the way the engine
\* walks the versions newer than a snapshot, newest first. Each step keeps
\* only what an open snapshot can still read (Prune), as compaction does.
\*
\* LEAN. proofs/lean/Regolith/Validation.lean proves, for every history
\* size, that these per-class rules accept only histories equivalent to the
\* serial one in commit order (all_classes_serial);
\* proofs/lean/Regolith/Relaxations.lean states each class's relaxation
\* exactly; proofs/lean/Regolith/MergeOperator.lean proves the merge-operator
\* laws the blind-merge and projected-read rules rest on. RepeatableRead.tla's
\* header names every theorem.

EXTENDS Naturals, FiniteSets, Sequences, TLC

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
  Extras,    \* the transactions of the later workloads, one set per role (RoleNames);
             \* a config names a record the root module defines, e.g. Extras <- NoExtras
  CommutativeRanges, \* ranges the KeyClassifier declares commutative
  ContentAddressedRanges, \* ranges the KeyClassifier declares content-addressed
  Level,     \* "ReadCommitted" | "SnapshotIsolation" | "RepeatableRead" | "Serializable" | "DefraLevel"
  Mutant     \* "none", or the line a RED config breaks (RepeatableRead.tla, MUTANTS)

\* The roles of the later workloads, each a set of transaction ids.
RoleNames == {"Collectors", "Linkers", "Holders",
              "PartReaders", "PartRewriters", "PartWriters",
              "ValueReaders", "VersionWriters",
              "ReadOnlys", "Promoters", "SkewWriters",
              "LogAppenders", "LogReaders", "LogDeciders",
              "TallyMergers", "OwnWriters",
              "Checkers", "Revokers", "Granters"}
ASSUME Extras \in [RoleNames -> SUBSET Nat]
\* Two roles never share a transaction.
ASSUME \A r1, r2 \in RoleNames : r1 # r2 => Extras[r1] \cap Extras[r2] = {}

\* One name per role, so the rules read as the workloads are described.
Collectors     == Extras["Collectors"]     \* garbage collection of the shared block
Linkers        == Extras["Linkers"]        \* put (or merge) the shared block and pin it
Holders        == Extras["Holders"]        \* read the shared block and record its presence
PartReaders    == Extras["PartReaders"]    \* get_parts(part key, {1}) and decide on part 1
PartRewriters  == Extras["PartRewriters"]  \* get_parts(part key, {1}), then put the whole key
PartWriters    == Extras["PartWriters"]    \* one blind write of the part key, chosen at begin
ValueReaders   == Extras["ValueReaders"]   \* read the version key and decide on its value
VersionWriters == Extras["VersionWriters"] \* rewrite the version key, identically or not
ReadOnlys      == Extras["ReadOnlys"]      \* optimistic, write-free: read both skew keys
Promoters      == Extras["Promoters"]      \* pessimistic, write-free: get_for_update past the snapshot
SkewWriters    == Extras["SkewWriters"]    \* write both skew keys together
LogAppenders   == Extras["LogAppenders"]   \* append one entry to the log
LogReaders     == Extras["LogReaders"]     \* read the log head, append, and store a cursor
LogDeciders    == Extras["LogDeciders"]    \* misuse: decide on a log read
TallyMergers   == Extras["TallyMergers"]   \* merge into a commutative key, then scan its prefix
OwnWriters     == Extras["OwnWriters"]     \* two operations on one key, then read it back
Checkers       == Extras["Checkers"]       \* decide on what a range holds, with a validated scan
Revokers       == Extras["Revokers"]       \* delete a key of that range
Granters       == Extras["Granters"]       \* put a new key into that range

\* Every transaction of the later workloads.
NewTxns == UNION {Extras[r] : r \in RoleNames}
\* The transactions that read the part key with get_parts.
PartTxns == PartReaders \cup PartRewriters

\* Every transaction that writes the counter.
CounterTxns == Incrementers \cup ReadMergers \cup Rebasers \cup Resetters \cup Clearers
\* The DefraLevel workloads of #237.
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
                   "PolicyIgnoresRange",
                   "CaDeleteExempt", "PresenceReadFull", "PresenceUnchecked",
                   "PartsIgnorePut", "PartsIgnoreTouch", "PartsNoAbsentFallback",
                   "PartsNoPutFallback", "PartsNamesOther", "SeqOnlyValidation",
                   "WriteFreePessimistic", "OwnAppendVisible", "MergeBeforeScanReadsBase",
                   "PutsBeforeMerges", "OwnMergesInvisible", "ReasonNewestWrite",
                   "PlainScanDecides"}
ASSUME Remote \in Nat /\ Remote \notin Appenders \cup {Seed}
ASSUME RemoteParents \subseteq Appenders \cup {Seed}
ASSUME ExtraTxns \subseteq Nat
ASSUME ExtraTxns \cap (Appenders \cup {Pruner, Writer, Patcher}) = {}
\* The extra workloads are pairwise disjoint.
ASSUME Cardinality(ExtraTxns) =
         Cardinality(Mergers) + Cardinality(Incrementers) + Cardinality(ReadMergers)
         + Cardinality(Rebasers) + Cardinality(Resetters) + Cardinality(Clearers)
         + Cardinality(Migrators)
\* The later workloads use ids of their own.
ASSUME NewTxns \cap (Appenders \cup {Pruner, Writer, Patcher} \cup ExtraTxns) = {}

\* Every block of the DAG: the seed, one per appender, and the remote one.
Blocks == Appenders \cup {Seed} \cup (IF Mergers = {} THEN {} ELSE {Remote})
\* The transactions of the first workloads (#237), and every transaction.
OldTxns == Appenders \cup {Pruner, Writer, Patcher} \cup ExtraTxns
Txns    == OldTxns \cup NewTxns

----------------------------------------------------------------------------
\* THE KEY LAYOUT. Keys are <<range, p, c>>. Ranges sort by number, and
\* inside a range a key sorts by p, then c: the order a scan walks. A range
\* is also the prefix a KeyClassifier declares.
HeadRange    == 1   \* the DAG's head keys
MarkerRange  == 2   \* markers: a block naming its parent
DefRange     == 3   \* the collection definition
DocRange     == 4   \* the document written from the definition
CounterRange == 5   \* the counter
BlockRange   == 6   \* blocks, keyed by their content
PinRange     == 7   \* a linker's pin on the shared block
HoldRange    == 8   \* a holder's record of the shared block's presence
PartRange    == 9   \* the key read by parts
VersionRange == 10  \* a key rewritten on every save, often with the same bytes
SkewRange    == 11  \* two keys always written together
LogRange     == 12  \* the commit-ordered log: its head and its entries
TallyRange   == 13  \* a key merged into inside a commutative prefix
OwnRange     == 14  \* the key the own-writes workload writes and reads back
AclRange     == 15  \* a range a decision rests on as a whole (grants)
OutRange     == 16  \* each decider's own output key
ASSUME CommutativeRanges \subseteq {HeadRange, MarkerRange, TallyRange}
\* A key has one class.
ASSUME /\ ContentAddressedRanges \subseteq {HeadRange, MarkerRange, DefRange, DocRange,
                                             CounterRange, BlockRange}
       /\ ContentAddressedRanges \cap CommutativeRanges = {}
\* The classifier always declares the log range Log: only append writes it.
LogRanges == {LogRange}

HeadKey(b)      == <<HeadRange, b, b>>      \* block b is a head
MarkerKey(p, c) == <<MarkerRange, p, c>>    \* block c names block p as a parent
DefKey          == <<DefRange, 0, 0>>       \* the definition
DocKey          == <<DocRange, 0, 0>>       \* the document
CounterKey      == <<CounterRange, 0, 0>>   \* the counter
\* A block's content-addressed key: written once, identically by anyone.
BlockKey(b)     == <<BlockRange, b, b>>
\* The block the collector reclaims and linkers and holders refer to: the
\* seed's block, which no other workload writes.
Shared          == BlockKey(Seed)
PinKey(l)       == <<PinRange, l, l>>       \* linker l's pin
HoldKey(h)      == <<HoldRange, h, h>>      \* holder h's record
PartKey         == <<PartRange, 0, 0>>      \* the key read by parts
VersionKey      == <<VersionRange, 0, 0>>   \* the version key
SkewA           == <<SkewRange, 0, 1>>      \* the first skew key
SkewB           == <<SkewRange, 0, 2>>      \* the second skew key
\* The log's head holds the newest assigned position; entry p sorts after it.
LogHead         == <<LogRange, 0, 0>>
LogEntry(p)     == <<LogRange, 1, p>>       \* the entry at position p
TallyKey        == <<TallyRange, 0, 0>>     \* the key tally mergers merge into
OwnKey          == <<OwnRange, 0, 0>>       \* the key own-writers write and read
AclKey(i)       == <<AclRange, i, i>>       \* grant i
OutKey(t)       == <<OutRange, t, t>>       \* decider t's output

\* Positions the log can reach: one append per appending transaction.
LogPositions == 1..Cardinality(LogAppenders \cup LogReaders)
\* The transactions that write a decision into an output key of their own.
OutTxns == PartReaders \cup ValueReaders \cup LogReaders \cup LogDeciders \cup Checkers

\* Every key any workload of this config reads or writes.
Keys == {HeadKey(b) : b \in Blocks}
        \cup {MarkerKey(p, c) : p \in Blocks, c \in Blocks}
        \cup {DefKey, DocKey, CounterKey}
        \cup {BlockKey(b) : b \in Blocks}
        \cup {PinKey(l) : l \in Linkers} \cup {HoldKey(h) : h \in Holders}
        \cup {PartKey, VersionKey, SkewA, SkewB, LogHead, TallyKey, OwnKey,
              AclKey(1), AclKey(2)}
        \cup {LogEntry(p) : p \in LogPositions}
        \cup {OutKey(t) : t \in OutTxns}

\* Key a sorts at or before key b: by range, then p, then c.
KeyLeq(a, b) ==
  \/ a[1] < b[1]
  \/ a[1] = b[1] /\ a[2] < b[2]
  \/ a[1] = b[1] /\ a[2] = b[2] /\ a[3] <= b[3]

\* The first and the last key of a nonempty set, in scan order.
MinKey(S) == CHOOSE k \in S : \A j \in S : KeyLeq(k, j)
MaxKey(S) == CHOOSE k \in S : \A j \in S : KeyLeq(j, k)

\* A value is a natural; 0 is an absent key, and a delete intends 0. The
\* counter's value is its count, so an absent counter counts 0.
Absent == 0

\* The part key's value carries two parts as digits: part 1 is the ones
\* digit, part 2 the tens digit, so 11 is "both parts at 1". A present value
\* is never 0, since every write of the key leaves some part at least 1.
Parts == {1, 2}
\* Part p of value v, and the value whose parts are p1 and p2.
Part(v, p) == IF p = 1 THEN v % 10 ELSE v \div 10
PartValue(p1, p2) == p1 + 10 * p2

\* What every key holds before any commit.
InitStore ==
  [k \in Keys |->
     IF k \in {HeadKey(Seed), DefKey, BlockKey(Seed), VersionKey, SkewA, SkewB, OwnKey,
               AclKey(1)} THEN 1
     ELSE IF k = PartKey THEN PartValue(1, 1)
     ELSE Absent]

\* The kinds of committed write (the engine's WriteKind), and those that
\* replace a key's value outright.
Kinds     == {"Put", "Delete", "RangeDelete", "Merge"}
Replacing == {"Put", "Delete", "RangeDelete"}   \* everything but an operand

\* What a transaction did with a key, as a conflict reason names it (Access).
Accesses == {"Read", "ReadParts", "ReadPresence", "ReadForUpdate", "ScannedThenWrote",
             "ScannedRange", "Put", "Delete", "Merge"}

\* The anomalies and needless refusals the later workloads' invariants watch
\* for; RepeatableRead.tla says what each means.
FlagNames == {"HoldStale", "PartsStale", "PartsRefusedNeedlessly", "ValueStale",
              "IdenticalRewriteRefused", "Skew", "LogDecisionStale", "PhantomAppend",
              "OwnMismatch", "ScanStale", "BadReason"}

VARIABLES
  clock,     \* the engine sequence, advanced by every commit
  store,     \* [Keys -> Nat] what each key holds
  hist,      \* the committed writes, as records (THE HISTORY above)
  phase,     \* [Txns -> {"idle", "open", "committed", "aborted"}]
  snap,      \* [Txns -> Nat] begin snapshot
  tracked,   \* [Txns -> SUBSET Keys] keys recorded as point reads, served at the snapshot
  runs,      \* [Txns -> SUBSET (Keys \X Keys)] stretches scans walked
  written,   \* [Txns -> SUBSET Keys] keys the commit puts or deletes
  merged,    \* [Txns -> SUBSET Keys] keys the commit merges an operand into
  intended,  \* [Txns -> [Keys -> Nat]] what each put or deleted key is set to
  seen,      \* [Txns -> Nat] the value a write was derived from: the definition
             \* the writer or a migrator read, the count a read-merger read
  ops,       \* [Txns -> Seq(STRING)] the operations an own-writer or a part
             \* writer chose, in operation order
  forUpdate, \* [Txns -> SUBSET (Keys \X Nat)] get_for_update reads served past the
             \* snapshot, each with the horizon it was served at
  flags,     \* SUBSET FlagNames: anomalies and needless refusals observed so far
  parents,   \* [Blocks -> SUBSET Blocks] parents each committed block recorded
  stale,     \* TRUE once a write committed over a definition replaced after it was read
  dupRefused,    \* TRUE once a merger was refused over writes identical to its own
  wrongReceipt,  \* TRUE once a read-merger committed over a count that moved
  needlessRefusal, \* TRUE once a blind increment was refused that could have committed
  cbase,     \* ghost: what the last put, delete or range delete stored in the counter
  cepoch,    \* ghost: the sequence it committed at
  cinc       \* ghost: commit sequences of the increments counted on top of it

\* Every variable, so a step that changes none of them is a stutter.
vars == <<clock, store, hist, phase, snap, tracked, runs, written, merged, intended, seen,
          ops, forUpdate, flags, parents, stale, dupRefused, wrongReceipt,
          needlessRefusal, cbase, cepoch, cinc>>

\* The keys that hold a value now.
Stored == {k \in Keys : store[k] # Absent}

----------------------------------------------------------------------------
\* THE HISTORY, read the way the engine walks a key's versions.

\* Record a is newer than record b: a later commit, or, within one commit,
\* the operand above the put it was merged onto. Records of one commit for
\* different keys are ordered by key, so the order is total.
Newer(a, b) ==
  \/ a.seq > b.seq
  \/ a.seq = b.seq /\ a.kind = "Merge" /\ b.kind # "Merge"
  \/ a.seq = b.seq /\ (a.kind = "Merge") = (b.kind = "Merge")
     /\ KeyLeq(b.key, a.key) /\ a.key # b.key

\* The newest record of a nonempty set of records.
Newest(S) == CHOOSE w \in S : \A v \in S : v = w \/ Newer(w, v)

\* The writes of key k committed after sequence s: what a snapshot at s
\* does not see.
After(k, s) == {w \in hist : w.key = k /\ w.seq > s}

\* What key k held at sequence s: the value its newest write at or below s
\* left, or its initial value. A read at snapshot s returns this.
ValueAt(k, s) ==
  LET S == {w \in hist : w.key = k /\ w.seq <= s}
  IN IF S = {} THEN InitStore[k] ELSE Newest(S).val

\* The newest committed entry of key k is an unresolved merge operand.
NewestIsOperand(k) ==
  LET S == {w \in hist : w.key = k} IN S # {} /\ Newest(S).kind = "Merge"

\* The oldest sequence any open transaction can still read at: the oldest
\* open snapshot, or the current sequence when none is open (a transaction
\* that begins later snapshots there). ph and cl are the phases and the
\* sequence after the step.
Horizon(ph, cl) ==
  LET open == {snap[t] : t \in {u \in Txns : ph[u] = "open"}} \cup {cl}
  IN CHOOSE m \in open : \A n \in open : m <= n

\* The history h with what no open snapshot can read folded away, as
\* compaction folds versions per live snapshot: every record newer than the
\* horizon stays, and of the older ones only each key's newest, which
\* ValueAt needs for a read at the horizon or later. Every rule and ghost
\* reads the history at an open transaction's anchors (all at or above the
\* horizon) or its newest entries, so this changes no verdict; it only
\* merges states that differ in history nobody can see.
Prune(h, ph, cl) ==
  LET hz == Horizon(ph, cl)
  IN {r \in h : \/ r.seq > hz
                \/ r = Newest({q \in h : q.key = r.key /\ q.seq <= hz})}

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
\* WHO CONSULTS THE CLASSIFIER.

\* A pessimistic transaction. At DefraLevel it validates exactly as at
\* RepeatableRead and consults no classifier [3.1].
Pessimistic(t) == t \in Promoters

\* The transaction runs under DefraLevel's optimistic rules: key classes,
\* value validation, blind merges, write-free commits.
Classified(t) == Level = "DefraLevel" /\ ~Pessimistic(t)

\* KeyClass::ContentAddressed, applied where the classifier is consulted.
CA(t, k) == Classified(t) /\ k[1] \in ContentAddressedRanges

\* A key the classifier declares Log, applied where it is consulted.
LogKey(t, k) == Classified(t) /\ k[1] \in LogRanges

\* The transaction appends to the log at commit.
Appends(t) == t \in LogAppenders \cup LogReaders

\* PLAN [3.8]: no put, delete, merge or append.
WriteFree(t) == written[t] = {} /\ merged[t] = {} /\ ~Appends(t)

\* PLAN [3.8]: a write-free optimistic DefraLevel transaction validates no
\* plain read; its snapshot is consistent on its own. MUTANT
\* WriteFreePessimistic extends that to a pessimistic one, which the plan
\* rejects.
ValidatesNothing(t) ==
  /\ WriteFree(t)
  /\ \/ Classified(t)
     \/ Pessimistic(t) /\ Mutant = "WriteFreePessimistic"

\* policy::exempt_content_addressed: the content-addressed keys the commit
\* puts or merges, which nothing validates. The newest write decides, so a
\* key put (intended not absent) or merged counts; a key only deleted does
\* not. MUTANT CaDeleteExempt exempts a delete too (the rule before E17).
CaExempt(t) ==
  {k \in written[t] \cup merged[t] :
     /\ CA(t, k)
     /\ \/ k \in merged[t]
        \/ intended[t][k] # Absent
        \/ Mutant = "CaDeleteExempt"}

----------------------------------------------------------------------------
\* THE READS A COMMIT VALIDATES. Each is a record: the key, the anchor (the
\* sequence the read was served at), the access a conflict reason names,
\* the rule that validates it, and the parts it names (all parts unless it
\* is a projected read). The rules:
\*   "seq"       any newer write conflicts (every level but DefraLevel)
\*   "value"     PLAN [3.5]: the newest newer write conflicts unless it is a
\*               put or delete leaving exactly the value read
\*   "presence"  E17: conflicts only when the newest write left the key absent
\*   "parts"     PLAN [3.4]: walk newest first to the first write that
\*               changes a named part; it conflicts unless it is a put
\*               leaving exactly the value read
Rd(k, at, mine, rule, parts) ==
  [key |-> k, at |-> at, mine |-> mine, rule |-> rule, parts |-> parts]

\* How a full read is validated: by value at DefraLevel, by sequence
\* elsewhere. MUTANT SeqOnlyValidation compares sequences at DefraLevel too.
FullRule(t) == IF Classified(t) /\ Mutant # "SeqOnlyValidation" THEN "value" ELSE "seq"

\* The read of key k at anchor at found a value.
Found(k, at) == ValueAt(k, at) # Absent

\* The class rule for one plain read (a point read, a get_for_update, or a
\* written key a scan stretch covers): the read records it keeps, none when
\* the class drops it.
\*   Log key             never validated (PLAN [3.2]).
\*   content-addressed   E17/D7: a read of a key the commit puts or merges is
\*                       dropped; otherwise one that found the key is
\*                       presence-only and one that found nothing is full.
\*     MUTANT PresenceReadFull   a read that found the key is validated in
\*                               full by sequence, as RepeatableRead validates
\*                               any read, even when the commit puts the key.
\*     MUTANT PresenceUnchecked  a read that found the key is never
\*                               validated (the rule before E17).
\*   anything else       full.
Classify(t, k, at, mine) ==
  IF LogKey(t, k) THEN {}
  ELSE IF CA(t, k) /\ Found(k, at)
    THEN CASE Mutant = "PresenceReadFull"  -> {Rd(k, at, mine, "seq", Parts)}
           [] Mutant = "PresenceUnchecked" -> {}
           [] k \in CaExempt(t)            -> {}
           [] OTHER                        -> {Rd(k, at, "ReadPresence", "presence", Parts)}
  ELSE IF CA(t, k) /\ k \in CaExempt(t) THEN {}
  ELSE {Rd(k, at, mine, FullRule(t), Parts)}

\* No get_for_update in the first workloads; the term of validation_set is
\* kept, with an empty set, so the transcription stays complete.
ForUpdate(t) == {}

\* Transaction::validation_set: the recorded point reads the level validates.
ValidatedReads(t) ==
  {k \in tracked[t] :
     IF Level \in {"RepeatableRead", "Serializable", "DefraLevel"} THEN TRUE
     ELSE IF Level = "ReadCommitted" THEN k \in written[t]
     ELSE k \in ForUpdate(t) \/ k \in written[t]}

\* scan_range::cover: every written or merged key inside a stretch a scan
\* walked joins the reads, anchored at the begin snapshot.
\* policy::run_is_commutative: at DefraLevel a stretch whose two ends lie in
\* one declared range is dropped before cover sees it.
Commutative(s) ==
  /\ Level = "DefraLevel"
  /\ IF Mutant = "PolicyIgnoresRange"
       THEN s[1][1] \in CommutativeRanges \/ s[2][1] \in CommutativeRanges
       ELSE s[1][1] \in CommutativeRanges /\ s[2][1] = s[1][1]
\* The stretches of t that cover reads: those the policy did not drop.
CoveredRuns(t) == {s \in runs[t] : ~Commutative(s)}

\* Key k lies inside a stretch of t that covers reads.
Walked(t, k) == \E s \in CoveredRuns(t) : KeyLeq(s[1], k) /\ KeyLeq(k, s[2])

\* The parts a projected read names: part 1, which its decision uses.
\* MUTANT PartsNamesOther: a part reader names part 2 while deciding on
\* part 1, the caller misuse [3.4, Precondition].
NamedParts(t) == IF t \in PartReaders /\ Mutant = "PartsNamesOther" THEN {2} ELSE {1}

\* PLAN [3.4]: the read record of a part reader's or rewriter's get_parts.
\* At another level, or pessimistic, get_parts is a get. At DefraLevel it is
\* validated in full when it found nothing (existence is part of every
\* decision on parts) or when the transaction puts the key (a put replaces
\* every part); never with no part named; otherwise over its parts.
PartRead(t) ==
  LET full == \/ ~Found(PartKey, snap[t]) /\ Mutant # "PartsNoAbsentFallback"
              \/ PartKey \in written[t] /\ Mutant # "PartsNoPutFallback"
  IN IF t \notin PartTxns THEN {}
     ELSE IF ~Classified(t) THEN {Rd(PartKey, snap[t], "Read", FullRule(t), Parts)}
     ELSE IF full THEN {Rd(PartKey, snap[t], "ReadParts", FullRule(t), Parts)}
     ELSE IF NamedParts(t) = {} THEN {}
     ELSE {Rd(PartKey, snap[t], "ReadParts", "parts", NamedParts(t))}

\* Every read the commit validates. A point read and a stretch over the same
\* written key are one read, recorded as the point read.
KeptReads(t) ==
  IF ValidatesNothing(t) THEN {}
  ELSE UNION {Classify(t, k, snap[t], "Read") : k \in ValidatedReads(t)}
       \cup UNION {Classify(t, k, snap[t], "ScannedThenWrote") :
                     k \in {j \in written[t] \cup merged[t] : Walked(t, j)} \ ValidatedReads(t)}
       \cup UNION {Classify(t, f[1], f[2], "ReadForUpdate") : f \in forUpdate[t]}
       \cup PartRead(t)

\* The keys whose read stands for a write of the key (Engine::commit_locked,
\* the write loop): every kept read but a presence-only one.
StandingKeys(t) == {r.key : r \in {q \in KeptReads(t) : q.rule # "presence"}}

\* Engine::commit_locked, the write loop: a merged key takes the blind-merge
\* path only when no read of it stands for the write and the batch neither
\* puts nor deletes it (`Replaced`), its put being validated as a write.
BlindMerged(t) ==
  merged[t] \ ((IF Mutant = "ReadMergeBlind" THEN {} ELSE StandingKeys(t))
               \cup (IF Mutant = "PutMergeBlind" THEN {} ELSE written[t]))

----------------------------------------------------------------------------
\* THE NEWER WRITE THAT DECIDES. Each operator returns the set holding the
\* record that makes a check fail, empty when the check passes.

\* PLAN [3.5]: a put, delete or range delete that leaves exactly the value
\* the read returned is not a change.
Identical(w, r) == w.kind \in Replacing /\ w.val = ValueAt(r.key, r.at)

\* PLAN [3.4]: a newer write changes one of the parts P. MUTANT
\* PartsIgnorePut forgets that a put, delete or range delete always does;
\* MUTANT PartsIgnoreTouch forgets the operands that touch P.
Decisive(w, P) ==
  \/ w.kind \in Replacing /\ Mutant # "PartsIgnorePut"
  \/ w.kind = "Merge" /\ w.touch \cap P # {} /\ Mutant # "PartsIgnoreTouch"

\* The record that fails read r, by its rule.
ReadDecider(r) ==
  LET newer == After(r.key, r.at)
  IN IF newer = {} THEN {}
     ELSE CASE r.rule = "seq" -> {Newest(newer)}
            [] r.rule = "value" ->
                 IF Identical(Newest(newer), r) THEN {} ELSE {Newest(newer)}
            [] r.rule = "presence" ->
                 IF Newest(newer).kind \in {"Delete", "RangeDelete"} THEN {Newest(newer)} ELSE {}
            [] r.rule = "parts" ->
                 LET D == {w \in newer : Decisive(w, r.parts)}
                 IN IF D = {} \/ Identical(Newest(D), r) THEN {} ELSE {Newest(D)}

\* write_matches_committed: the write stores what the key already holds, and
\* the batch merges nothing on top of it. The engine also refuses an elision
\* when the key's newest entry is an unresolved merge operand. That is not
\* modeled. In the first workloads it cannot change an outcome: a counter
\* with an operand on top holds at least one, which a reset's delete never
\* equals, and a rebase's put is already refused elision by the merge its own
\* batch carries; Red_PutMergeElides shows that line only without it. In the
\* later workloads leaving it out only allows more elisions; every GREEN
\* config was also run with it, and stays GREEN.
Elided(t, k) ==
  /\ intended[t][k] = store[k]
  /\ k \notin merged[t] \/ Mutant = "PutMergeElides"

\* The written keys the write loop checks: not exempt, not standing behind
\* a read, not blind-merged.
WriteChecked(t) == written[t] \ (StandingKeys(t) \cup BlindMerged(t) \cup CaExempt(t))

\* The record that fails a blind merge into k. At DefraLevel
\* (IsolationLevel::blind_merges_commute) only a newer replacement does
\* (newest_terminator_seq_above), walking past newer operands; elsewhere any
\* newer write. MUTANT RangeDeleteNotReplacement: a range tombstone is not
\* a replacement here.
MergeDecider(t, k) ==
  LET newer == After(k, snap[t])
      repl  == {w \in newer : /\ w.kind \in Replacing
                              /\ ~(w.kind = "RangeDelete" /\ Mutant = "RangeDeleteNotReplacement")}
  IN IF Classified(t)
       THEN IF Mutant = "MergeIgnoresReplacement" \/ repl = {} THEN {} ELSE {Newest(repl)}
       ELSE IF newer = {} THEN {} ELSE {Newest(newer)}

\* PLAN [3.15]: the records that fail a validated scan: any write newer than
\* the snapshot inside the range it covered. A checker consumes its whole
\* range, so the range covered is all of it. MUTANT PlainScanDecides: the
\* checker decides on a plain scan, which validates no range.
ScanDecider(t) ==
  LET newer == {w \in hist : w.key[1] = AclRange /\ w.seq > snap[t]}
  IN IF t \notin Checkers \/ Mutant = "PlainScanDecides" \/ ValidatesNothing(t) \/ newer = {}
       THEN {} ELSE {Newest(newer)}

----------------------------------------------------------------------------
\* THE COMMIT DECISION. A candidate is one failed check: the key, what this
\* transaction did with it, the anchor it was checked at, the parts it
\* named, and the deciding record.
Cand(k, mine, at, parts, w) == [key |-> k, mine |-> mine, at |-> at, parts |-> parts, w |-> w]

\* Engine::commit_locked, the read loop: every kept read whose key is not
\* blind-merged.
ReadCands(t) ==
  UNION {{Cand(r.key, r.mine, r.at, r.parts, w) : w \in ReadDecider(r)} :
           r \in {q \in KeptReads(t) : q.key \notin BlindMerged(t)}}

\* Engine::commit_locked, the write loop with `writes_at` the begin snapshot.
\* A content-addressed key the classifier exempts is skipped.
WriteCands(t) ==
  {Cand(k, IF intended[t][k] = Absent THEN "Delete" ELSE "Put", snap[t], Parts,
        Newest(After(k, snap[t]))) :
     k \in {j \in WriteChecked(t) : After(j, snap[t]) # {} /\ ~Elided(t, j)}}

\* The same loop for a key the commit only merges into: never elided.
MergeCands(t) ==
  UNION {{Cand(k, "Merge", snap[t], Parts, w) : w \in MergeDecider(t, k)} :
           k \in BlindMerged(t) \ CaExempt(t)}

\* PLAN [3.15]: a failed validated scan names the key that landed in the range.
ScanCands(t) == {Cand(w.key, "ScannedRange", snap[t], Parts, w) : w \in ScanDecider(t)}

\* Every failed check of t's commit.
Candidates(t) == ReadCands(t) \cup WriteCands(t) \cup MergeCands(t) \cup ScanCands(t)

\* The commit aborts when any check failed.
Conflicts(t) == Candidates(t) # {}

\* PLAN [3.14]: the reason an abort carries. The engine reports the first
\* failed check in its loop order; any failed check is a valid reason, so the
\* model picks one. `theirs` and `latest` come from the deciding record.
\* MUTANT ReasonNewestWrite reports the key's newest write instead, which is
\* not the one that decided when newer writes that decide nothing (an
\* operand over a replacement, for a blind merge) sit above it.
\* The reason t's abort carries.
ReasonOf(t) ==
  LET c == CHOOSE c \in Candidates(t) : TRUE
      w == IF Mutant = "ReasonNewestWrite" THEN Newest(After(c.key, c.at)) ELSE c.w
  IN [key |-> c.key, mine |-> c.mine, theirs |-> w.kind, observed |-> c.at,
      latest |-> w.seq, parts |-> c.parts]

----------------------------------------------------------------------------
\* WHAT A COMMIT WRITES.

\* An own-writer's operations folded onto value v in operation order
\* [3.9]: a put stores 5, a delete removes the key, a merge adds one.
RECURSIVE Fold(_, _)
Fold(s, v) ==
  IF s = <<>> THEN v
  ELSE Fold(Tail(s), CASE Head(s) = "put" -> 5 [] Head(s) = "delete" -> Absent
                       [] Head(s) = "merge" -> v + 1)

\* The same operations with every put and delete first and every merge after
\* them: what a 0.1.x commit applies (MUTANT PutsBeforeMerges).
PutsFirst(s) ==
  LET reps == SelectSeq(s, LAMBDA o : o # "merge")
      mrgs == SelectSeq(s, LAMBDA o : o = "merge")
  IN (IF reps = <<>> THEN <<>> ELSE <<reps[Len(reps)]>>) \o mrgs

\* The operations an own-writer's commit applies.
CommitOps(t) == IF Mutant = "PutsBeforeMerges" THEN PutsFirst(ops[t]) ELSE ops[t]

\* The parts a part writer's operand touches; any other operand touches every
\* part (MergeOperator::touches defaults to true).
Touch(t) ==
  IF t \in PartWriters /\ ops[t] = <<"touch1">> THEN {1}
  ELSE IF t \in PartWriters /\ ops[t] = <<"touch2">> THEN {2}
  ELSE Parts

\* One operand of t applied to value v of key k: on the part key, one more
\* on each part it touches; on a content-addressed block, the block's own
\* bytes (an idempotent operand); on anything else, one more.
Operand(t, k, v) ==
  CASE k = PartKey ->
         PartValue(Part(v, 1) + (IF 1 \in Touch(t) THEN 1 ELSE 0),
                   Part(v, 2) + (IF 2 \in Touch(t) THEN 1 ELSE 0))
    [] k[1] = BlockRange -> 1
    [] OTHER -> v + 1

\* A put or delete first, then a merge on top of what it left.
Applied(t, k) ==
  IF t \in OwnWriters /\ k = OwnKey THEN Fold(CommitOps(t), store[k])
  ELSE LET base == IF k \in written[t] THEN intended[t][k] ELSE store[k]
       IN IF k \in merged[t] THEN Operand(t, k, base) ELSE base

\* PLAN [3.6]: the position an append takes, assigned in the ordered step
\* from the head the view holds now, dense from 1.
AppendPos == store[LogHead] + 1
\* The keys an append writes: its entry and the head.
AppendKeys(t) == IF Appends(t) THEN {LogEntry(AppendPos), LogHead} ELSE {}
\* An entry holds its appender's id; the head holds the newest position.
AppendValue(t, k) == IF k = LogHead THEN AppendPos ELSE t

\* What key k holds after t commits.
NewValue(t, k) ==
  IF k \in AppendKeys(t) THEN AppendValue(t, k)
  ELSE IF k \in written[t] \cup merged[t] THEN Applied(t, k)
  ELSE store[k]

\* The records a commit at sequence n adds to the history: a Put or Delete
\* per written key, a Merge per merged key (newer than a put of the same
\* key), and the append's two puts.
Records(t, n) ==
  {[seq |-> n, key |-> k, kind |-> IF intended[t][k] = Absent THEN "Delete" ELSE "Put",
    val |-> intended[t][k], touch |-> Parts] : k \in written[t]}
  \cup {[seq |-> n, key |-> k, kind |-> "Merge", val |-> Applied(t, k), touch |-> Touch(t)] :
          k \in merged[t]}
  \cup {[seq |-> n, key |-> k, kind |-> "Put", val |-> AppendValue(t, k), touch |-> Parts] :
          k \in AppendKeys(t)}

====
