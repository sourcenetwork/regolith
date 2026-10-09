---- MODULE StripeCompaction ----
\* 4.8: compaction under live snapshots. Every key's versions are reduced
\* per snapshot stripe, merge operands are folded only by an exact
\* `partial_merge`, the compaction filter runs on every stripe, and the
\* live-snapshot list is read only after the inputs are fixed (E5).
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/Stripes.lean:
\*   combine_reads              one fold of two neighbours of one stripe
\*                              changes no read at a stripe boundary
\*   reduce_reads               the whole reduction changes no read at a
\*                              live snapshot or at the head, on top of any
\*                              base the older versions resolve to
\*   window_reads_kept          so a compaction of any window of a key's
\*                              versions, newer ones above and older below,
\*                              changes no such read
\*   reduce_keeps_newest        the newest version's sequence is kept
\*   inexact_fold_breaks_reads  the RED Inexact case, as a counterexample
\*   unlisted_snapshot_breaks_reads
\*                              the RED CaptureEarly and IgnoreStripes cases:
\*                              a snapshot missing from the list loses the
\*                              version it reads
\* TLC checks the same laws here over every interleaving of writes,
\* flushes, snapshot registrations and releases, and one compaction at a
\* time whose steps interleave with all of them.
\*
\* THE ENGINE.
\*   Stripes::reduce_group, reduce_stripe, fold
\*                                  src/engine/compaction/stripes.rs
\*     The live snapshots cut the sequence line into stripes. An entry at
\*     sequence s belongs to the stripe bounded by the smallest live
\*     snapshot at or above s, or to the top stripe. Inside a stripe only
\*     the newest state is visible to any reader, so the entries beneath
\*     its terminator (the newest value or deletion) are dropped, the
\*     operands over the terminator fold into it with `full_merge`, and an
\*     operand-only stripe folds with `partial_merge` when the operator has
\*     an exact one. The filter judges the value that ends each stripe.
\*   SnapshotRegistry::live_seqs     src/engine/snapshot_registry.rs
\*     The list the stripes are cut at. SnapshotRegistry.tla shows the
\*     lock-free registry returns every live snapshot or one at or above
\*     the horizon sampled before the scan.
\*
\* THE DEFECTS.
\*   Capture = "BeforeInputs" (E5): the list is read before the inputs are
\*     fixed. A snapshot registered in between is missing from the list,
\*     yet the inputs hold versions newer than it (a flush landed in the
\*     window), so its version is dropped beneath a newer one.
\*   FoldOperandOnly = "Always" with Operator = "Inexact": an operand-only
\*     stripe is folded with a `partial_merge` that does not agree with
\*     applying the operands one at a time (a floating-point sum), so the
\*     value read through it changes.
\*   Stripes = "Ignore": the reduction treats the whole key as one stripe,
\*     as if no snapshot were live.
\*
\* THE FIX. Fix the inputs, then read the list. A snapshot registered after
\* that reads at the visible sequence, which is at or above every version
\* in the inputs, so it reads each key's top stripe, whose newest state is
\* always kept. Fold an operand-only stripe only with an exact
\* `partial_merge`; with an inexact operator such a stripe stays operands
\* until a base lands in the same stripe.
\*
\* FILTERS. A filter that changes or removes a value changes what a live
\* snapshot reads, by design (plan 3.1: expiry applies under snapshots). So
\* the expected reads move with the filter's decisions: when a compaction
\* installs, each live reader's expected value becomes what it reads in the
\* tree just before the install with the filter applied in place to every
\* stripe's terminator in the inputs. The invariant then says the
\* reduction itself (drops and folds) changes nothing beyond that. With
\* Filter = "None" the expectations never move, and the invariant is the
\* plain "every live snapshot reads the same value before and after".
\*
\* DESIGN CHOICES where the plan leaves room (recorded in the report):
\*   - A compaction's inputs are any window of consecutive runs. In an LSM
\*     ordered as LsmOrder.tla proves, the inputs of any compaction hold a
\*     consecutive stretch of each key's versions: newer ones may sit above
\*     the window (memtable, newer runs) and older ones below it, so both a
\*     stripe cut at the window's top and an operand-only stripe whose base
\*     lies below the window occur.
\*   - The filter runs on each stripe's terminator before the operands
\*     over it fold, as Stripes::reduce_stripe does.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - The read order across memtable and runs: a read merges every entry
\*     of the key by sequence, which is what the engine's read order returns
\*     on an ordered tree (LsmOrder.tla, Lean read_newest).
\*   - Range tombstones (`Stripes::shadowed`): they act as deletions with a
\*     sequence and follow the same stripe rule. When a pass may drop the
\*     tombstone itself (E27) is TombstoneRetirement.tla.
\*   - Several concurrent compactions: their windows are disjoint and each
\*     reads the list after fixing its own inputs, so each is the case here.
\*   - The configurations use one key: the reduction treats each key on its
\*     own (StripeSets splits by key), so a second key only multiplies the
\*     states. Each reader registers once; a later registration is another
\*     reader.
\*
\* CONFIGURATIONS.
\*   MC_StripeCompaction_Green                Exact operator, no filter
\*   MC_StripeCompaction_Green_Filter         Exact operator, Expire filter
\*   MC_StripeCompaction_Green_Inexact        Inexact operator, never folds
\*                                            an operand-only stripe
\*   MC_StripeCompaction_Red_CaptureEarly     SnapshotReadsKept fails (E5)
\*   MC_StripeCompaction_Red_InexactFold      HeadKept fails
\*   MC_StripeCompaction_Red_IgnoreStripes    SnapshotReadsKept fails

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
  Keys,             \* the user keys, naturals
  MaxSeq,           \* the last sequence a write may take: bounds the writes
  MaxRuns,          \* the most runs (sorted files) the model lets exist
  Readers,          \* reader ids, model values; each holds at most one
                    \* snapshot, and the readers are interchangeable
  PutValues,        \* the values a put may write, naturals
  Cap,              \* the largest value a merge result may reach
  Operator,         \* "Exact" or "Inexact": whether partial_merge is exact
  FoldOperandOnly,  \* "IfExact" (the fix) or "Always" (the defect)
  Capture,          \* "AfterInputs" (the fix) or "BeforeInputs" (E5)
  Stripes,          \* "PerSnapshot" (the fix) or "Ignore" (the defect)
  Filter            \* "None" or "Expire" (removes 0, lowers Cap to Cap - 1)

ASSUME Keys \subseteq Nat /\ Keys # {}
ASSUME MaxSeq \in Nat /\ MaxRuns \in Nat \ {0} /\ Cap \in Nat \ {0}
ASSUME PutValues \subseteq 0..Cap
ASSUME Operator \in {"Exact", "Inexact"}
ASSUME FoldOperandOnly \in {"IfExact", "Always"}
ASSUME Capture \in {"AfterInputs", "BeforeInputs"}
ASSUME Stripes \in {"PerSnapshot", "Ignore"}
ASSUME Filter \in {"None", "Expire"}

\* What a read of a key with no visible state returns. Values are >= 0.
Absent == -1

\* A sequence above every sequence a write takes: the top stripe's bound,
\* and the snapshot the head reads at.
Infinity == MaxSeq + 1

VARIABLES
  seq,       \* the last sequence handed out; 0 before the first write
  mem,       \* the memtable: a set of entries <<key, seq, kind, value>>
  runs,      \* the runs, OLDEST FIRST, each a set of entries; a flush
             \* appends, so a compaction window's positions stay valid
  live,      \* [Readers -> BOOLEAN] whether the reader holds a snapshot
  used,      \* the readers that have registered; each registers once, which
             \* bounds the model and loses nothing: a later registration is
             \* another reader
  snap,      \* [Readers -> Nat] the sequence the reader's snapshot reads at
  seen,      \* [Readers -> [Keys -> Int]] what each live snapshot must read
  headSeen,  \* [Keys -> Int] what a read at the head must return
  last,      \* [Keys -> Nat] the sequence of each key's newest write, 0 none
  cphase,    \* the compaction: "idle", "fixed", "sampled" or "ready"
  win,       \* <<lo, hi>>: the positions of the input runs, once fixed
  list       \* the live-snapshot list the compaction read, once read

\* Every variable, so a step that changes none of them is a stutter.
vars == <<seq, mem, runs, live, used, snap, seen, headSeen, last, cphase, win, list>>

----------------------------------------------------------------------------
\* Helpers.

\* The smaller of two integers.
Min2(a, b) == IF a <= b THEN a ELSE b

\* The least element of a finite, nonempty set of integers.
Min(S) == CHOOSE m \in S : \A n \in S : m <= n

\* The greatest element of a finite, nonempty set of integers.
Max(S) == CHOOSE m \in S : \A n \in S : n <= m

\* The entry with the greatest sequence in a nonempty set of entries.
\* Sequences are unique per entry, so it is well defined.
Newest(S) == CHOOSE e \in S : \A f \in S : f[2] <= e[2]

\* The entry with the least sequence in a nonempty set of entries.
Oldest(S) == CHOOSE e \in S : \A f \in S : e[2] <= f[2]

\* Every entry the tree holds: the memtable and every run.
Tree == mem \cup UNION {runs[i] : i \in 1..Len(runs)}

----------------------------------------------------------------------------
\* The merge operator. A merge operand is a natural added to the value
\* beneath it; a missing base counts as 0.

\* full_merge one operand at a time: apply operand x to `base`. The exact
\* operator is a saturating sum. The inexact one rounds after every
\* addition, as a floating-point sum does: adding 1 to an even total rounds
\* it back down, so small increments applied one at a time are lost.
Apply(base, x) ==
  LET b == IF base = Absent THEN 0 ELSE base
  IN IF Operator = "Exact" THEN Min2(b + x, Cap) ELSE Min2(2 * ((b + x) \div 2), Cap)

\* partial_merge of two operands, older x then newer y: their sum. For the
\* exact operator, applying it equals applying x then y, for every base.
\* For the inexact one it does not: Apply(0, 1) twice is 0, Apply(0, 2) is 2.
PM(x, y) == Min2(x + y, Cap)

\* full_merge of a set of operands onto `acc`, oldest first.
RECURSIVE FoldOps(_, _)
FoldOps(acc, S) ==
  IF S = {} THEN acc ELSE LET e == Oldest(S) IN FoldOps(Apply(acc, e[4]), S \ {e})

\* partial_merge folded over a set of operands, oldest first, onto `acc`.
RECURSIVE PMRest(_, _)
PMRest(acc, S) ==
  IF S = {} THEN acc ELSE LET e == Oldest(S) IN PMRest(PM(acc, e[4]), S \ {e})

\* One operand standing for a nonempty set of operands: partial_merge
\* folded from the oldest.
PMFold(S) == LET o == Oldest(S) IN PMRest(o[4], S \ {o})

----------------------------------------------------------------------------
\* Reads. All sets of entries below hold the entries of one key.

\* The terminators: values and deletions.
Terms(S) == {e \in S : e[3] # "merge"}

\* The operands over the newest terminator, or every operand when there is
\* no terminator. These are what a read applies.
Leading(S) ==
  IF Terms(S) = {} THEN {e \in S : e[3] = "merge"}
  ELSE {e \in S : e[3] = "merge" /\ e[2] > Newest(Terms(S))[2]}

\* What the operands build on: the newest terminator's value, or Absent
\* when it is a deletion or there is none.
Base(S) ==
  IF Terms(S) = {} THEN Absent
  ELSE LET t == Newest(Terms(S)) IN IF t[3] = "put" THEN t[4] ELSE Absent

\* What a read returns from the entries it sees: Absent when it sees none,
\* the newest terminator's value when nothing is merged over it, otherwise
\* the operands applied oldest first onto that base.
Resolve(S) ==
  IF S = {} THEN Absent
  ELSE IF Leading(S) = {} THEN Base(S)
  ELSE FoldOps(Base(S), Leading(S))

\* A read of key k at snapshot s over the set of entries T.
Read(T, k, s) == Resolve({e \in T : e[1] = k /\ e[2] <= s})

\* The sequences the live snapshots read at.
LiveSeqs == {snap[r] : r \in {x \in Readers : live[x]}}

\* Renaming the readers changes nothing the invariants look at, so TLC
\* checks one state of each set of states that differ only by a renaming.
ReaderSymmetry == Permutations(Readers)

----------------------------------------------------------------------------
\* The reduction.

\* The bound of the stripe sequence s falls in, under the list L: the
\* smallest listed snapshot at or above s, or Infinity for the top stripe.
\* Stripes = "Ignore" puts every entry in the top stripe.
Top(L, s) ==
  IF Stripes = "Ignore" \/ ~(\E l \in L : l >= s) THEN Infinity
  ELSE Min({l \in L : l >= s})

\* The filter's decision on a value: Expire removes the value 0 (as a
\* time-to-live filter removes an expired value) ...
FilterRemoves(v) == Filter = "Expire" /\ v = 0

\* ... and changes the value Cap to Cap - 1; every other value is kept.
FilterChange(v) == IF Filter = "Expire" /\ v = Cap THEN Cap - 1 ELSE v

\* Stripes::filter_value on one entry: a removed value becomes a deletion
\* at the same sequence, so an older version cannot resurface; deletions
\* and operands are not judged.
FilterEntry(e) ==
  IF e[3] # "put" THEN e
  ELSE IF FilterRemoves(e[4]) THEN <<e[1], e[2], "del", 0>>
  ELSE <<e[1], e[2], "put", FilterChange(e[4])>>

\* The stripes of the inputs I under the list L: for each key and each
\* stripe bound, the entries of that key in that stripe.
StripeSets(I, L) ==
  {{e \in I : e[1] = k /\ Top(L, e[2]) = t} :
     k \in Keys, t \in {Top(L, f[2]) : f \in I}} \ {{}}

\* Stripes::reduce_stripe on one stripe G of one key: keep its newest
\* state. With a terminator: filter it, drop what is beneath it, and fold
\* the operands over it into one value at the stripe's newest sequence.
\* Without one: fold the operands into one operand at the newest sequence,
\* only through an exact partial_merge (or always, in the defect).
ReduceStripe(G) ==
  LET ops == Leading(G)
      ts  == Terms(G)
      k   == Newest(G)[1]
      top == Newest(G)[2]
  IN IF ts # {} THEN
       LET t == FilterEntry(Newest(ts))
       IN IF ops = {} THEN {t}
          ELSE {<<k, top, "put", FoldOps(IF t[3] = "put" THEN t[4] ELSE Absent, ops)>>}
     ELSE IF Cardinality(ops) > 1 /\ (Operator = "Exact" \/ FoldOperandOnly = "Always")
       THEN {<<k, top, "merge", PMFold(ops)>>}
     ELSE ops

\* The run a compaction writes: every stripe of the inputs reduced.
Reduce(I, L) == UNION {ReduceStripe(G) : G \in StripeSets(I, L)}

\* The inputs with only the filter applied, in place, to every stripe's
\* terminator: what the filter decided, without any drop or fold. The
\* expected reads after an install are the reads of this.
FilterInPlace(I, L) ==
  UNION {IF Terms(G) = {} THEN G
         ELSE (G \ {Newest(Terms(G))}) \cup {FilterEntry(Newest(Terms(G)))} :
           G \in StripeSets(I, L)}

----------------------------------------------------------------------------
\* Actions.

\* The start: no write, no run, no snapshot, no compaction.
Init ==
  /\ seq      = 0
  /\ mem      = {}
  /\ runs     = <<>>
  /\ live     = [r \in Readers |-> FALSE]
  /\ used     = {}
  /\ snap     = [r \in Readers |-> 0]
  /\ seen     = [r \in Readers |-> [k \in Keys |-> Absent]]
  /\ headSeen = [k \in Keys |-> Absent]
  /\ last     = [k \in Keys |-> 0]
  /\ cphase   = "idle"
  /\ win      = <<0, 0>>
  /\ list     = {}

\* A write of key k: an entry of the given kind and value at the next
\* sequence, into the memtable. The head now reads what this write made it.
Write(k, kind, v) ==
  /\ seq < MaxSeq
  /\ seq'      = seq + 1
  /\ mem'      = mem \cup {<<k, seq + 1, kind, v>>}
  /\ last'     = [last EXCEPT ![k] = seq + 1]
  /\ headSeen' = [j \in Keys |-> Read(Tree \cup {<<k, seq + 1, kind, v>>}, j, Infinity)]
  /\ UNCHANGED <<runs, live, used, snap, seen, cphase, win, list>>

\* A flush: the memtable becomes the newest run.
Flush ==
  /\ mem # {}
  /\ Len(runs) < MaxRuns
  /\ runs' = Append(runs, mem)
  /\ mem'  = {}
  /\ UNCHANGED <<seq, live, used, snap, seen, headSeen, last, cphase, win, list>>

\* Reader r registers a snapshot at the visible sequence, and records what
\* it reads for every key at that moment.
Register(r) ==
  /\ r \notin used
  /\ live' = [live EXCEPT ![r] = TRUE]
  /\ used' = used \cup {r}
  /\ snap' = [snap EXCEPT ![r] = seq]
  /\ seen' = [seen EXCEPT ![r] = [k \in Keys |-> Read(Tree, k, seq)]]
  /\ UNCHANGED <<seq, mem, runs, headSeen, last, cphase, win, list>>

\* Reader r releases its snapshot. What it held is reset, so states that
\* differ only in a released reader's past are one state.
Release(r) ==
  /\ live[r]
  /\ live' = [live EXCEPT ![r] = FALSE]
  /\ snap' = [snap EXCEPT ![r] = 0]
  /\ seen' = [seen EXCEPT ![r] = [k \in Keys |-> Absent]]
  /\ UNCHANGED <<seq, mem, runs, used, headSeen, last, cphase, win, list>>

\* The compaction fixes its inputs: the runs at positions lo..hi. The fix
\* does this first; the defect does it after it read the list.
FixInputs(lo, hi) ==
  /\ \/ Capture = "AfterInputs" /\ cphase = "idle"
     \/ Capture = "BeforeInputs" /\ cphase = "sampled"
  /\ 1 <= lo /\ lo <= hi /\ hi <= Len(runs)
  /\ win'    = <<lo, hi>>
  /\ cphase' = IF Capture = "AfterInputs" THEN "fixed" ELSE "ready"
  /\ UNCHANGED <<seq, mem, runs, live, used, snap, seen, headSeen, last, list>>

\* The compaction reads the live-snapshot list. The fix does this after it
\* fixed its inputs; the defect does it first.
SampleLive ==
  /\ \/ Capture = "AfterInputs" /\ cphase = "fixed"
     \/ Capture = "BeforeInputs" /\ cphase = "idle"
  /\ list'   = LiveSeqs
  /\ cphase' = IF Capture = "AfterInputs" THEN "ready" ELSE "sampled"
  /\ UNCHANGED <<seq, mem, runs, live, used, snap, seen, headSeen, last, win>>

\* The compaction installs: the input runs are replaced, in place, by one
\* run holding their reduction. Every live reader's and the head's
\* expected read becomes what it reads in the tree just before, with the
\* filter's decisions applied in place (no change when Filter = "None").
Install ==
  /\ cphase = "ready"
  /\ LET lo       == win[1]
         hi       == win[2]
         inputs   == UNION {runs[i] : i \in lo..hi}
         others   == mem \cup UNION {runs[i] : i \in (1..Len(runs)) \ (lo..hi)}
         filtered == others \cup FilterInPlace(inputs, list)
     IN /\ runs' = SubSeq(runs, 1, lo - 1) \o <<Reduce(inputs, list)>>
                     \o SubSeq(runs, hi + 1, Len(runs))
        /\ seen' = IF Filter = "None" THEN seen
                   ELSE [r \in Readers |->
                           IF live[r] THEN [k \in Keys |-> Read(filtered, k, snap[r])]
                           ELSE seen[r]]
        /\ headSeen' = IF Filter = "None" THEN headSeen
                       ELSE [k \in Keys |-> Read(filtered, k, Infinity)]
  /\ cphase' = "idle"
  /\ win'    = <<0, 0>>
  /\ list'   = {}
  /\ UNCHANGED <<seq, mem, live, used, snap, last>>

\* Every step the system can take.
Next ==
  \/ \E k \in Keys :
       \/ \E v \in PutValues : Write(k, "put", v)
       \/ Write(k, "merge", 1)
       \/ Write(k, "del", 0)
  \/ Flush
  \/ \E r \in Readers : Register(r) \/ Release(r)
  \/ \E lo, hi \in 1..MaxRuns : FixInputs(lo, hi)
  \/ SampleLive
  \/ Install

\* Every behaviour: start in Init, then take Next steps or stutter.
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ seq \in 0..MaxSeq
  /\ Len(runs) <= MaxRuns
  /\ live \in [Readers -> BOOLEAN]
  /\ snap \in [Readers -> 0..MaxSeq]
  /\ last \in [Keys -> 0..MaxSeq]
  /\ cphase \in {"idle", "fixed", "sampled", "ready"}
  /\ list \subseteq 0..MaxSeq

\* THE HEADLINE. Every live snapshot reads every key the same at every step
\* after it registered, flushes and compactions included; with a filter,
\* up to the values the filter changed or removed. Lean: reduce_reads.
SnapshotReadsKept ==
  \A r \in Readers : live[r] => \A k \in Keys : Read(Tree, k, snap[r]) = seen[r][k]

\* A read at the head returns what the writes made it, through every
\* flush and compaction; with a filter, up to its decisions. Lean:
\* reduce_reads, at a snapshot above every sequence.
HeadKept == \A k \in Keys : Read(Tree, k, Infinity) = headSeen[k]

\* The newest version of every key keeps its sequence, so commit
\* validation sees the same newest write. Lean: reduce_keeps_newest.
NewestKept ==
  \A k \in Keys :
    LET ss == {e[2] : e \in {f \in Tree : f[1] = k}}
    IN (IF ss = {} THEN 0 ELSE Max(ss)) = last[k]

====
