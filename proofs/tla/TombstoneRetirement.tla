---- MODULE TombstoneRetirement ----
\* E27: when compaction may drop a range tombstone. Dropped column families
\* leave range tombstones, and a tombstone a pass carries forever makes every
\* later pass over its range pay for it.
\*
\* THE ENGINE.
\*   Retirement::carried_tombstones     src/engine/compaction/retire.rs
\*     The range tombstones a pass writes out: all of its inputs' tombstones
\*     but those it retires. One retires when the pass writes the deepest
\*     level holding a key of its range and no live snapshot is below its
\*     sequence. Never at L0.
\*   Retirement::retire_deletion        src/engine/compaction/retire.rs
\*     The same rule for a point deletion, which is a range tombstone over
\*     its one key here, and which the engine retires only as the oldest
\*     entry of its key with no merge operand on it.
\*   Stripes::shadowed                  src/engine/compaction/stripes.rs
\*     The pass drops every entry a tombstone of its inputs covers in the
\*     entry's own snapshot stripe, retired tombstones included.
\*
\* THE DEFECTS, one per mutant value of Retire.
\*   "IgnoreSnapshots": retire at the bottom whatever the snapshots. A
\*     snapshot below the tombstone keeps a covered version alive in an older
\*     stripe; with the tombstone gone a snapshot above it reads that version
\*     back.
\*   "IgnoreDeeper": retire with the snapshots clear but a deeper run still
\*     holding a covered version. A snapshot above the tombstone reads it
\*     back.
\*
\* THE FIX. Retire a tombstone only when no deeper run meets its range and
\* every live snapshot is at or above its sequence. Every version it covers
\* is then in the pass's inputs, in its stripe, and dropped with it.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - The read order across sources: a read merges every entry of the key by
\*     sequence, which is what the engine's read order returns on an ordered
\*     tree (LsmOrder.tla, Lean read_newest). A version older than a
\*     tombstone is never above it in that order: both enter at the top and
\*     a pass merges adjacent runs.
\*   - Point deletions and merge operands, and dropping a put under a newer
\*     put: StripeCompaction.tla checks those reductions. Here a pass drops
\*     only what a tombstone covers, which is all a retirement relies on.
\*   - L0, whose tables overlap: a pass writing L0 retires nothing.
\*   - Several concurrent passes and the capture window (E5): the passes'
\*     inputs are disjoint, and the engine reads the live list once the
\*     inputs are fixed (StripeCompaction.tla); here a pass is one step.
\*   - A run is one table: the engine tests each deeper table's range, the
\*     model each deeper run's span, which is the same test on one table.
\*
\* CONFIGURATIONS.
\*   MC_TombstoneRetirement_Green                 the fix: reads kept
\*   MC_TombstoneRetirement_Green_Retires         the fix retires: the
\*                                                witness NothingRetired fails
\*   MC_TombstoneRetirement_Red_IgnoreSnapshots   SnapshotReadsKept fails
\*   MC_TombstoneRetirement_Red_IgnoreDeeper      SnapshotReadsKept fails

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  Keys,     \* the user keys, naturals
  MaxSeq,   \* the last sequence a write may take: bounds the writes
  MaxRuns,  \* the most runs (levels) the model lets exist
  Readers,  \* reader ids; each registers one snapshot at most once
  Retire    \* "Fix", "IgnoreSnapshots" or "IgnoreDeeper"

ASSUME Keys \subseteq Nat /\ Keys # {}
ASSUME MaxSeq \in Nat /\ MaxRuns \in Nat \ {0}
ASSUME Retire \in {"Fix", "IgnoreSnapshots", "IgnoreDeeper"}

\* What a read of a key with no visible put returns. Puts read as their
\* sequence, so every value is at least 1.
Absent == 0

\* A sequence above every sequence a write takes: the head reads at it.
Infinity == MaxSeq + 1

\* A put of key k at sequence s: <<"put", k, k, s>>. A range tombstone over
\* the keys lo..hi at sequence s: <<"rt", lo, hi, s>>. The second and third
\* fields are the keys the entry holds or covers.
Put(k, s) == <<"put", k, k, s>>
Rt(lo, hi, s) == <<"rt", lo, hi, s>>

\* The fields of an entry e.
Kind(e) == e[1]
Lo(e) == e[2]
Hi(e) == e[3]
SeqOf(e) == e[4]

VARIABLES
  seq,      \* the last sequence handed out; 0 before the first write
  mem,      \* the memtable: a set of entries
  runs,     \* the runs, NEWEST FIRST: a pass merges runs i and i + 1 into
            \* the deeper position; runs after i + 1 are deeper still
  hist,     \* every entry ever written, never compacted: the ground truth
  live,     \* [Readers -> BOOLEAN] whether the reader holds its snapshot
  used,     \* the readers that have registered
  snap,     \* [Readers -> Nat] the sequence the reader's snapshot reads at
  seen,     \* [Readers -> [Keys -> Nat]] what each snapshot read when taken
  retired   \* how many tombstones passes have retired

\* Every variable, so a step that changes none of them is a stutter.
vars == <<seq, mem, runs, hist, live, used, snap, seen, retired>>

\* The greatest element of a finite, nonempty set of naturals.
Max(S) == CHOOSE m \in S : \A n \in S : n <= m
\* The least element of a finite, nonempty set of naturals.
Min(S) == CHOOSE m \in S : \A n \in S : m <= n

\* Every entry the tree holds: the memtable and every run.
Tree == mem \cup UNION {runs[i] : i \in 1..Len(runs)}

\* A read of key k at snapshot s over the entries E: the newest put of k at
\* or below s, unless a tombstone at or below s covering k is newer than it.
ReadIn(E, k, s) ==
  LET puts == {SeqOf(e) : e \in {x \in E : Kind(x) = "put" /\ Lo(x) = k /\ SeqOf(x) <= s}}
      rts  == {SeqOf(e) : e \in {x \in E : Kind(x) = "rt" /\ Lo(x) <= k /\ k <= Hi(x) /\ SeqOf(x) <= s}}
  IN IF puts = {} THEN Absent
     ELSE LET p == Max(puts) IN IF \E t \in rts : t > p THEN Absent ELSE p

\* The sequences of the live snapshots.
LiveSeqs == {snap[r] : r \in {x \in Readers : live[x]}}

\* The upper bound of the stripe sequence s falls in: the smallest live
\* snapshot at or above it, or Infinity for the top stripe.
Top(s) == LET above == {l \in LiveSeqs : l >= s} IN IF above = {} THEN Infinity ELSE Min(above)

\* Stripes::shadowed: entry e of the window W is a put that a tombstone of W
\* covers in e's own stripe.
Shadowed(W, e) ==
  /\ Kind(e) = "put"
  /\ \E t \in W : Kind(t) = "rt" /\ Lo(t) <= Lo(e) /\ Lo(e) <= Hi(t)
                  /\ SeqOf(e) < SeqOf(t) /\ SeqOf(t) <= Top(SeqOf(e))

\* The keys of run R span from its least to its greatest key, the range a
\* table records; that span meets lo..hi.
RunMeets(R, lo, hi) ==
  /\ R # {}
  /\ Min({Lo(e) : e \in R}) <= hi
  /\ lo <= Max({Hi(e) : e \in R})

\* A pass writing position i + 1 retires tombstone t: in the fix, no run
\* deeper than i + 1 meets t's range and no live snapshot is below t.
\* Each mutant drops one conjunct.
Retires(i, t) ==
  LET clearBelow == \A j \in (i + 2)..Len(runs) : ~RunMeets(runs[j], Lo(t), Hi(t))
      clearSnaps == \A l \in LiveSeqs : SeqOf(t) <= l
  IN CASE Retire = "Fix"             -> clearBelow /\ clearSnaps
       [] Retire = "IgnoreSnapshots" -> clearBelow
       [] OTHER                      -> clearSnaps

\* The elements of T at positions 1.. not in S, in order.
RECURSIVE Keep(_, _, _)
Keep(T, S, i) ==
  IF i > Len(T) THEN <<>> ELSE (IF i \in S THEN <<>> ELSE <<T[i]>>) \o Keep(T, S, i + 1)

----------------------------------------------------------------------------
\* Actions.

\* The start: no write, empty memtable and runs, no snapshot.
Init ==
  /\ seq     = 0
  /\ mem     = {}
  /\ runs    = <<>>
  /\ hist    = {}
  /\ live    = [r \in Readers |-> FALSE]
  /\ used    = {}
  /\ snap    = [r \in Readers |-> 0]
  /\ seen    = [r \in Readers |-> [k \in Keys |-> Absent]]
  /\ retired = 0

\* A put of key k at the next sequence.
DoPut(k) ==
  /\ seq < MaxSeq
  /\ seq' = seq + 1
  /\ mem' = mem \cup {Put(k, seq + 1)}
  /\ hist' = hist \cup {Put(k, seq + 1)}
  /\ UNCHANGED <<runs, live, used, snap, seen, retired>>

\* A range delete of the keys lo..hi at the next sequence: what
\* drop_column_family writes over its family's keys.
DoRangeDelete(lo, hi) ==
  /\ seq < MaxSeq
  /\ lo <= hi
  /\ seq' = seq + 1
  /\ mem' = mem \cup {Rt(lo, hi, seq + 1)}
  /\ hist' = hist \cup {Rt(lo, hi, seq + 1)}
  /\ UNCHANGED <<runs, live, used, snap, seen, retired>>

\* A flush turns the memtable into the newest run.
Flush ==
  /\ mem # {}
  /\ Len(runs) < MaxRuns
  /\ runs' = <<mem>> \o runs
  /\ mem'  = {}
  /\ UNCHANGED <<seq, hist, live, used, snap, seen, retired>>

\* A pass merges run i into run i + 1: it drops what a tombstone of its
\* window shadows and writes out every tombstone it does not retire. An
\* output with nothing left in it is no run at all.
Compact(i) ==
  /\ i + 1 <= Len(runs)
  /\ LET W    == runs[i] \cup runs[i + 1]
         gone == {t \in W : Kind(t) = "rt" /\ Retires(i, t)}
         out  == {e \in W : ~Shadowed(W, e)} \ gone
     IN /\ runs'    = Keep([runs EXCEPT ![i + 1] = out],
                           IF out = {} THEN {i, i + 1} ELSE {i}, 1)
        /\ retired' = retired + Cardinality(gone)
  /\ UNCHANGED <<seq, mem, hist, live, used, snap, seen>>

\* Reader r registers a snapshot at the newest sequence and records what it
\* reads for every key.
TakeSnapshot(r) ==
  /\ r \notin used
  /\ used' = used \cup {r}
  /\ live' = [live EXCEPT ![r] = TRUE]
  /\ snap' = [snap EXCEPT ![r] = seq]
  /\ seen' = [seen EXCEPT ![r] = [k \in Keys |-> ReadIn(Tree, k, seq)]]
  /\ UNCHANGED <<seq, mem, runs, hist, retired>>

\* Reader r releases its snapshot.
Release(r) ==
  /\ live[r]
  /\ live' = [live EXCEPT ![r] = FALSE]
  /\ UNCHANGED <<seq, mem, runs, hist, used, snap, seen, retired>>

\* Every step the system can take.
Next ==
  \/ \E k \in Keys : DoPut(k)
  \/ \E lo, hi \in Keys : DoRangeDelete(lo, hi)
  \/ Flush
  \/ \E i \in 1..MaxRuns : Compact(i)
  \/ \E r \in Readers : TakeSnapshot(r) \/ Release(r)

\* Every behaviour: start in Init, then take Next steps or stutter.
Spec == Init /\ [][Next]_vars

\* Readers are interchangeable.
ReaderSymmetry == Permutations(Readers)

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ seq \in 0..MaxSeq
  /\ Len(runs) <= MaxRuns
  /\ live \in [Readers -> BOOLEAN]
  /\ used \subseteq Readers
  /\ snap \in [Readers -> 0..MaxSeq]
  /\ retired \in Nat

\* THE HEADLINE. Every live snapshot reads every key as it did when taken.
SnapshotReadsKept ==
  \A r \in Readers : live[r] => \A k \in Keys : ReadIn(Tree, k, snap[r]) = seen[r][k]

\* A read at the head returns what the whole history says.
HeadKept == \A k \in Keys : ReadIn(Tree, k, Infinity) = ReadIn(hist, k, Infinity)

\* The witness: nothing was ever retired. The fix must break it, or it
\* retires nothing and keeps the reads by never trying.
NothingRetired == retired = 0

====
