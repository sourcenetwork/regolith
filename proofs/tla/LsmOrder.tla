---- MODULE LsmOrder ----
\* E1: `compact_range` at L0 must pick a closed input set.
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/LsmOrder.lean:
\*   read_newest                    the read order returns the newest visible
\*                                  version, on ordered sources
\*   put_ordered, flush_ordered     a write and a flush keep the sources ordered
\*   compact_range_reads_newest     compacting the closure keeps them ordered
\*                                  and changes no read
\*   pickL0_closed, pickL0_covers   the closure picker returns a closed set
\*                                  holding every file that meets the range
\*   intersect_only_breaks_reads    the RED case, as a counterexample
\* TLC checks the same invariant here over every interleaving of puts,
\* flushes and range compactions, for a few keys and versions.
\*
\* THE ENGINE, as it reads and compacts.
\*   RegolithEngine::lookup_in_view   src/engine/mod.rs
\*     A point read walks the active memtable, then the L0 files newest
\*     first, then the deeper levels. The first source holding a version of
\*     the key at or below the snapshot answers, with its newest such version.
\*   run_compact_range                src/engine/compaction.rs
\*     At L0 the inputs are the files that intersect [start, end]. They and
\*     the L1 files their key range overlaps are merged into L1.
\*
\* THE DEFECT (Picker = "Intersect"). Picking only the files that intersect
\* the range can move a newer version of a key into L1 while an older
\* version of the same key stays behind in an older, unpicked L0 file. Every
\* read consults L0 before L1, so the read of that key travels backwards.
\*
\* THE FIX (Picker = "Closure"). Start from the files that intersect the
\* range. Add every L0 file older than a picked file whose key range overlaps
\* the picked set's key range. Repeat until nothing changes.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - compact_range flushes the memtable before it picks; here a flush may
\*     happen at any moment, that one included.
\*   - L1 is one sorted run, so it is one set of versions: merging the
\*     picked files with the L1 files they overlap is a union, and which L1
\*     files were rewritten is invisible to a read.
\*   - A compaction may drop a version no registered snapshot can see. The
\*     reads checked here are at every snapshot, so every version is kept.
\*   - Levels below L1 sit after L1 in read order and are not touched by an
\*     L0 compaction.
\*
\* CONFIGURATIONS.
\*   MC_LsmOrder_Green          Picker = "Closure"    ReadNewest holds.
\*   MC_LsmOrder_Red_Intersect  Picker = "Intersect"  ReadNewest fails.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Keys,    \* the user keys: a finite set of naturals, ordered as keys are
  MaxSeq,  \* the last sequence a put may take, which bounds the writes
  MaxL0,   \* the most L0 files the model lets accumulate
  Picker   \* "Closure" (the fix) or "Intersect" (the defect)

ASSUME Keys \subseteq Nat /\ Keys # {}
ASSUME MaxSeq \in Nat /\ MaxL0 \in Nat
ASSUME Picker \in {"Closure", "Intersect"}

VARIABLES
  seq,  \* the last sequence handed out; 0 before the first write
  mem,  \* the active memtable: a set of versions <<key, sequence>>
  l0,   \* the L0 files, newest first: a sequence of sets of versions
  l1    \* the L1 run: one set of versions

\* Every variable, so a step that changes none of them is a stutter.
vars == <<seq, mem, l0, l1>>

----------------------------------------------------------------------------
\* Helpers.

\* The greatest element of a finite, nonempty set of naturals.
Max(S) == CHOOSE m \in S : \A n \in S : n <= m
\* The least element of a finite, nonempty set of naturals.
Min(S) == CHOOSE m \in S : \A n \in S : m <= n

\* The sequences of the versions of key k in a set of versions F that a
\* snapshot at `snap` may see: those at or below it.
Visible(F, k, snap) == {v[2] : v \in {x \in F : x[1] = k /\ x[2] <= snap}}

\* The keys a file holds. Its key range runs from the least to the greatest.
KeysOf(F) == {v[1] : v \in F}

----------------------------------------------------------------------------
\* Reads.

\* The sources in read order: the memtable, the L0 files newest first, L1.
Sources == <<mem>> \o l0 \o <<l1>>

\* RegolithEngine::lookup_in_view: the first source in read order holding a
\* version of k the snapshot may see answers, with its newest one. 0 means
\* the key reads as absent (sequences start at 1).
Read(k, snap) ==
  LET hits == {i \in 1..Len(Sources) : Visible(Sources[i], k, snap) # {}}
  IN IF hits = {} THEN 0 ELSE Max(Visible(Sources[Min(hits)], k, snap))

\* Every version the tree holds, whichever source holds it.
AllVersions == mem \cup l1 \cup UNION {l0[i] : i \in 1..Len(l0)}

\* What a correct read returns: the newest version of k anywhere that the
\* snapshot may see, or 0 when there is none.
Newest(k, snap) ==
  IF Visible(AllVersions, k, snap) = {} THEN 0 ELSE Max(Visible(AllVersions, k, snap))

----------------------------------------------------------------------------
\* Picking the L0 inputs of compact_range(lo, hi). A picked set is a set of
\* positions in l0; a larger position is an older file.

\* The file holds a key inside [lo, hi].
Intersects(F, lo, hi) == \E k \in KeysOf(F) : lo <= k /\ k <= hi

\* The keys of the files at positions P. The picked set's key range runs
\* from the least to the greatest of them.
Hull(P) == UNION {KeysOf(l0[i]) : i \in P}

\* The file's key range meets the range the keys H span: the interval test
\* min(F) <= max(H) /\ min(H) <= max(F). An empty side meets nothing.
Overlaps(F, H) ==
  /\ KeysOf(F) # {}
  /\ H # {}
  /\ Min(KeysOf(F)) <= Max(H)
  /\ Min(H) <= Max(KeysOf(F))

\* run_compact_range at L0 today: every file that intersects the range.
Initial(lo, hi) == {i \in 1..Len(l0) : Intersects(l0[i], lo, hi)}

\* One closure step: add every file older than some picked file (a later
\* position) whose key range meets the picked set's key range.
Grow(P) ==
  P \cup {j \in 1..Len(l0) : (\E i \in P : i < j) /\ Overlaps(l0[j], Hull(P))}

\* Grow to the fixpoint. Each step that changes P adds a file, so it ends
\* within Len(l0) steps.
RECURSIVE Close(_)
Close(P) == IF Grow(P) = P THEN P ELSE Close(Grow(P))

\* The input set the configured picker chooses.
Pick(lo, hi) == IF Picker = "Closure" THEN Close(Initial(lo, hi)) ELSE Initial(lo, hi)

\* The L0 files at position i and after that P does not pick, in L0 order.
RECURSIVE Unpicked(_, _)
Unpicked(P, i) ==
  IF i > Len(l0) THEN <<>>
  ELSE (IF i \in P THEN <<>> ELSE <<l0[i]>>) \o Unpicked(P, i + 1)

----------------------------------------------------------------------------
\* Actions.

\* The start: no write yet, an empty memtable, no L0 file, an empty L1.
Init ==
  /\ seq = 0
  /\ mem = {}
  /\ l0  = <<>>
  /\ l1  = {}

\* A put of key k: the next sequence, inserted into the memtable.
Put(k) ==
  /\ seq < MaxSeq
  /\ seq' = seq + 1
  /\ mem' = mem \cup {<<k, seq + 1>>}
  /\ UNCHANGED <<l0, l1>>

\* A flush: the memtable becomes the newest L0 file, and a new, empty
\* memtable takes the writes.
Flush ==
  /\ mem # {}
  /\ Len(l0) < MaxL0
  /\ l0'  = <<mem>> \o l0
  /\ mem' = {}
  /\ UNCHANGED <<seq, l1>>

\* compact_range(lo, hi) at L0: the picked files leave L0, and their
\* versions join L1 (merged with the L1 files they overlap).
CompactRange(lo, hi) ==
  LET P == Pick(lo, hi)
  IN /\ P # {}
     /\ l0' = Unpicked(P, 1)
     /\ l1' = l1 \cup UNION {l0[i] : i \in P}
     /\ UNCHANGED <<seq, mem>>

\* Every step the system can take.
Next ==
  \/ \E k \in Keys : Put(k)
  \/ Flush
  \/ \E lo, hi \in Keys : lo <= hi /\ CompactRange(lo, hi)

\* Every behaviour: start in Init, then take Next steps or stutter.
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ seq \in 0..MaxSeq
  /\ mem \subseteq Keys \X (1..MaxSeq)
  /\ Len(l0) <= MaxL0
  /\ \A i \in 1..Len(l0) : l0[i] \subseteq Keys \X (1..MaxSeq)
  /\ l1 \subseteq Keys \X (1..MaxSeq)

\* THE HEADLINE. Every read, of every key, at every snapshot up to the
\* newest sequence, returns the newest version of that key the snapshot may
\* see. Lean: read_newest with compact_range_reads_newest.
ReadNewest == \A k \in Keys : \A snap \in 0..seq : Read(k, snap) = Newest(k, snap)

====
