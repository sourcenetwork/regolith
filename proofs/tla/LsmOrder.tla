---- MODULE LsmOrder ----
\* The LSM read order. A point read returns the newest version visible at
\* its snapshot through every write, freeze and flush, L0 install,
\* `compact_range` (E1), level compaction, external ingest, and the
\* demotion of an overlapping level at open (E14, D13), with every level
\* below L0 searched by binary search on its tables' key ranges.
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/LsmOrder.lean:
\*   read_newest                    the read order returns the newest visible
\*                                  version, on ordered sources
\*   put_ordered, flush_ordered     a write and a flush keep the sources ordered
\*   install_oldest_same_order      installing the oldest frozen memtable in
\*                                  L0 leaves the read order as it was
\*   install_newer_breaks_reads     installing a newer one first, the RED
\*                                  FlushAnyOrder case, as a counterexample
\*   compact_range_reads_newest     compacting the closure keeps the sources
\*                                  ordered and changes no read
\*   pickL0_closed, pickL0_covers   the closure picker returns a closed set
\*                                  holding every file that meets the range
\*   intersect_only_breaks_reads    the RED Intersect case, as a counterexample
\*   ingest_ordered                 a file of the newest sequence placed below
\*                                  every source that holds none of its keys
\*                                  keeps the sources ordered
\*   ingest_below_holder_breaks_reads
\*                                  the RED IngestIgnoresUpper case
\*   demote_reads_newest            demoting the overlapping level and every
\*                                  level above it to L0, in age order, keeps
\*                                  the read order and every read
\*   noShared_level_ordered         the overlapping level's tables share no
\*                                  key, so any order of them is ordered
\*   demote_level_only_breaks_reads the RED DemoteLevelOnly case
\*   bsearch_eq_scan, level_read_bsearch
\*                                  binary search over a sorted level whose
\*                                  tables do not overlap finds the table a
\*                                  linear scan finds
\* TLC checks the same invariants here over every interleaving of those
\* steps, for a few keys and versions.
\*
\* THE ENGINE, as it reads and compacts.
\*   RegolithEngine::lookup_in_view   src/engine/mod.rs
\*     A point read walks the memtables, then the L0 files newest first,
\*     then each deeper level, where a binary search on key ranges picks
\*     the one table that may hold the key. The first source holding a
\*     version of the key at or below the snapshot answers, with its newest
\*     such version.
\*   run_compact_range                src/engine/compaction.rs
\*     At L0 the inputs are the files that intersect [start, end]. They and
\*     the L1 tables their key range overlaps are merged into L1.
\*   RegolithEngine::install          src/engine/ingest.rs
\*     An external file takes a fresh sequence and is placed at a level
\*     (`placement`), after the memtables holding a key of its range are
\*     flushed (`flush_memtables_holding`).
\*   manifest replay                  src/engine/manifest.rs
\*     Today refuses a deeper level whose tables overlap (E14).
\*   rotate_if_full, seal_active      src/engine/mod.rs (Freeze here)
\*     A writer whose commit group fills the active memtable seals it under
\*     the pipeline mutex: it becomes the newest frozen memtable and a fresh
\*     one takes the writes. The flush is not done there (E9). A rotation
\*     that would leave more than max_write_buffer_number memtables first
\*     writes the oldest frozen one out itself: that is the bound MaxImm.
\*   Flusher::flush_oldest            src/engine/flush.rs (FlushInstall)
\*     Whoever flushes (the compaction worker, the bounded step a write owes
\*     with no worker, a rotation at the cap, an explicit flush) takes the
\*     `flushing` exclusion, picks the OLDEST frozen memtable, writes its
\*     table, installs it as the newest L0 file and retires the memtable,
\*     all inside that one hold, so a flush is one step here.
\*
\* THE DEFECTS, one per mutant constant.
\*   Picker = "Intersect" (E1). Picking only the L0 files that intersect the
\*     range can move a newer version of a key into L1 while an older one
\*     stays in an older, unpicked L0 file, which every read consults first.
\*   FlushOrder = "Any". With several frozen memtables, a newer one's file
\*     is installed in L0 before an older one is flushed. The older frozen
\*     memtable is read before L0, so its older version answers first. This
\*     is what flushes off the commit path would do without the `flushing`
\*     exclusion: two threads flushing at once, the newer memtable's flush
\*     finishing first.
\*   Ingest = "IgnoreUpper". The file is placed at the deepest level whose
\*     own tables it does not overlap, without checking L0 and the levels
\*     above, which may hold older versions of its keys and are read first.
\*   Legacy = "DemoteLevelOnly". At open, only the overlapping level moves
\*     to L0, in front of the levels above it, which hold newer versions.
\*   Legacy = "Keep". The overlapping level stays, and binary search over
\*     ranges that overlap lands on a table that does not hold the key.
\*
\* THE FIXES.
\*   Picker = "Closure": add every older L0 file whose key range overlaps
\*     the picked set's, until nothing changes.
\*   FlushOrder = "Oldest": a flush installs in memtable order; a file
\*     written early waits for the older ones. The code gets this from the
\*     `flushing` exclusion and from always taking the oldest frozen
\*     memtable, whichever thread flushes.
\*   Ingest = "Placed": the deepest level L such that no L0 file holds a key
\*     in the file's range and no table of levels 1..L overlaps it; L0 when
\*     there is none. A memtable holding a key in the range is flushed
\*     first (D48), so the action requires none does.
\*   Legacy = "Demote": at open, if levels overlap, take the deepest such
\*     level d and move every table of levels 1..d to the end of L0: level
\*     by level, each level's tables newest first by sequence.
\*
\* DESIGN CHOICE where the plan leaves room (recorded in the report). Plan
\* 4.3 says the overlapping level's tables move to L0. Moved alone they sit
\* in front of levels 1..d-1, which hold newer versions of the same keys,
\* so for d >= 2 reads go backwards (RED DemoteLevelOnly). The reading that
\* keeps reads correct moves levels 1..d together. Those levels are smaller
\* than level d by the level multiplier, so this adds about a tenth to a
\* one-time move. For d = 1 the two readings coincide.
\*
\* HOW AN OVERLAPPING LEVEL ARISES (E14). 0.1.x ingested a file carrying a
\* range tombstone at a level chosen by its point keys but recorded its key
\* range widened by the tombstone. LegacyIngest models that: before Open,
\* a file of one key is placed by its point key and recorded with a wider
\* range. Range tombstones themselves are left out: the overlap they cause
\* in recorded ranges is what breaks the binary search.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - compact_range flushes the memtable before it picks; here a flush may
\*     happen at any moment, that one included.
\*   - A compaction writes one output table; splitting it into several
\*     tables with disjoint ranges changes no read.
\*   - A compaction may drop a version no registered snapshot can see
\*     (StripeCompaction.tla). The reads checked here are at every snapshot,
\*     so every version is kept.
\*
\* CONFIGURATIONS.
\*   MC_LsmOrder_Green                       E1 closure, L1 as tables
\*   MC_LsmOrder_Red_Intersect               ReadNewest fails
\*   MC_LsmOrder_Green_Flush                 frozen memtables, in order
\*   MC_LsmOrder_Red_FlushAnyOrder           ReadNewest fails
\*   MC_LsmOrder_Green_Ingest                two levels, ingest placement
\*   MC_LsmOrder_Red_IngestIgnoresUpper      ReadNewest fails
\*   MC_LsmOrder_Green_Demote                legacy overlap, demoted at open
\*   MC_LsmOrder_Red_DemoteLevelOnly         ReadNewest fails
\*   MC_LsmOrder_Red_NoDemotion              ReadNewest fails

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Keys,        \* the user keys: a finite set of naturals, ordered as keys are
  MaxSeq,      \* the last sequence a write may take, which bounds the writes
  MaxL0,       \* the most L0 files a flush or ingest lets accumulate
  Picker,      \* "Closure" (the fix) or "Intersect" (E1)
  MaxImm,      \* the most frozen memtables; 0 flushes the memtable directly
  FlushOrder,  \* "Oldest" (the fix) or "Any" (the defect)
  Levels,      \* how many levels lie below L0
  Ingest,      \* "Off", "Placed" (the fix) or "IgnoreUpper" (the defect)
  Legacy       \* "Off", "Demote" (the fix), "DemoteLevelOnly" or "Keep"

ASSUME Keys \subseteq Nat /\ Keys # {}
ASSUME MaxSeq \in Nat /\ MaxL0 \in Nat /\ MaxImm \in Nat /\ Levels \in Nat \ {0}
ASSUME Picker \in {"Closure", "Intersect"}
ASSUME FlushOrder \in {"Oldest", "Any"}
ASSUME Ingest \in {"Off", "Placed", "IgnoreUpper"}
ASSUME Legacy \in {"Off", "Demote", "DemoteLevelOnly", "Keep"}

VARIABLES
  seq,     \* the last sequence handed out; 0 before the first write
  mem,     \* the active memtable: a set of versions <<key, sequence>>
  imm,     \* the frozen memtables, newest first: a sequence of sets
  l0,      \* the L0 files, newest first: a sequence of sets of versions
  lv,      \* lv[j], j in 1..Levels: level j's tables in key order, each a
           \* record [v |-> versions, lo |-> least key, hi |-> greatest key]
           \* where [lo, hi] is the range the manifest records
  opened   \* whether the open that demotes overlap has run; FALSE only
           \* while a legacy (0.1.x) database is being built

\* Every variable, so a step that changes none of them is a stutter.
vars == <<seq, mem, imm, l0, lv, opened>>

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

\* The closed ranges [a, b] and [c, d] share a key.
RangesMeet(a, b, c, d) == a <= d /\ c <= b

\* The elements of T at positions 1.. not in S, in order.
RECURSIVE Keep(_, _, _)
Keep(T, S, i) ==
  IF i > Len(T) THEN <<>> ELSE (IF i \in S THEN <<>> ELSE <<T[i]>>) \o Keep(T, S, i + 1)

\* Table t inserted into the key-ordered tables T: after every table whose
\* range starts lower, or starts at the same key and ends lower.
Insert(T, t) ==
  LET i == Cardinality({x \in 1..Len(T) : T[x].lo < t.lo \/ (T[x].lo = t.lo /\ T[x].hi < t.hi)})
  IN SubSeq(T, 1, i) \o <<t>> \o SubSeq(T, i + 1, Len(T))

\* The newest sequence a set of versions holds: its age.
AgeOf(F) == Max({v[2] : v \in F})

\* Tables newest first by their newest sequence.
RECURSIVE AgeOrder(_)
AgeOrder(T) ==
  IF T = <<>> THEN <<>>
  ELSE LET i == CHOOSE x \in 1..Len(T) : \A y \in 1..Len(T) : AgeOf(T[y].v) <= AgeOf(T[x].v)
       IN <<T[i]>> \o AgeOrder(Keep(T, {i}, 1))

\* The version sets of a sequence of tables, as L0 files.
Files(T) == [i \in 1..Len(T) |-> T[i].v]

----------------------------------------------------------------------------
\* Reads.

\* Binary search on level tables T for key k: the least position i in a..b
\* with i = b or T[i].hi >= k, halving [a, b) each step. On tables sorted
\* by range and not overlapping, that is the one table whose range may
\* hold k. Lean: bsearch_eq_scan.
RECURSIVE Bisect(_, _, _, _)
Bisect(T, k, a, b) ==
  IF a >= b THEN a
  ELSE LET mid == (a + b) \div 2
       IN IF T[mid].hi < k THEN Bisect(T, k, mid + 1, b) ELSE Bisect(T, k, a, mid)

\* The source level j offers a read of k: the versions of the table the
\* binary search lands on, when its range holds k; else nothing.
Candidate(j, k) ==
  LET T == lv[j]
      i == Bisect(T, k, 1, Len(T) + 1)
  IN IF i <= Len(T) /\ T[i].lo <= k THEN T[i].v ELSE {}

\* What a linear scan of level j offers: every table whose range holds k.
ScanCandidate(j, k) == UNION {lv[j][i].v : i \in {x \in 1..Len(lv[j]) : lv[j][x].lo <= k /\ k <= lv[j][x].hi}}

\* The sources a read of k consults in order: the memtable, the frozen
\* memtables newest first, the L0 files newest first, then one table per
\* level.
Sources(k) == <<mem>> \o imm \o l0 \o [j \in 1..Levels |-> Candidate(j, k)]

\* RegolithEngine::lookup_in_view over the sources S of key k: the first
\* source in read order holding a version of k the snapshot may see
\* answers, with its newest one. 0 means the key reads as absent
\* (sequences start at 1).
ReadIn(S, k, snap) ==
  LET hits == {i \in 1..Len(S) : Visible(S[i], k, snap) # {}}
  IN IF hits = {} THEN 0 ELSE Max(Visible(S[Min(hits)], k, snap))

\* A point read of k at snapshot snap.
Read(k, snap) == ReadIn(Sources(k), k, snap)

\* Every version the tree holds, whichever source holds it.
AllVersions ==
  mem \cup UNION {imm[i] : i \in 1..Len(imm)} \cup UNION {l0[i] : i \in 1..Len(l0)}
      \cup UNION {UNION {lv[j][t].v : t \in 1..Len(lv[j])} : j \in 1..Levels}

\* What a correct read returns over the versions A: the newest version of k
\* that the snapshot may see, or 0 when there is none.
NewestIn(A, k, snap) == IF Visible(A, k, snap) = {} THEN 0 ELSE Max(Visible(A, k, snap))

\* The newest visible version of k anywhere in the tree.
Newest(k, snap) == NewestIn(AllVersions, k, snap)

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

----------------------------------------------------------------------------
\* Placement of an ingested file of key range [a, b].

\* Some memtable, active or frozen, holds a key in [a, b].
MemHolds(a, b) == \E v \in mem \cup UNION {imm[i] : i \in 1..Len(imm)} : a <= v[1] /\ v[1] <= b

\* Some L0 file holds a key in [a, b].
L0Holds(a, b) == \E i \in 1..Len(l0) : \E v \in l0[i] : a <= v[1] /\ v[1] <= b

\* Some table of level j records a range that meets [a, b].
LevelMeets(j, a, b) == \E t \in 1..Len(lv[j]) : RangesMeet(lv[j][t].lo, lv[j][t].hi, a, b)

\* The file may go to level j. The fix: nothing read before level j holds a
\* key in its range, and no table of level j meets it. The defect checks
\* only level j itself.
Fits(j, a, b) ==
  IF Ingest = "IgnoreUpper" THEN ~LevelMeets(j, a, b)
  ELSE ~L0Holds(a, b) /\ \A i \in 1..j : ~LevelMeets(i, a, b)

----------------------------------------------------------------------------
\* Demotion at open.

\* The levels whose recorded ranges overlap: two tables share a key range.
OverlapLevels ==
  {j \in 1..Levels :
     \E t, u \in 1..Len(lv[j]) :
       t # u /\ RangesMeet(lv[j][t].lo, lv[j][t].hi, lv[j][u].lo, lv[j][u].hi)}

\* The tables of the levels in D, in level order, each level's tables
\* newest first: the files they become in L0, in read order.
RECURSIVE Demoted(_, _)
Demoted(D, j) ==
  IF j > Levels THEN <<>>
  ELSE (IF j \in D THEN Files(AgeOrder(lv[j])) ELSE <<>>) \o Demoted(D, j + 1)

\* The levels the configured open demotes. The fix: every level from L1
\* down to the deepest overlapping one. The defect: the overlapping ones.
DemotedLevels ==
  CASE OverlapLevels = {} \/ Legacy = "Keep" -> {}
    [] Legacy = "Demote"                     -> 1..Max(OverlapLevels)
    [] OTHER                                 -> OverlapLevels

----------------------------------------------------------------------------
\* Actions.

\* The start: no write yet, empty memtables, L0 and levels. A legacy
\* configuration starts before the open.
Init ==
  /\ seq    = 0
  /\ mem    = {}
  /\ imm    = <<>>
  /\ l0     = <<>>
  /\ lv     = [j \in 1..Levels |-> <<>>]
  /\ opened = (Legacy = "Off")

\* A put of key k: the next sequence, inserted into the memtable.
Put(k) ==
  /\ seq < MaxSeq
  /\ seq' = seq + 1
  /\ mem' = mem \cup {<<k, seq + 1>>}
  /\ UNCHANGED <<imm, l0, lv, opened>>

\* With no frozen memtables (MaxImm = 0), a flush turns the memtable into
\* the newest L0 file, and a new, empty memtable takes the writes.
Flush ==
  /\ MaxImm = 0
  /\ mem # {}
  /\ Len(l0) < MaxL0
  /\ l0'  = <<mem>> \o l0
  /\ mem' = {}
  /\ UNCHANGED <<seq, imm, lv, opened>>

\* Rotation freezes the memtable (seal_active, under the pipeline mutex): it
\* becomes the newest frozen memtable, still read before L0, and a new,
\* empty memtable takes the writes. Nothing is flushed here (E9).
Freeze ==
  /\ MaxImm > 0                  \* this configuration keeps frozen memtables
  /\ mem # {}                    \* there is something to freeze
  /\ Len(imm) < MaxImm           \* under the cap: at the cap the rotation flushes the oldest first
  /\ imm' = <<mem>> \o imm        \* the memtable joins the front: the newest frozen one
  /\ mem' = {}                   \* writes go to a fresh, empty memtable
  /\ UNCHANGED <<seq, l0, lv, opened>>   \* no sequence, file or level changes

\* A flush of frozen memtable i (Flusher::flush_oldest, by whatever thread)
\* installs its file as the newest L0 file and drops the memtable. The fix
\* installs only the oldest (the last in `imm`); the defect installs
\* whichever flush finished first.
FlushInstall(i) ==
  /\ i \in 1..Len(imm)                  \* a frozen memtable
  /\ FlushOrder = "Any" \/ i = Len(imm)  \* the oldest one, unless the bug is planted
  /\ Len(l0) < MaxL0                    \* keeps the model small
  /\ l0'  = <<imm[i]>> \o l0             \* its file is the newest L0 file
  /\ imm' = Keep(imm, {i}, 1)            \* and it is no longer frozen
  /\ UNCHANGED <<seq, mem, lv, opened>>  \* nothing else changes

\* compact_range(lo, hi) at L0: the picked files leave L0 and merge with
\* the L1 tables their key range meets into one L1 table.
CompactRange(lo, hi) ==
  LET P   == Pick(lo, hi)
      V   == UNION {l0[i] : i \in P}
      L1  == lv[1]
      ins == {t \in 1..Len(L1) : RangesMeet(L1[t].lo, L1[t].hi, Min(KeysOf(V)), Max(KeysOf(V)))}
      out == [v  |-> V \cup UNION {L1[t].v : t \in ins},
              lo |-> Min({Min(KeysOf(V))} \cup {L1[t].lo : t \in ins}),
              hi |-> Max({Max(KeysOf(V))} \cup {L1[t].hi : t \in ins})]
  IN /\ P # {}
     /\ l0' = Keep(l0, P, 1)
     /\ lv' = [lv EXCEPT ![1] = Insert(Keep(L1, ins, 1), out)]
     /\ UNCHANGED <<seq, mem, imm, opened>>

\* A level compaction: table t of level j merges with the tables of level
\* j + 1 its range meets into one table of level j + 1.
CompactLevel(j, t) ==
  /\ j < Levels
  /\ t \in 1..Len(lv[j])
  /\ LET T   == lv[j][t]
         N   == lv[j + 1]
         ins == {u \in 1..Len(N) : RangesMeet(N[u].lo, N[u].hi, T.lo, T.hi)}
         out == [v  |-> T.v \cup UNION {N[u].v : u \in ins},
                 lo |-> Min({T.lo} \cup {N[u].lo : u \in ins}),
                 hi |-> Max({T.hi} \cup {N[u].hi : u \in ins})]
     IN lv' = [lv EXCEPT ![j] = Keep(lv[j], {t}, 1), ![j + 1] = Insert(Keep(N, ins, 1), out)]
  /\ UNCHANGED <<seq, mem, imm, l0, opened>>

\* An ingest of a file holding the keys ks, all at the next sequence. A
\* memtable holding a key in its range is flushed first (D48), so here none
\* may. The file goes to the deepest level it fits, else to the L0 front.
IngestFile(ks) ==
  /\ Ingest # "Off"
  /\ opened
  /\ seq < MaxSeq
  /\ LET a    == Min(ks)
         b    == Max(ks)
         F    == [v |-> {<<k, seq + 1>> : k \in ks}, lo |-> a, hi |-> b]
         fits == {j \in 1..Levels : Fits(j, a, b)}
     IN /\ ~MemHolds(a, b)
        /\ IF fits = {}
             THEN /\ Len(l0) < MaxL0
                  /\ l0' = <<F.v>> \o l0
                  /\ UNCHANGED lv
             ELSE /\ lv' = [lv EXCEPT ![Max(fits)] = Insert(@, F)]
                  /\ UNCHANGED l0
  /\ seq' = seq + 1
  /\ UNCHANGED <<mem, imm, opened>>

\* A 0.1.x ingest (E14): a file holding key k at the next sequence, placed
\* at level j by its point key, which nothing read before level j holds and
\* no table of level j meets, but recorded with the wider range [a, b].
LegacyIngest(j, k, a, b) ==
  /\ ~opened
  /\ seq < MaxSeq
  /\ a <= k /\ k <= b
  /\ ~MemHolds(k, k) /\ ~L0Holds(k, k)
  /\ \A i \in 1..j : ~LevelMeets(i, k, k)
  /\ lv'  = [lv EXCEPT ![j] = Insert(@, [v |-> {<<k, seq + 1>>}, lo |-> a, hi |-> b])]
  /\ seq' = seq + 1
  /\ UNCHANGED <<mem, imm, l0, opened>>

\* The first open by this version: the configured demotion moves levels to
\* the end of L0, as one version edit.
Open ==
  /\ ~opened
  /\ opened' = TRUE
  /\ l0'     = l0 \o Demoted(DemotedLevels, 1)
  /\ lv'     = [j \in 1..Levels |-> IF j \in DemotedLevels THEN <<>> ELSE lv[j]]
  /\ UNCHANGED <<seq, mem, imm>>

\* Every step the system can take.
Next ==
  \/ \E k \in Keys : Put(k)
  \/ Flush
  \/ Freeze
  \/ \E i \in 1..MaxImm : FlushInstall(i)
  \/ \E lo, hi \in Keys : lo <= hi /\ CompactRange(lo, hi)
  \/ \E j \in 1..Levels : \E t \in 1..Len(lv[j]) : CompactLevel(j, t)
  \/ \E ks \in (SUBSET Keys) \ {{}} : IngestFile(ks)
  \/ Legacy # "Off" /\ \E j \in 1..Levels, k, a, b \in Keys : LegacyIngest(j, k, a, b)
  \/ Open

\* Every behaviour: start in Init, then take Next steps or stutter.
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ seq \in 0..MaxSeq
  /\ mem \subseteq Keys \X (1..MaxSeq)
  /\ Len(imm) <= MaxImm
  /\ \A i \in 1..Len(imm) : imm[i] \subseteq Keys \X (1..MaxSeq)
  /\ \A i \in 1..Len(l0) : l0[i] \subseteq Keys \X (1..MaxSeq)
  /\ Len(lv) = Levels
  /\ \A j \in 1..Levels : \A t \in 1..Len(lv[j]) :
       /\ lv[j][t].v \subseteq Keys \X (1..MaxSeq)
       /\ \A x \in lv[j][t].v : lv[j][t].lo <= x[1] /\ x[1] <= lv[j][t].hi
  /\ opened \in BOOLEAN

\* THE HEADLINE. Once open, every read, of every key, at every snapshot up
\* to the newest sequence, returns the newest version of that key the
\* snapshot may see. Lean: read_newest, with the theorem for each step.
\* (Binding A and S by membership in a one-element set makes TLC compute
\* each once per state and key rather than once per snapshot.)
ReadNewest ==
  opened =>
    \A A \in {AllVersions} : \A k \in Keys : \A S \in {Sources(k)} :
      \A snap \in 0..seq : ReadIn(S, k, snap) = NewestIn(A, k, snap)

\* Once open, every level's tables are in key order and their ranges do
\* not overlap: what the binary search needs.
LevelsSorted ==
  opened => \A j \in 1..Levels : \A t \in 1..(Len(lv[j]) - 1) : lv[j][t].hi < lv[j][t + 1].lo

\* Once open, the binary search on each level offers exactly what a linear
\* scan of that level does. Lean: bsearch_eq_scan, level_read_bsearch.
BisectIsScan ==
  opened => \A j \in 1..Levels : \A k \in Keys : Candidate(j, k) = ScanCandidate(j, k)

====
