---- MODULE CommitOrderedAppend ----
\* Commit-ordered append (plan 3.6): `Transaction::append(log, entry,
\* once_key)` gives an entry the log's next position in the ordered step of
\* the commit, so positions follow commit order, are dense from 1, and an
\* append never conflicts. This model supersedes defradb.rs #1911 (its five
\* invariants and four REDs are ported here under generic names) and adds
\* density, at-most-once keys, numbering at commit, group commit, aborts, a
\* failed group, the Phase 7 pipeline and the transaction's own view.
\* Crashes per durability mode are in CommitOrderedAppendCrash.tla.
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/Append.lean:
\*   reachable_inv              the ordered step keeps the invariant below,
\*                              whatever it decides and whoever aborts
\*   dense_from_one             positions assigned after validation are
\*                              exactly 1..head, in assignment order
\*   unique_positions           no two rows share a position
\*   at_most_once               no two rows carry one once key
\*   commit_order               a smaller position belongs to an earlier
\*                              commit, or to an earlier append of the same one
\*   snapshot_sees_prefix       a snapshot whose head is H sees exactly the
\*                              rows at positions 1..H, all of them
\*   view_only_head_duplicates  the RED ViewOnlyHead, as a counterexample
\*   assign_before_validation_leaves_hole
\*                              the RED AssignBeforeValidation, likewise
\*   stamps_leave_hole          the RED Stamps, likewise
\* TLC checks the same invariants here over every interleaving of a few
\* writers, groups, aborts, WAL errors and reads.
\*
\* THE DESIGN (plan 3.6 and 4.7; the code is not written yet).
\*   Transaction::append      queues (log, entry, once key) in the
\*     transaction. Nothing is read or validated for it, and the transaction
\*     never sees its own appends: their positions do not exist until commit.
\*   The ordered step         the group-commit leader, under today's commit
\*     mutex, takes the queued commits in group order. For each member it
\*     first validates the member's reads; only a member that passes gets a
\*     sequence and positions. The head and the once keys are read from the
\*     view plus the earlier members of the same group: nothing is cached,
\*     so a group that fails leaves no trace.
\*   Positions                the next position is head + 1. An append whose
\*     once key already holds a position appends nothing. Each assigned
\*     append writes entry_key(p) = entry, once_key = p and head_key = p in
\*     the member's own atomic commit.
\*   Publication              the group's writes become visible together,
\*     at its sequences. A reader bounds itself by the head key in its own
\*     snapshot and reads positions (cursor, head]; a missing row there is a
\*     failed read, never a skip.
\*   The Phase 7 pipeline (4.7, Depth = 2)   the decide stage runs ahead of
\*     publication: a later group decides while an earlier decided group is
\*     still being written. It reads the decided prefix: the view plus every
\*     decided, unpublished group.
\*
\* THE REJECTED DESIGNS AND MISUSES. Each is a RED configuration.
\*   Mode = "Counter"          (#1911 Counter) the head key is read and
\*     bumped inside the transaction, as an ordinary validated write. Two
\*     appenders that touch nothing else in common conflict on it.
\*   Mode = "Detached"         (#1911 Detached, DetachedOrder; defradb.rs
\*     #1897) the transaction writes an unnumbered pending row; a second,
\*     separate commit later numbers every pending row in begin order. A
\*     second durable commit per write, positions out of commit order, and
\*     an append committed without its number.
\*   Mode = "Stamp"            (regolith #216, #218; plan D1) the position
\*     is the commit's sequence number. Every commit takes a sequence, so a
\*     commit that does not append leaves a hole in the log.
\*   Mutant = "LatestBound"    (#1911 StampLatest) the reader bounds itself
\*     by the latest assigned position instead of the head in its snapshot,
\*     moving its cursor past rows that are decided but not yet visible.
\*   Mutant = "ViewOnlyHead"   a group member reads the head from the view
\*     only, ignoring the earlier members of its group.
\*   Mutant = "OnceFromView"   a once key is looked up in the view only,
\*     ignoring earlier members of the group and earlier appends of the
\*     same transaction.
\*   Mutant = "AssignBeforeValidation"   positions are taken before the
\*     member is validated, so a member that then aborts consumes them.
\*   Mutant = "HeadCache"      the head lives in a cache advanced at
\*     assignment, before publication; a WAL error does not roll it back.
\*   Mutant = "PublishedView"  (Phase 7) the decide stage reads the
\*     published view while an earlier decided group is unpublished.
\*
\* READINGS CHOSEN WHERE THE PLAN LEAVES ROOM.
\*   - A validation failure on another key is a nondeterministic outcome
\*     for the writers in MayAbort: whatever the other key is, an append
\*     must stay correct, so any failure pattern is allowed.
\*   - A WAL error fails the group at the front of the pipeline and every
\*     group decided after it (they were decided on top of it). With
\*     Depth = 2 the plan latches the engine read-only after such an error
\*     (4.7 item 7); this model lets the engine continue, which allows more
\*     behaviours, so every invariant that holds here holds there too.
\*   - After a group, the head key holds the last position any committed
\*     member of it assigned (each assignment writes head_key = p); a group
\*     that assigns nothing leaves the head key alone.
\*   - Groups publish in decide order (publication is over the contiguous
\*     decided prefix), and a WAL error is injected at the front group only:
\*     an error at a later group is the same as publishing the earlier ones
\*     first, and readers see only published state.
\*   - Stamps (Mode = "Stamp") take one sequence per commit; that red uses
\*     writers that append at most once and no once keys, which is the shape
\*     #1911 checked.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - One log. Logs have disjoint head, entry and once keys, so two logs
\*     are two copies of this model that share only the commit order.
\*   - Entries are named by <<writer, append index>>. A row is the fact
\*     "this append was assigned this position". In the store a second
\*     assignment of one position overwrites the entry_key put of the first;
\*     keeping both as facts lets INV_UniqueCursors name the defect directly.
\*   - A reader takes its snapshot and reads in one step, at the published
\*     view. Without crashes the view only grows, so an older snapshot is
\*     an earlier published view, on which every invariant was checked.
\*   - Group order is any order of the chosen members, which includes the
\*     arrival order the engine uses.
\*   - A transaction whose commit aborted or failed does not retry; a retry
\*     is a new transaction, which another writer already plays.
\*
\* CONFIGURATIONS. Teeth (plan 7.1 item 11) come two ways. Each RED lists
\* the invariants it is not about before the one it names, so the state TLC
\* reports breaks the named one alone. And each mutant has a Teeth
\* configuration, GREEN, that checks every invariant but the ones it is
\* about over its whole state space. Invariants a mutant breaks by design
\* are left out of both and named in its configuration.
\*   MC_CommitOrderedAppend_Green_Writers      every writer shape, one at a time
\*   MC_CommitOrderedAppend_Green_Groups       groups of two
\*   MC_CommitOrderedAppend_Green_Faults       groups of two with aborts
\*                                             and a WAL error
\*   MC_CommitOrderedAppend_Green_Pipeline     two decided groups in flight
\*   MC_CommitOrderedAppend_Teeth_<mutant>     GREEN, one per mutant below
\*                                             (Detached covers its three REDs)
\*   MC_CommitOrderedAppend_Red_Counter                 INV_NoDisjointConflict
\*   MC_CommitOrderedAppend_Red_Detached                INV_OneCommitPerWrite
\*   MC_CommitOrderedAppend_Red_DetachedOrder           INV_CommitOrder
\*   MC_CommitOrderedAppend_Red_DetachedNumbering       INV_NumberedAtCommit
\*   MC_CommitOrderedAppend_Red_LatestBound             INV_NoSkip
\*   MC_CommitOrderedAppend_Red_Stamps                  INV_Dense
\*   MC_CommitOrderedAppend_Red_ViewOnlyHead            INV_UniqueCursors
\*   MC_CommitOrderedAppend_Red_OnceFromView            INV_AtMostOnce
\*   MC_CommitOrderedAppend_Red_AssignBeforeValidation  INV_Dense
\*   MC_CommitOrderedAppend_Red_HeadCache               INV_Dense
\*   MC_CommitOrderedAppend_Red_PublishedView           INV_UniqueCursors

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Singles,      \* writers that append once, with no once key
  SharedOnce,   \* writers that append once with the once key "o1", which
                \* they all share: at most one of them may get a row
  Doubles,      \* writers that append twice to the log, no once key
  RepeatOnce,   \* writers that append twice with the same once key "o2"
  Silent,       \* writers whose commit appends nothing
  MayAbort,     \* writers whose validation on another key may fail
  GroupSize,    \* the most members one commit group takes
  Depth,        \* decided groups in flight: 1 is today's commit mutex,
                \* 2 is the Phase 7 pipeline
  MaxWalErrors, \* the most WAL errors the model injects
  Mode,         \* how positions are assigned: "Append" (the design),
                \* "Counter", "Detached" or "Stamp"
  Mutant        \* "none" or one misuse of the design, named above

\* Every writer. Each writer is one transaction, which commits at most once.
Writers == Singles \cup SharedOnce \cup Doubles \cup RepeatOnce \cup Silent

\* The marker for an append made without a once key.
NoOnce == "none"

\* The once keys any writer uses.
OnceKeys == {"o1", "o2"}

\* The appends writer w makes, in the order it calls `append`: each element
\* is the once key passed, or NoOnce.
Appends(w) ==
  CASE w \in Singles    -> <<NoOnce>>
    [] w \in SharedOnce -> <<"o1">>
    [] w \in Doubles    -> <<NoOnce, NoOnce>>
    [] w \in RepeatOnce -> <<"o2", "o2">>
    [] w \in Silent     -> <<>>

\* The writer shapes are disjoint, so every writer has exactly one shape.
ASSUME \A A, B \in {Singles, SharedOnce, Doubles, RepeatOnce, Silent} :
         A # B => A \cap B = {}
\* Only writers can abort; a group holds at least one member; the pipeline
\* is today's mutex or two deep; the mode and mutant are ones named above.
ASSUME MayAbort \subseteq Writers
ASSUME GroupSize \in Nat \ {0} /\ Depth \in {1, 2} /\ MaxWalErrors \in Nat
ASSUME Mode \in {"Append", "Counter", "Detached", "Stamp"}
ASSUME Mutant \in {"none", "LatestBound", "ViewOnlyHead", "OnceFromView",
                   "AssignBeforeValidation", "HeadCache", "PublishedView"}
\* A mutant is a misuse of the design, so it runs on the design.
ASSUME Mutant # "none" => Mode = "Append"
\* The rejected designs ran under a commit mutex, with #1911's writer shapes:
\* stamps on writers appending at most once, no once keys where the design
\* had none.
ASSUME Mode # "Append" => Depth = 1
ASSUME Mode = "Stamp" => Doubles \cup RepeatOnce \cup SharedOnce = {}
ASSUME Mode = "Detached" => RepeatOnce \cup SharedOnce = {}

VARIABLES
  phase,      \* [Writers -> Phases]: where each transaction is
  snapHead,   \* [Writers -> Nat]: Counter only, the head its snapshot read
  shortId,    \* [Writers -> Nat]: Detached only, the begin order
  nextShort,  \* Detached only: the next begin-order number
  cseq,       \* [Writers -> Nat]: the sequence the writer's commit took
  rows,       \* the published rows: [pos, w, i, once] records
  onceAt,     \* [OnceKeys -> Nat]: the position each once key holds in the
              \* published view, 0 when it holds none
  head,       \* the published head key: the newest position, 0 for none
  vseq,       \* the published sequence: the newest visible commit
  inflight,   \* the decided groups not yet published, oldest first
  pending,    \* Detached only: committed appends <<w, i>> not yet numbered
  cache,      \* HeadCache only: the cached head
  walErrors,  \* the WAL errors injected so far
  commits,    \* the durable commits issued, of any kind
  writes,     \* the writer transactions that committed
  rcur,       \* the reader's cursor: it has read every position up to it
  seen,       \* the entries <<w, i>> the reader was handed
  readFailed  \* a read found a position at or below its snapshot's head
              \* with no row

\* The variables the transactions own.
txnVars == <<phase, snapHead, shortId, nextShort, cseq>>
\* The variables the engine owns.
engineVars == <<rows, onceAt, head, vseq, inflight, pending, cache, walErrors, commits, writes>>
\* The variables the reader owns.
readerVars == <<rcur, seen, readFailed>>
\* Every variable, so a step that changes none of them is a stutter.
vars == <<txnVars, engineVars, readerVars>>

\* A transaction's phases: not begun, open (its body runs and it may read),
\* decided (validated and numbered, waiting for publication), done
\* (published: its commit returned), aborted (its validation failed), and
\* failed (its group hit a WAL error, so its commit returned an error).
Phases == {"idle", "open", "decided", "done", "aborted", "failed"}

\* The set of elements of a sequence.
Range(s) == {s[k] : k \in DOMAIN s}

----------------------------------------------------------------------------
\* The decided prefix: what the ordered step reads.

\* The newest decided group, the one the next decision builds on.
Last == inflight[Len(inflight)]

\* The head after every decided group: the published head when nothing is in
\* flight, else the head the newest decided group leaves.
DecidedHead == IF inflight = <<>> THEN head ELSE Last.postHead

\* The once keys after every decided group, likewise.
DecidedOnce == IF inflight = <<>> THEN onceAt ELSE Last.postOnce

\* The sequence after every decided group, likewise. Sequences are always
\* taken from the decided prefix; no mutant here is about them.
DecidedSeq == IF inflight = <<>> THEN vseq ELSE Last.postSeq

\* The head a new group starts from. The design: the decided prefix. The
\* HeadCache mutant: its cache. The PublishedView mutant: the published
\* view, missing any decided group still in flight.
StartHead ==
  CASE Mutant = "HeadCache"     -> cache
    [] Mutant = "PublishedView" -> head
    [] OTHER                    -> DecidedHead

\* The once keys a new group starts from, by the same rule.
StartOnce == IF Mutant = "PublishedView" THEN onceAt ELSE DecidedOnce

----------------------------------------------------------------------------
\* The ordered step. It walks a group's members in group order, carrying a
\* running state: the head the next position is counted from, the last
\* position the group wrote to the head key (0 for none), the once keys
\* and the sequence as the earlier members left them, the rows and pending
\* appends the group adds, the members that committed and those that
\* aborted, and each writer's sequence.

\* Writer w's i-th append against the running state st. If its once key
\* already holds a position (in the view, an earlier member, or an earlier
\* append of w), it appends nothing. Otherwise it takes the next position:
\* head + 1, or, for stamps, the commit's own sequence; and it writes the
\* entry, the once key and head_key = p. OnceFromView looks the once key up
\* in the group's starting view only.
AssignOne(st, w, i) ==
  LET o   == Appends(w)[i]
      dup == /\ o # NoOnce
             /\ IF Mutant = "OnceFromView" THEN StartOnce[o] # 0 ELSE st.onceAt[o] # 0
      p   == IF Mode = "Stamp" THEN st.seq ELSE st.head + 1
  IN IF dup THEN st
     ELSE [st EXCEPT !.head    = IF Mode = "Stamp" THEN @ ELSE p,
                     !.headPut = IF Mode = "Stamp" THEN @ ELSE p,
                     !.onceAt  = IF o = NoOnce THEN @ ELSE [@ EXCEPT ![o] = p],
                     !.rows    = @ \cup {[pos |-> p, w |-> w, i |-> i, once |-> o]}]

\* Writer w's appends from the i-th on, in append order: several appends of
\* one transaction take consecutive positions.
RECURSIVE AssignFrom(_, _, _)
AssignFrom(st, w, i) ==
  IF i > Len(Appends(w)) THEN st ELSE AssignFrom(AssignOne(st, w, i), w, i + 1)

\* One member w of the group, given the set F of members whose validation on
\* another key fails.
\*   valid: w is not in F, and, for Counter, the head it read in its
\*     snapshot is still the head (an ordinary validated read of it).
\*   start: w's sequence is the next one; ViewOnlyHead also resets the head
\*     to the group's starting head, forgetting earlier members.
\*   after: the running state once w's appends are numbered (Detached: once
\*     they are queued unnumbered).
\* A valid member commits with all of that. An invalid one aborts and takes
\* nothing; under AssignBeforeValidation it has already taken its positions,
\* so the running head keeps them (its own writes, the head key among them,
\* are discarded with it).
DecideMember(st, w, F) ==
  LET valid == /\ w \notin F
               /\ Mode = "Counter" => snapHead[w] = st.head
      start == [st EXCEPT !.head = IF Mutant = "ViewOnlyHead" THEN StartHead ELSE @,
                          !.seq  = @ + 1]
      after == IF Mode = "Detached"
                 THEN [start EXCEPT !.pend = @ \cup {<<w, i>> : i \in 1..Len(Appends(w))}]
                 ELSE AssignFrom(start, w, 1)
  IN CASE valid ->
            [after EXCEPT !.members = Append(@, w), !.cseq = [@ EXCEPT ![w] = start.seq]]
       [] Mutant = "AssignBeforeValidation" ->
            [st EXCEPT !.head = after.head, !.aborted = @ \cup {w}]
       [] OTHER ->
            [st EXCEPT !.aborted = @ \cup {w}]

\* Every member of group g in group order, starting from st.
RECURSIVE DecideAll(_, _, _)
DecideAll(st, g, F) ==
  IF g = <<>> THEN st ELSE DecideAll(DecideMember(st, Head(g), F), Tail(g), F)

\* The running state a group starts with: the starting head and once keys,
\* the decided sequence, nothing added or written yet.
GroupStart ==
  [head |-> StartHead, headPut |-> 0, onceAt |-> StartOnce, seq |-> DecidedSeq,
   rows |-> {}, pend |-> {}, members |-> <<>>, aborted |-> {}, cseq |-> cseq]

\* The groups the leader may form from the writers in S: one to GroupSize
\* distinct writers, in any order.
Groups(S) ==
  UNION {{g \in [1..n -> S] : \A a, b \in 1..n : a # b => g[a] # g[b]} : n \in 1..GroupSize}

----------------------------------------------------------------------------
\* Actions.

\* The start: nobody has begun, the log is empty, nothing is in flight, and
\* the reader has read nothing.
Init ==
  /\ phase      = [w \in Writers |-> "idle"]
  /\ snapHead   = [w \in Writers |-> 0]
  /\ shortId    = [w \in Writers |-> 0]
  /\ nextShort  = 1
  /\ cseq       = [w \in Writers |-> 0]
  /\ rows       = {}
  /\ onceAt     = [o \in OnceKeys |-> 0]
  /\ head       = 0
  /\ vseq       = 0
  /\ inflight   = <<>>
  /\ pending    = {}
  /\ cache      = 0
  /\ walErrors  = 0
  /\ commits    = 0
  /\ writes     = 0
  /\ rcur       = 0
  /\ seen       = {}
  /\ readFailed = FALSE

\* Writer w begins: its snapshot is the published view. Counter records the
\* head it reads there; Detached hands it the next begin-order number
\* (#1897's short ID). Its appends are queued while it is open.
Begin(w) ==
  /\ phase[w] = "idle"
  /\ phase'     = [phase EXCEPT ![w] = "open"]
  /\ snapHead'  = IF Mode = "Counter" THEN [snapHead EXCEPT ![w] = head] ELSE snapHead
  /\ shortId'   = IF Mode = "Detached" THEN [shortId EXCEPT ![w] = nextShort] ELSE shortId
  /\ nextShort' = IF Mode = "Detached" THEN nextShort + 1 ELSE nextShort
  /\ UNCHANGED <<cseq>>
  /\ UNCHANGED engineVars
  /\ UNCHANGED readerVars

\* The ordered step decides group g, in which the members in F fail
\* validation on another key. The group joins the pipeline as a record of
\* what it writes: its rows, the once keys it sets, its last head-key write
\* (0 for none), the head, once keys and sequence the decided prefix holds
\* after it (what the next decision reads), and its pending appends
\* (Detached). Members that committed are decided; the others aborted.
\* HeadCache advances its cache here, before publication.
Decide(g, F) ==
  /\ Len(inflight) < Depth
  /\ LET st == DecideAll(GroupStart, g, F)
     IN /\ inflight' = Append(inflight,
             [members  |-> st.members,
              rows     |-> st.rows,
              onceSet  |-> [o \in OnceKeys |-> IF st.onceAt[o] # StartOnce[o] THEN st.onceAt[o] ELSE 0],
              headPut  |-> st.headPut,
              postHead |-> IF st.headPut # 0 THEN st.headPut ELSE DecidedHead,
              postOnce |-> st.onceAt,
              postSeq  |-> st.seq,
              pend     |-> st.pend])
        /\ phase' = [w \in Writers |->
                       CASE w \in Range(st.members) -> "decided"
                         [] w \in st.aborted        -> "aborted"
                         [] OTHER                   -> phase[w]]
        /\ cseq'  = st.cseq
        /\ cache' = IF Mutant = "HeadCache" THEN st.head ELSE cache
  /\ UNCHANGED <<snapHead, shortId, nextShort>>
  /\ UNCHANGED <<rows, onceAt, head, vseq, pending, walErrors, commits, writes>>
  /\ UNCHANGED readerVars

\* The oldest decided group is written to the WAL, applied and published:
\* its rows, once keys and head become visible at its sequences, and its
\* members' commits return. Each member is one transaction's own commit.
Publish ==
  /\ inflight # <<>>
  /\ LET g == Head(inflight)
     IN /\ rows'     = rows \cup g.rows
        /\ onceAt'   = [o \in OnceKeys |-> IF g.onceSet[o] # 0 THEN g.onceSet[o] ELSE onceAt[o]]
        /\ head'     = IF g.headPut # 0 THEN g.headPut ELSE head
        /\ vseq'     = g.postSeq
        /\ pending'  = pending \cup g.pend
        /\ phase'    = [w \in Writers |-> IF w \in Range(g.members) THEN "done" ELSE phase[w]]
        /\ commits'  = commits + Len(g.members)
        /\ writes'   = writes + Len(g.members)
        /\ inflight' = Tail(inflight)
  /\ UNCHANGED <<snapHead, shortId, nextShort, cseq>>
  /\ UNCHANGED <<cache, walErrors>>
  /\ UNCHANGED readerVars

\* A WAL error at the oldest decided group, after its positions were
\* assigned. That group and every group decided on top of it fail; their
\* members' commits return an error and nothing of them is published. The
\* next group decides from the view again. HeadCache's cache is not rolled
\* back.
WalError ==
  /\ inflight # <<>>
  /\ walErrors < MaxWalErrors
  /\ LET failed == UNION {Range(inflight[k].members) : k \in 1..Len(inflight)}
     IN phase' = [w \in Writers |-> IF w \in failed THEN "failed" ELSE phase[w]]
  /\ inflight'  = <<>>
  /\ walErrors' = walErrors + 1
  /\ UNCHANGED <<snapHead, shortId, nextShort, cseq>>
  /\ UNCHANGED <<rows, onceAt, head, vseq, pending, cache, commits, writes>>
  /\ UNCHANGED readerVars

\* Detached only: the place of pending append e = <<w, i>> when the pending
\* appends are sorted by their writer's begin order, then append order;
\* 1 for the first. Begin order is #1897's short-ID order.
Rank(e) ==
  Cardinality({x \in pending : \/ shortId[x[1]] < shortId[e[1]]
                               \/ x[1] = e[1] /\ x[2] <= e[2]})

\* Detached only: #1897's second commit. It numbers every pending append
\* after the head by its rank, and writes the new head. It is a durable
\* commit of its own, under the commit mutex, so it waits for nothing in
\* flight.
Sequence ==
  /\ Mode = "Detached"
  /\ pending # {}
  /\ inflight = <<>>
  /\ rows'    = rows \cup {[pos |-> head + Rank(e), w |-> e[1], i |-> e[2], once |-> NoOnce] : e \in pending}
  /\ head'    = head + Cardinality(pending)
  /\ pending' = {}
  /\ vseq'    = vseq + 1
  /\ commits' = commits + 1
  /\ UNCHANGED <<onceAt, inflight, cache, walErrors, writes>>
  /\ UNCHANGED txnVars
  /\ UNCHANGED readerVars

\* The head in the reader's snapshot, the published view: the head key, or,
\* for stamps, the published sequence.
SnapHead == IF Mode = "Stamp" THEN vseq ELSE head

\* The latest assigned position, decided or not: what LatestBound reads.
LatestHead == IF Mode = "Stamp" THEN DecidedSeq ELSE DecidedHead

\* The bound the reader reads up to. The design: the head in its snapshot.
Bound == IF Mutant = "LatestBound" THEN LatestHead ELSE SnapHead

\* Some position between the cursor and the snapshot's head holds no row.
Missing == \E p \in (rcur + 1)..SnapHead : \A r \in rows : r.pos # p

\* The reader reads positions (rcur, Bound] in its snapshot. A missing row
\* at or below its snapshot's head fails the read, and the cursor stays; a
\* reader never skips a row it can see is missing. Otherwise it is handed
\* every row in the range and moves its cursor to the bound. Positions
\* above the snapshot's head are not in its snapshot at all: only
\* LatestBound reads that far, and it cannot tell them from rows that are
\* not committed yet.
Read ==
  /\ Bound > rcur
  /\ ~readFailed
  /\ IF Missing
       THEN /\ readFailed' = TRUE
            /\ UNCHANGED <<rcur, seen>>
       ELSE /\ seen' = seen \cup {<<r.w, r.i>> : r \in {x \in rows : rcur < x.pos /\ x.pos <= Bound}}
            /\ rcur' = Bound
            /\ UNCHANGED readFailed
  /\ UNCHANGED txnVars
  /\ UNCHANGED engineVars

\* Every step the system can take. The leader forms a group from open
\* writers and picks which of them fail validation on another key.
Next ==
  \/ \E w \in Writers : Begin(w)
  \/ \E g \in Groups({w \in Writers : phase[w] = "open"}) :
       \E F \in SUBSET (MayAbort \cap Range(g)) : Decide(g, F)
  \/ Publish
  \/ WalError
  \/ Sequence
  \/ Read

\* Every behaviour: start in Init, then take Next steps or stutter.
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Invariants. The first five are #1911's.

\* Every variable holds what its comment says.
TypeOK ==
  /\ phase \in [Writers -> Phases]
  /\ snapHead \in [Writers -> Nat]
  /\ shortId \in [Writers -> Nat]
  /\ cseq \in [Writers -> Nat]
  /\ \A r \in rows : r.pos \in Nat \ {0} /\ r.w \in Writers /\ r.i \in 1..Len(Appends(r.w))
  /\ onceAt \in [OnceKeys -> Nat]
  /\ head \in Nat /\ vseq \in Nat
  /\ Len(inflight) <= Depth
  /\ pending \subseteq Writers \X (1..2)
  /\ walErrors <= MaxWalErrors
  /\ rcur \in Nat
  /\ seen \subseteq Writers \X (1..2)
  /\ readFailed \in BOOLEAN

\* A position the reader has passed never gains a row it was not handed: a
\* row at or below the cursor was seen. Lean: snapshot_sees_prefix (the rows
\* at or below a snapshot's head never change).
INV_NoSkip == \A r \in rows : r.pos <= rcur => <<r.w, r.i>> \in seen

\* No two appends were assigned one position. Lean: unique_positions.
INV_UniqueCursors == \A a, b \in rows : a.pos = b.pos => a = b

\* Row a comes before row b in commit order: a's transaction took an
\* earlier sequence, or both are appends of one transaction and a was made
\* first.
Before(a, b) == \/ cseq[a.w] < cseq[b.w]
                \/ a.w = b.w /\ a.i < b.i

\* Positions follow commit order, several appends per transaction included.
\* Lean: commit_order.
INV_CommitOrder == \A a, b \in rows : a.pos < b.pos => Before(a, b)

\* An append never causes a conflict: the only writers that abort are those
\* whose validation on another key may fail. (In Lean, orderedStep takes
\* the validation outcome as given and reads nothing it validates.)
INV_NoDisjointConflict == \A w \in Writers \ MayAbort : phase[w] # "aborted"

\* A write costs exactly its own commit: no second commit numbers it. (In
\* Lean, orderedStep numbers a transaction in the one step that commits it.)
INV_OneCommitPerWrite == commits = writes

\* A snapshot with head H sees rows 1..H, every one of them, and no read
\* ever finds one missing. The view only grows here, so checking the
\* current view at every state checks every snapshot. Lean: dense_from_one
\* and snapshot_sees_prefix.
INV_Dense == {r.pos : r \in rows} = 1..SnapHead /\ ~readFailed

\* At most one row carries a once key, and the once key holds exactly that
\* row's position. Lean: at_most_once.
INV_AtMostOnce ==
  /\ \A a, b \in rows : a.once # NoOnce /\ a.once = b.once => a = b
  /\ \A r \in rows : r.once # NoOnce => onceAt[r.once] = r.pos
  /\ \A o \in OnceKeys : onceAt[o] # 0 => \E r \in rows : r.once = o

\* Writer w's i-th append has its number in the view: its own row, or, for
\* an append whose once key was already taken, the position the once key
\* holds.
Numbered(w, i) ==
  \/ \E r \in rows : r.w = w /\ r.i = i
  \/ Appends(w)[i] # NoOnce /\ onceAt[Appends(w)[i]] # 0

\* Every append of a committed transaction has its position the moment the
\* commit returns. This replaces #1911's unchecked liveness ("eventually
\* numbered") with a safety property. (In Lean, by construction, as for
\* INV_OneCommitPerWrite.)
INV_NumberedAtCommit ==
  \A w \in Writers : phase[w] = "done" => \A i \in 1..Len(Appends(w)) : Numbered(w, i)

\* While a transaction is open, and so may still read, none of its own
\* appends is in the view; its snapshot is an earlier view, so no read
\* inside it can see its own appends. It holds because positions exist only
\* after commit.
INV_OwnAppendsInvisible == \A w \in Writers : phase[w] = "open" => \A r \in rows : r.w # w

====
