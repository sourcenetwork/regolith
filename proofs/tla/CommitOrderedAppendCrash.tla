---- MODULE CommitOrderedAppendCrash ----
\* Commit-ordered append (plan 3.6) across crashes, per durability mode
\* (plan 7.1, CommitOrderedAppend.tla item 9). CommitOrderedAppend.tla
\* checks the ordered step without crashes; this module adds the WAL, the
\* durable and visible prefixes, and power cuts.
\*
\* PROVED FOR EVERY SIZE in Lean:
\*   Regolith/Append.lean, snapshot_sees_prefix
\*       the state after any prefix of the commit order holds exactly the
\*       rows 1..H of the full log, H being that prefix's head: a recovered
\*       prefix is dense, and its rows never change as later commits land
\*   Regolith/Append.lean, dense_from_one, unique_positions, at_most_once
\*       every such prefix is dense from 1, unique, and holds each once key
\*       once
\*   Regolith/WalRecovery.lean, recovers_prefix
\*       recovery yields a gap-free prefix of commit order holding every
\*       durable record (here, a crash keeps such a prefix by construction)
\* TLC checks the invariants below over every interleaving of a few
\* commits, syncs, publications, two readers and a power cut.
\*
\* THE DESIGN (plan 3.6 "Durability", 4.2 and 4.7; the code is not
\* written yet).
\*   Each commit's record (its rows, once keys and head) is one WAL record,
\*   written in commit order. A sync makes every written record durable.
\*   Publication makes the next record visible; under Immediate durability
\*   only once it is durable, so the visible prefix never passes the durable
\*   one. A power cut keeps a gap-free prefix of the records that holds every
\*   durable one (WalRotation.tla), and recovery makes it all visible. The
\*   next commit after recovery numbers from the recovered head.
\*
\* TWO READERS.
\*   The internal reader keeps its cursor in the same database: it reads
\*   positions (cursor, H] of the visible view, H being the head there, and
\*   commits cursor = H as a record of its own. That record follows every
\*   row it read in the WAL, so a crash that keeps the cursor keeps the rows.
\*   The external reader keeps its cursor and what it has recorded outside
\*   the database, so a crash does not roll them back.
\*
\* WHAT EACH MODE PROMISES (plan 3.6).
\*   Immediate: visible at or below durable, so an acknowledged commit and
\*     the positions anyone saw survive any crash (INV_VisibleDurable,
\*     INV_AckStable, INV_ExternalStable).
\*   Eventual: a crash may drop acknowledged commits and their positions are
\*     assigned again. The log stays dense and unique (INV_Dense,
\*     INV_UniqueCursors, INV_AtMostOnce) and the internal reader never
\*     skips (INV_NoSkip). An external reader can see a position reassigned:
\*     the RED.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - One writer per record. A group's members share one WAL record, which
\*     a crash keeps or drops whole, so a group is a writer with several
\*     appends; CommitOrderedAppend.tla checks the group's numbering.
\*   - Validation and aborts: an aborted commit writes no record.
\*   - The once key a record sets is read off its rows: the row and
\*     once_key = p are written in the same record.
\*   - A writer whose commit was cut short does not retry; the writers that
\*     have not begun play the commits after recovery.
\*
\* CONFIGURATIONS.
\*   MC_CommitOrderedAppendCrash_Green_Immediate   Durability = "Immediate"
\*     every invariant holds.
\*   MC_CommitOrderedAppendCrash_Green_Eventual    Durability = "Eventual"
\*     INV_Dense, INV_UniqueCursors, INV_AtMostOnce and INV_NoSkip hold. It
\*     is also the RED's teeth: the same constants, every invariant the RED
\*     is not about, over the whole state space.
\*   MC_CommitOrderedAppendCrash_Red_EventualExternal
\*     INV_ExternalStable fails.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Singles,     \* writers that append once, with no once key
  SharedOnce,  \* writers that append once with the shared once key "o1"
  Doubles,     \* writers that append twice, no once key
  Durability,  \* "Immediate" or "Eventual"
  MaxCrashes   \* the most power cuts the model injects

\* Every writer; each commits at most once.
Writers == Singles \cup SharedOnce \cup Doubles

\* The marker for an append made without a once key.
NoOnce == "none"

\* The internal reader's name on its cursor records.
Reader == "reader"

\* The appends writer w makes, in order: the once key passed, or NoOnce.
Appends(w) ==
  CASE w \in Singles    -> <<NoOnce>>
    [] w \in SharedOnce -> <<"o1">>
    [] w \in Doubles    -> <<NoOnce, NoOnce>>

ASSUME \A A, B \in {Singles, SharedOnce, Doubles} : A # B => A \cap B = {}
ASSUME Reader \notin Writers
ASSUME Durability \in {"Immediate", "Eventual"} /\ MaxCrashes \in Nat

VARIABLES
  wal,      \* the records written, in commit order
  durable,  \* how many leading records a sync made durable
  visible,  \* how many leading records are published
  phase,    \* [Writers -> {"idle", "written", "acked", "recovered", "lost"}]
  acked,    \* the writers whose commit returned success; a crash keeps it
  crashes,  \* the power cuts so far
  iseen,    \* the entries <<w, i>> the internal reader was handed
  xcur,     \* the external reader's cursor, kept outside the database
  xseen     \* the <<position, entry>> pairs the external reader recorded

\* Every variable, so a step that changes none of them is a stutter.
vars == <<wal, durable, visible, phase, acked, crashes, iseen, xcur, xseen>>

\* The greatest element of a finite, nonempty set of naturals.
Max(S) == CHOOSE m \in S : \A n \in S : n <= m

----------------------------------------------------------------------------
\* The database as of the first n records. A record is
\* [kind |-> "commit", w, rows, head] for a writer's commit (head 0 when it
\* assigned nothing) or [kind |-> "cursor", w |-> Reader, rows |-> {},
\* head |-> 0, value] for the internal reader's cursor commit.

\* The rows the first n records hold.
RowsIn(n) == UNION {wal[k].rows : k \in 1..n}

\* The head key after the first n records: the last head any of them wrote.
HeadIn(n) ==
  LET ks == {k \in 1..n : wal[k].head # 0}
  IN IF ks = {} THEN 0 ELSE wal[Max(ks)].head

\* Once key o holds a position after the first n records.
OnceTaken(n, o) == \E r \in RowsIn(n) : r.once = o

\* The internal reader's cursor after the first n records: the last value
\* it committed, 0 before its first.
CursorIn(n) ==
  LET ks == {k \in 1..n : wal[k].kind = "cursor"}
  IN IF ks = {} THEN 0 ELSE wal[Max(ks)].value

\* The rows writer w's commit assigns when the first n records are the
\* decided prefix: positions after the head there, in append order, each
\* append skipped when its once key is taken (there or by an earlier
\* append of w).
RECURSIVE AssignFrom(_, _, _, _, _)
AssignFrom(w, i, h, taken, acc) ==
  IF i > Len(Appends(w)) THEN acc
  ELSE LET o == Appends(w)[i]
       IN IF o # NoOnce /\ o \in taken
            THEN AssignFrom(w, i + 1, h, taken, acc)
            ELSE AssignFrom(w, i + 1, h + 1, taken \cup ({o} \ {NoOnce}),
                            acc \cup {[pos |-> h + 1, w |-> w, i |-> i, once |-> o]})
NewRows(w, n) ==
  AssignFrom(w, 1, HeadIn(n), {o \in {"o1"} : OnceTaken(n, o)}, {})

----------------------------------------------------------------------------
\* Actions.

\* The start: an empty log, nothing synced or visible, nobody begun.
Init ==
  /\ wal     = <<>>
  /\ durable = 0
  /\ visible = 0
  /\ phase   = [w \in Writers |-> "idle"]
  /\ acked   = {}
  /\ crashes = 0
  /\ iseen   = {}
  /\ xcur    = 0
  /\ xseen   = {}

\* Writer w commits: the ordered step numbers its appends from the decided
\* prefix (every record written so far) and writes its record to the WAL.
Commit(w) ==
  /\ phase[w] = "idle"
  /\ LET rs == NewRows(w, Len(wal))
     IN wal' = Append(wal, [kind |-> "commit", w |-> w, rows |-> rs,
                            head |-> IF rs = {} THEN 0 ELSE Max({r.pos : r \in rs})])
  /\ phase' = [phase EXCEPT ![w] = "written"]
  /\ UNCHANGED <<durable, visible, acked, crashes, iseen, xcur, xseen>>

\* A sync makes every written record durable.
Sync ==
  /\ durable < Len(wal)
  /\ durable' = Len(wal)
  /\ UNCHANGED <<wal, visible, phase, acked, crashes, iseen, xcur, xseen>>

\* The next record is published. Under Immediate it must be durable first.
\* A writer's commit returns success when its record is published.
Publish ==
  /\ visible < Len(wal)
  /\ Durability = "Immediate" => visible < durable
  /\ visible' = visible + 1
  /\ LET r == wal[visible + 1]
     IN IF r.kind = "commit"
          THEN /\ phase' = [phase EXCEPT ![r.w] = "acked"]
               /\ acked' = acked \cup {r.w}
          ELSE UNCHANGED <<phase, acked>>
  /\ UNCHANGED <<wal, durable, crashes, iseen, xcur, xseen>>

\* The internal reader reads positions (cursor, H] of the visible view and
\* commits its new cursor H in the same database. It waits for its last
\* cursor record to be published before reading again.
ReadInternal ==
  LET c == CursorIn(visible)
      h == HeadIn(visible)
  IN /\ h > c
     /\ \A k \in (visible + 1)..Len(wal) : wal[k].kind # "cursor"
     /\ iseen' = iseen \cup {<<r.w, r.i>> : r \in {x \in RowsIn(visible) : c < x.pos /\ x.pos <= h}}
     /\ wal' = Append(wal, [kind |-> "cursor", w |-> Reader, rows |-> {}, head |-> 0, value |-> h])
     /\ UNCHANGED <<durable, visible, phase, acked, crashes, xcur, xseen>>

\* The external reader reads positions (xcur, H] of the visible view,
\* records each position with the entry it held, and moves its cursor.
ReadExternal ==
  LET h == HeadIn(visible)
  IN /\ h > xcur
     /\ xseen' = xseen \cup {<<r.pos, <<r.w, r.i>>>> : r \in {x \in RowsIn(visible) : xcur < x.pos /\ x.pos <= h}}
     /\ xcur' = h
     /\ UNCHANGED <<wal, durable, visible, phase, acked, crashes, iseen>>

\* A power cut. It keeps a gap-free prefix of the records holding every
\* durable one, and recovery publishes all of it. A writer whose record was
\* dropped lost its commit (acknowledged or not); one whose unpublished
\* record survived is recovered without ever being told. The external
\* reader's state and the internal reader's handed entries are outside the
\* database and survive.
Crash ==
  /\ crashes < MaxCrashes
  /\ \E k \in durable..Len(wal) :
       /\ wal'     = SubSeq(wal, 1, k)
       /\ durable' = k
       /\ visible' = k
       /\ phase'   = [w \in Writers |->
                        IF phase[w] \in {"written", "acked"}
                          THEN IF \E j \in 1..k : wal[j].w = w
                                 THEN IF phase[w] = "written" THEN "recovered" ELSE "acked"
                                 ELSE "lost"
                          ELSE phase[w]]
  /\ crashes' = crashes + 1
  /\ UNCHANGED <<acked, iseen, xcur, xseen>>

\* Every step the system can take.
Next ==
  \/ \E w \in Writers : Commit(w)
  \/ Sync
  \/ Publish
  \/ ReadInternal
  \/ ReadExternal
  \/ Crash

\* Every behaviour: start in Init, then take Next steps or stutter.
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ durable \in 0..Len(wal)
  /\ visible \in 0..Len(wal)
  /\ phase \in [Writers -> {"idle", "written", "acked", "recovered", "lost"}]
  /\ acked \subseteq Writers
  /\ crashes \in 0..MaxCrashes
  /\ iseen \subseteq Writers \X (1..2)
  /\ xcur \in Nat

\* The visible view with head H holds rows at exactly positions 1..H, after
\* any crash too. Lean: dense_from_one and snapshot_sees_prefix.
INV_Dense == {r.pos : r \in RowsIn(visible)} = 1..HeadIn(visible)

\* No two rows anywhere in the log share a position. Lean: unique_positions.
INV_UniqueCursors == \A a, b \in RowsIn(Len(wal)) : a.pos = b.pos => a = b

\* No two rows anywhere in the log carry one once key. Lean: at_most_once.
INV_AtMostOnce ==
  \A a, b \in RowsIn(Len(wal)) : a.once # NoOnce /\ a.once = b.once => a = b

\* The internal reader, whose cursor commits in the same database, has been
\* handed every visible row at or below its cursor, across crashes.
INV_NoSkip ==
  \A r \in RowsIn(visible) : r.pos <= CursorIn(visible) => <<r.w, r.i>> \in iseen

\* Immediate: nothing is visible that is not durable.
INV_VisibleDurable == visible <= durable

\* Immediate: every commit that returned success is still in the visible
\* view, so the positions it was given still hold its entries.
INV_AckStable ==
  \A w \in acked : \E k \in 1..visible : wal[k].kind = "commit" /\ wal[k].w = w

\* A position the external reader recorded never holds another entry.
INV_ExternalStable ==
  \A pr \in xseen : \A r \in RowsIn(visible) : r.pos = pr[1] => <<r.w, r.i>> = pr[2]

====
