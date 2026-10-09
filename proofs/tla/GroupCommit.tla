---- MODULE GroupCommit ----
\* E10: group commit for optimistic transactions (plan 4.4). Queued
\* transactions share one WAL append and at most one fsync, and the group
\* decides, numbers and publishes them exactly as if they had committed one
\* at a time in queue order.
\*
\* PROVED FOR EVERY SIZE in Lean:
\*   Regolith/GroupCommit.lean
\*     group_eq_serial              validating each member against the
\*                                  view plus the keys written by members
\*                                  accepted earlier in the group decides
\*                                  every member as committing them one at
\*                                  a time does (SerialEquivalent here)
\*     early_check_split            validating up to h outside the mutex
\*                                  and above h under it decides as one
\*                                  check of every version (Submit and
\*                                  Decide here)
\*     view_only_breaks_serial      the RED case, as a counterexample
\*   Regolith/Pipeline.lean
\*     seqs_dense                   within a group, accepted members take
\*                                  consecutive sequences in decision
\*                                  order and aborted members take none
\*                                  (SeqFollowsDecisionOrder checks the
\*                                  order). A failed group's sequences are
\*                                  drawn and never used, as today, so
\*                                  across a failure they are not dense.
\* TLC checks the concurrent protocol here: every interleaving of begins,
\* early validation, ring pushes, the leader's steps and failed groups.
\* Tickets and visibility after durability are checked by TLC only; they
\* are properties of interleavings, not laws over sizes.
\*
\* THE ENGINE TODAY.
\*   RegolithEngine::submit, lead_with, drain_locked   src/engine/commit/mod.rs
\*     A writer pushes a ticket into the commit ring. Whoever holds the
\*     pipeline mutex is the leader: it drains the ring into one group.
\*   admit_from_ring
\*     Admits tickets in ring order up to MAX_GROUP_BYTES.
\*   run_group
\*     Draws the group's sequences with one fetch_add on latest_seq, in
\*     group order; appends every record with one write; fsyncs once if any
\*     member asked for Immediate; applies to the memtable; publishes
\*     visible_seq; all under the pipeline mutex.
\*   run_and_complete, WriteSlot::complete
\*     Completes every member's ticket once, with the same outcome on a
\*     failed group (G2).
\*   commit_locked
\*     Today an optimistic transaction is a group of one, validated under
\*     the mutex against the view (E10, the defect this design removes).
\*
\* THE DESIGN (4.4).
\*   Validation outside the mutex. A transaction samples the horizon h
\*   before it queues and validates the versions in (snapshot, h] there.
\*   In-group validation. Under the mutex the leader validates each member
\*   in queue order against the versions in (h, view] plus the keys written
\*   by members it accepted earlier in this group. A member that conflicts
\*   with an earlier one aborts exactly as if they had committed one after
\*   the other.
\*   One append and at most one fsync per group, then apply, then publish,
\*   then every ticket completes once.
\*
\* CHOICES WHERE THE PLAN IS SILENT.
\*   - A failed group (G2) fails every member, the ones the leader decided
\*     to abort included: the comparison is a one-at-a-time run under the
\*     same persistent fault, in which every member fails too.
\*   - The early check and the ring push are one step: the early check reads
\*     only versions at or below h, which no later step changes.
\*   - Groups do not overlap: a leader takes the next group only after the
\*     previous one completed. This is today's pipeline mutex; overlapping
\*     groups are CommitPipeline.tla.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - A batch takes one sequence per operation; here a commit takes one.
\*     Every operation of a commit sorts above every earlier commit and
\*     below every later one, which is all validation and publication read.
\*   - Identical-write elision, merges and exempt keys refine the conflict
\*     test per key (RepeatableRead.tla); the group protocol around the
\*     test is the same whatever the test says.
\*   - Plain writes in a group carry no validation and behave as accepted
\*     members.
\*   - The bounded leader (E21) changes who leads, not what a group does.
\*   - An ingest's pending slot is IngestPublication.tla and
\*     CommitPipeline.tla.
\*
\* CONFIGURATIONS.
\*   MC_GroupCommit_Green                  Mutant = "none", Faults = TRUE
\*     Every invariant and AllTicketsComplete hold.
\*   MC_GroupCommit_Red_ViewOnly           Mutant = "ViewOnly"
\*     SerialEquivalent fails: a member validated against the view alone
\*     commits over an earlier member's write to the same key.
\*   MC_GroupCommit_Red_PublishBeforeSync  Mutant = "PublishBeforeSync"
\*     DurableBeforeVisible fails: an Immediate commit is visible before
\*     its fsync.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Txns,       \* the transactions: a finite set of naturals, one commit each
  Keys,       \* the keys: a finite set of naturals
  Reads,      \* [Txns -> SUBSET Keys]: the keys each transaction read
  Writes,     \* [Txns -> SUBSET Keys]: the keys each transaction writes
  Immediate,  \* the transactions that commit at Immediate durability; the
              \* others commit at Eventual
  MaxGroup,   \* the most members one group admits (MAX_GROUP_BYTES)
  Faults,     \* TRUE: a group's WAL append or fsync may fail (G2)
  Mutant      \* "none", "ViewOnly" or "PublishBeforeSync"

ASSUME Txns \subseteq Nat /\ Keys \subseteq Nat
ASSUME Reads \in [Txns -> SUBSET Keys] /\ Writes \in [Txns -> SUBSET Keys]
\* Every transaction writes something: a read-only commit takes no sequence
\* and never enters a group.
ASSUME \A t \in Txns : Writes[t] # {}
ASSUME Immediate \subseteq Txns
ASSUME MaxGroup \in Nat \ {0}
ASSUME Faults \in BOOLEAN
ASSUME Mutant \in {"none", "ViewOnly", "PublishBeforeSync"}

VARIABLES
  pc,           \* [Txns -> phase]: "idle", "begun", "queued", "grouped", "done"
  snap,         \* [Txns -> Nat]: the visible sequence the transaction began at
  hor,          \* [Txns -> Nat]: the horizon h it validated up to outside the mutex
  queue,        \* the commit ring: queued transactions in arrival order
  group,        \* the leader's group in ring order; empty when no group runs
  gi,           \* the position in group of the next member to decide
  gview,        \* the visible sequence when the leader took the group
  gacc,         \* the keys written by members accepted earlier in this group
  gwal,         \* the WAL end before this group's append, for the rollback
  stage,        \* the leader's stage: "idle", "deciding", "written",
                \* "applied" or "published"
  synced,       \* this group's fsync has run
  dec,          \* [Txns -> {"none", "accept", "conflict"}]: the validation verdict
  seq,          \* [Txns -> Nat]: an accepted member's sequence, 0 otherwise
  pos,          \* [Txns -> Nat]: the place of the verdict in decision order, 0 before
  npos,         \* how many verdicts have been given
  outcome,      \* [Txns -> {"none", "commit", "conflict", "failed"}]: the ticket's result
  completions,  \* [Txns -> Nat]: how many times the ticket completed
  lastSeq,      \* latest_seq: the last sequence drawn
  walEnd,       \* the last sequence whose record is in the WAL
  durable,      \* the last sequence whose record an fsync made durable
  store,        \* the applied versions <<key, sequence>> (the memtable)
  visible       \* visible_seq: the horizon a new snapshot reads at

\* Every variable, so a step that changes none of them is a stutter.
vars == <<pc, snap, hor, queue, group, gi, gview, gacc, gwal, stage, synced,
          dec, seq, pos, npos, outcome, completions, lastSeq, walEnd,
          durable, store, visible>>

----------------------------------------------------------------------------
\* Helpers.

\* The greatest element of a finite, nonempty set of naturals.
Max(S) == CHOOSE m \in S : \A n \in S : n <= m

\* The smaller of two naturals.
Min2(a, b) == IF a <= b THEN a ELSE b

\* The keys whose newer versions abort t: those it read and those it writes.
Touched(t) == Reads[t] \cup Writes[t]

\* The store holds a version of a key t touched with a sequence in (lo, hi]:
\* a write t's snapshot did not see, within the window being checked.
NewerIn(t, lo, hi) == \E v \in store : lo < v[2] /\ v[2] <= hi /\ v[1] \in Touched(t)

\* The members of the running group, as a set.
Members == {group[i] : i \in 1..Len(group)}

\* The members the leader accepted so far.
Accepted == {m \in Members : dec[m] = "accept"}

\* The group needs its fsync: some accepted member asked for Immediate.
NeedsSync == Accepted \cap Immediate # {}

\* The versions transaction t writes, at its sequence.
VersionsOf(t) == {<<k, seq[t]>> : k \in Writes[t]}

\* Transaction t was accepted and its group did not fail: it has committed
\* or is committing.
Lands(t) == dec[t] = "accept" /\ outcome[t] # "failed"

----------------------------------------------------------------------------
\* Actions.

\* The start: nothing begun, queued, decided or written.
Init ==
  /\ pc          = [t \in Txns |-> "idle"]
  /\ snap        = [t \in Txns |-> 0]
  /\ hor         = [t \in Txns |-> 0]
  /\ queue       = <<>>
  /\ group       = <<>>
  /\ gi          = 1
  /\ gview       = 0
  /\ gacc        = {}
  /\ gwal        = 0
  /\ stage       = "idle"
  /\ synced      = FALSE
  /\ dec         = [t \in Txns |-> "none"]
  /\ seq         = [t \in Txns |-> 0]
  /\ pos         = [t \in Txns |-> 0]
  /\ npos        = 0
  /\ outcome     = [t \in Txns |-> "none"]
  /\ completions = [t \in Txns |-> 0]
  /\ lastSeq     = 0
  /\ walEnd      = 0
  /\ durable     = 0
  /\ store       = {}
  /\ visible     = 0

\* Transaction t begins: its snapshot is the visible sequence. Its reads
\* are snapshot reads, answered as of this moment whenever they are issued.
Begin(t) ==
  /\ pc[t] = "idle"
  /\ pc'   = [pc EXCEPT ![t] = "begun"]
  /\ snap' = [snap EXCEPT ![t] = visible]
  /\ UNCHANGED <<hor, queue, group, gi, gview, gacc, gwal, stage, synced, dec,
                 seq, pos, npos, outcome, completions, lastSeq, walEnd,
                 durable, store, visible>>

\* Transaction t commits: outside the mutex it samples h, the visible
\* sequence, and validates the versions in (snapshot, h]. A conflict there
\* aborts it at once and its ticket completes; otherwise it joins the ring.
Submit(t) ==
  LET h == visible
  IN /\ pc[t] = "begun"
     /\ hor' = [hor EXCEPT ![t] = h]
     /\ IF NewerIn(t, snap[t], h)
          THEN \* The early abort: a verdict, in decision order, and a
               \* completed ticket. Nothing enters the ring.
               /\ pc'          = [pc EXCEPT ![t] = "done"]
               /\ dec'         = [dec EXCEPT ![t] = "conflict"]
               /\ outcome'     = [outcome EXCEPT ![t] = "conflict"]
               /\ completions' = [completions EXCEPT ![t] = @ + 1]
               /\ pos'         = [pos EXCEPT ![t] = npos + 1]
               /\ npos'        = npos + 1
               /\ UNCHANGED queue
          ELSE \* No conflict up to h: the ticket is pushed to the ring.
               /\ pc'    = [pc EXCEPT ![t] = "queued"]
               /\ queue' = Append(queue, t)
               /\ UNCHANGED <<dec, outcome, completions, pos, npos>>
     /\ UNCHANGED <<snap, group, gi, gview, gacc, gwal, stage, synced, seq,
                    lastSeq, walEnd, durable, store, visible>>

\* A thread takes the pipeline mutex with no group running and admits the
\* first k queued tickets, k up to the cap: as many as arrived before it
\* drained the ring. It records the view it will validate against.
Lead(k) ==
  /\ stage = "idle"
  /\ k \in 1..Min2(MaxGroup, Len(queue))
  /\ group'  = SubSeq(queue, 1, k)
  /\ queue'  = SubSeq(queue, k + 1, Len(queue))
  /\ pc'     = [t \in Txns |-> IF \E i \in 1..k : queue[i] = t THEN "grouped" ELSE pc[t]]
  /\ gi'     = 1
  /\ gview'  = visible
  /\ gacc'   = {}
  /\ gwal'   = walEnd
  /\ stage'  = "deciding"
  /\ synced' = FALSE
  /\ UNCHANGED <<snap, hor, dec, seq, pos, npos, outcome, completions, lastSeq,
                 walEnd, durable, store, visible>>

\* The leader decides the next member t in queue order. It conflicts if the
\* view holds a newer version of a key it touched that the early check did
\* not cover, (h, view], or if a member accepted earlier in this group
\* writes a key it touched. Mutant ViewOnly skips the second test. An
\* accepted member draws the next sequence now, so sequences follow the
\* decision order; a conflicting one draws none.
Decide ==
  LET t        == group[gi]
      inGroup  == Mutant # "ViewOnly" /\ Touched(t) \cap gacc # {}
      conflict == NewerIn(t, hor[t], gview) \/ inGroup
  IN /\ stage = "deciding"
     /\ gi <= Len(group)
     /\ dec'     = [dec EXCEPT ![t] = IF conflict THEN "conflict" ELSE "accept"]
     /\ seq'     = IF conflict THEN seq ELSE [seq EXCEPT ![t] = lastSeq + 1]
     /\ lastSeq' = IF conflict THEN lastSeq ELSE lastSeq + 1
     /\ gacc'    = IF conflict THEN gacc ELSE gacc \cup Writes[t]
     /\ pos'     = [pos EXCEPT ![t] = npos + 1]
     /\ npos'    = npos + 1
     /\ gi'      = gi + 1
     /\ UNCHANGED <<pc, snap, hor, queue, group, gview, gwal, stage, synced,
                    outcome, completions, walEnd, durable, store, visible>>

\* Every member decided: the accepted members' records go to the WAL in one
\* append. A group with no accepted member writes nothing.
Write ==
  /\ stage = "deciding"
  /\ gi > Len(group)
  /\ walEnd' = IF Accepted = {} THEN walEnd ELSE lastSeq
  /\ stage'  = "written"
  /\ UNCHANGED <<pc, snap, hor, queue, group, gi, gview, gacc, gwal, synced,
                 dec, seq, pos, npos, outcome, completions, lastSeq, durable,
                 store, visible>>

\* One fsync for the whole group, when some accepted member asked for
\* Immediate. It makes every record written so far durable.
Sync ==
  /\ stage \in {"written", "applied", "published"}
  /\ ~synced
  /\ NeedsSync
  /\ durable' = walEnd
  /\ synced'  = TRUE
  /\ UNCHANGED <<pc, snap, hor, queue, group, gi, gview, gacc, gwal, stage,
                 dec, seq, pos, npos, outcome, completions, lastSeq, walEnd,
                 store, visible>>

\* The accepted members' versions go into the memtable, after the fsync
\* when the group needs one. Mutant PublishBeforeSync applies (and so
\* publishes) without waiting for it.
Apply ==
  /\ stage = "written"
  /\ synced \/ ~NeedsSync \/ Mutant = "PublishBeforeSync"
  /\ store' = store \cup UNION {VersionsOf(m) : m \in Accepted}
  /\ stage' = "applied"
  /\ UNCHANGED <<pc, snap, hor, queue, group, gi, gview, gacc, gwal, synced,
                 dec, seq, pos, npos, outcome, completions, lastSeq, walEnd,
                 durable, visible>>

\* visible_seq moves to the group's last sequence: the whole group becomes
\* visible at once.
Publish ==
  /\ stage = "applied"
  /\ visible' = IF Accepted = {} THEN visible ELSE lastSeq
  /\ stage'   = "published"
  /\ UNCHANGED <<pc, snap, hor, queue, group, gi, gview, gacc, gwal, synced,
                 dec, seq, pos, npos, outcome, completions, lastSeq, walEnd,
                 durable, store>>

\* Every member's ticket completes once, with its own verdict, and the
\* mutex is released.
Complete ==
  /\ stage = "published"
  /\ synced \/ ~NeedsSync
  /\ pc'          = [t \in Txns |-> IF t \in Members THEN "done" ELSE pc[t]]
  /\ outcome'     = [t \in Txns |-> IF t \in Members
                                      THEN (IF dec[t] = "accept" THEN "commit" ELSE "conflict")
                                      ELSE outcome[t]]
  /\ completions' = [t \in Txns |-> IF t \in Members THEN completions[t] + 1 ELSE completions[t]]
  /\ group'       = <<>>
  /\ stage'       = "idle"
  /\ UNCHANGED <<snap, hor, queue, gi, gview, gacc, gwal, synced, dec, seq,
                 pos, npos, lastSeq, walEnd, durable, store, visible>>

\* G2: the group's append or fsync fails. The WAL is truncated to where the
\* group began, nothing is applied or published, and every member's ticket
\* completes once with the failure. The drawn sequences are never used.
Fail ==
  /\ Faults
  /\ stage = "written"
  /\ ~synced
  /\ Accepted # {}
  /\ walEnd'      = gwal
  /\ pc'          = [t \in Txns |-> IF t \in Members THEN "done" ELSE pc[t]]
  /\ outcome'     = [t \in Txns |-> IF t \in Members THEN "failed" ELSE outcome[t]]
  /\ completions' = [t \in Txns |-> IF t \in Members THEN completions[t] + 1 ELSE completions[t]]
  /\ group'       = <<>>
  /\ stage'       = "idle"
  /\ UNCHANGED <<snap, hor, queue, gi, gview, gacc, gwal, synced, dec, seq,
                 pos, npos, lastSeq, durable, store, visible>>

\* Every step the system can take.
Next ==
  \/ \E t \in Txns : Begin(t) \/ Submit(t)
  \/ \E k \in 1..MaxGroup : Lead(k)
  \/ Decide \/ Write \/ Sync \/ Apply \/ Publish \/ Complete \/ Fail

\* Every behaviour: start in Init, take Next steps, and never stop while a
\* step is possible.
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ pc \in [Txns -> {"idle", "begun", "queued", "grouped", "done"}]
  /\ snap \in [Txns -> 0..lastSeq]
  /\ hor \in [Txns -> 0..lastSeq]
  /\ dec \in [Txns -> {"none", "accept", "conflict"}]
  /\ seq \in [Txns -> 0..lastSeq]
  /\ outcome \in [Txns -> {"none", "commit", "conflict", "failed"}]
  /\ stage \in {"idle", "deciding", "written", "applied", "published"}
  /\ store \subseteq Keys \X (1..lastSeq)
  /\ durable <= walEnd /\ walEnd <= lastSeq /\ visible <= lastSeq

\* What committing one at a time in decision order decides for t: it
\* aborts exactly when a transaction that landed before it in that order
\* wrote a key t touched at a sequence t's snapshot does not see.
SerialVerdict(t) ==
  IF \E j \in Txns :
       /\ Lands(j)
       /\ pos[j] < pos[t]
       /\ seq[j] > snap[t]
       /\ Writes[j] \cap Touched(t) # {}
  THEN "conflict" ELSE "commit"

\* THE HEADLINE. Every ticket that reported commit or conflict reported
\* what committing the transactions one at a time, in decision order, would
\* have decided. Lean: group_eq_serial.
SerialEquivalent ==
  \A t \in Txns : outcome[t] \in {"commit", "conflict"} => outcome[t] = SerialVerdict(t)

\* Sequences follow the decision order: of two landed transactions, the one
\* decided first has the smaller sequence. Lean: seqs_dense.
SeqFollowsDecisionOrder ==
  \A i, j \in Txns : Lands(i) /\ Lands(j) /\ pos[i] < pos[j] => seq[i] < seq[j]

\* The memtable holds exactly the versions of the transactions that landed
\* and were applied: nothing from an aborted member or a failed group (G2).
StoreHoldsCommits ==
  LET applied == {t \in Txns : Lands(t) /\
                     (outcome[t] = "commit" \/ (t \in Members /\ stage \in {"applied", "published"}))}
  IN store = UNION {VersionsOf(t) : t \in applied}

\* No torn group: every landed transaction at or below the horizon is in the
\* memtable, so a snapshot sees a group whole or not at all.
VisibleIsApplied ==
  \A t \in Txns : Lands(t) /\ seq[t] <= visible => VersionsOf(t) \subseteq store

\* At Immediate a commit is visible only once it is durable, so no reader
\* sees a commit a crash could lose.
DurableBeforeVisible ==
  \A t \in Immediate : Lands(t) /\ seq[t] <= visible => seq[t] <= durable

\* A ticket completes at most once, and a done transaction's ticket has
\* completed exactly once.
TicketsCompleteOnce ==
  \A t \in Txns : completions[t] <= 1 /\ (pc[t] = "done" <=> completions[t] = 1)

\* A ticket that reports commit is telling the truth: the commit is visible,
\* and durable when it asked for Immediate.
TicketMeansVisible ==
  \A t \in Txns : outcome[t] = "commit" =>
    /\ seq[t] <= visible
    /\ (t \in Immediate => seq[t] <= durable)

\* Nothing is stuck: when no step is possible, every ticket has completed.
NoStuckTicket == (~ENABLED Next) => \A t \in Txns : pc[t] = "done"

----------------------------------------------------------------------------
\* Liveness.

\* Every transaction's ticket eventually completes.
AllTicketsComplete == <>(\A t \in Txns : pc[t] = "done")

----------------------------------------------------------------------------
\* Workloads, chosen by the configurations.

\* Transactions 1 and 2 write key 1, so whichever is decided second
\* conflicts unless its snapshot sees the first. Transaction 3 reads key 1
\* and writes key 2, so it conflicts with a write of key 1 its snapshot
\* missed. Transaction 4, when present, writes key 2 blind and races 3.
ReadsW == [t \in Txns |-> IF t = 3 THEN {1} ELSE {}]
WritesW == [t \in Txns |-> IF t \in {3, 4} THEN {2} ELSE {1}]

====
