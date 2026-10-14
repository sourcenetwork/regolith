---- MODULE CfRegistry ----
\* ===========================================================================
\* THE STORY
\* ===========================================================================
\* A column family is a named keyspace inside one database: its keys carry
\* the family's id in front. Creating a family writes its name to the
\* database's own metadata; dropping it writes one range tombstone over every
\* key with its id (deleting them all at once) and removes the name. The
\* registry in memory (CfRegistry, src/column_family.rs) says which ids are
\* live, and every write to a family checks it.
\*
\* Every write takes a sequence number, in order, in the "ordered step" of
\* the commit pipeline (one thread at a time holds it). A tombstone at
\* sequence 7 deletes every key of the family written at sequences below 7.
\*
\* Tiny example. Writer W checks "family 5 is live" and goes to commit. A
\* drop of family 5 commits first, at sequence 7. If W's write now takes
\* sequence 8, it lands ABOVE the tombstone: it is visible, in a family no
\* handle can name any more, and no later compaction removes it. W was told
\* "ok" for bytes nobody can ever read.
\*
\* The fix (src/engine/commit/families.rs): a write is checked against the
\* registry IN the ordered step, just before it takes its sequence, and a
\* drop retires the family IN the ordered step, right after its tombstone's
\* group committed. So a write either takes a sequence below the tombstone
\* (and the tombstone deletes it) or finds the family gone and is refused.
\*
\* GROUP COMMIT (src/engine/commit/mod.rs). Writes do not take the ordered
\* step one by one. A writer that finds the pipeline free leads a group: its
\* own request first (lead_with), then the ticket a previous leader handed
\* the pipeline to, if any, then tickets other writers queued on the ring
\* (admit_from_ring). A writer that finds the pipeline taken queues its
\* ticket on the ring and waits; any thread that gets the pipeline later may
\* run it. At the end of a turn the leader takes the ticket at the head of
\* the ring out and holds it for the next group (the bounded hand-off, E21):
\* that ticket waits ACROSS the end of one turn and the start of the next,
\* and a drop can run its own group in between. A transaction commits as a
\* member of a group like any write, and an ingest installs its table in the
\* ordered step on its own. So the real rule is: every member is checked
\* when the group it is in RUNS (fence_group, the first thing
\* run_and_complete does, before any sequence), whatever path put it there;
\* and an ingest is checked at its install.
\*
\* Two wrong places for the check, and their stories:
\*   - checked when the hand-off took the ticket, not again when its group
\*     runs: W is queued; a leader hands the pipeline to W's ticket (family
\*     live, W passes); the drop runs its group (tombstone 7) and retires
\*     the family; W's group runs and W lands at 8, over the tombstone;
\*   - a transaction member skips the check: W's transaction queues; the
\*     drop runs; W's group runs and W lands over the tombstone.
\*
\* What can go wrong, and what this model checks cannot happen:
\*   - a write lands after its family's tombstone (NoWriteAfterDrop);
\*   - a write lands before its family was created (NoWriteBeforeBirth);
\*   - a reader sees a family go back: live after dead, or unborn after
\*     live (LifeInOrder). Ids are never reused, which is what keeps this.
\*
\* WHAT IS MODELLED, and the code each piece mirrors:
\*   life      a family id's stage: CfRegistry::by_id holds the id while
\*             it is live; "unborn" before CfRegistry::publish, "dead"
\*             after CfRegistry::retire
\*   seq       the commit pipeline's sequence counter (latest_seq)
\*   born,tomb the sequence of the create's meta write and of the drop's
\*             range tombstone
\*   landed    every committed write, as <<family, sequence>>
\*   wpc       each writer's progress
\*   ring      the commit ring (commit_ring, an ArrayQueue of tickets)
\*   held      the ticket the hand-off holds for the next group
\*             (Pipeline::held), 0 for none
\*   heldPassed only the FenceAtHandOff bug: the held ticket was checked
\*             when the hand-off took it
\*   seenLife  each reader's observations of one family, in order
\*
\* WHAT IS LEFT OUT, and why that loses nothing:
\*   - The pipeline mutex itself: each step below that the code runs under
\*     it (a whole group, a create, a drop, an ingest install, a hand-off)
\*     is one atomic step, which is exactly what holding the mutex gives.
\*   - The name map: a name finds an id, but liveness is the id alone.
\*   - The appends a transaction numbers: they write the default family,
\*     which is never dropped.
\*   - Group size limits: a leader admits any number of queued tickets,
\*     from none to all, which covers every limit.
\*
\* CONFIGURATIONS (each GREEN must pass, each RED must break the one
\* invariant it names):
\*   MC_CfRegistry_Green              a plain writer, a transaction and an
\*                                    ingest on one family that is created
\*                                    and dropped, every group-commit path
\*                                    open, a reader watching.
\*   MC_CfRegistry_Red_FenceOutside   the family is checked only at the API
\*                                    boundary, not in the ordered step:
\*                                    NoWriteAfterDrop breaks.
\*   MC_CfRegistry_Red_RetireLate     the drop retires the family after the
\*                                    ordered step, so writes admitted in
\*                                    between land past the tombstone:
\*                                    NoWriteAfterDrop breaks.
\*   MC_CfRegistry_Red_ReuseId        a create may take a dropped family's
\*                                    id again: LifeInOrder breaks.
\*   MC_CfRegistry_Red_FenceAtHandOff the held ticket is checked when the
\*                                    hand-off takes it, not when its group
\*                                    runs: NoWriteAfterDrop breaks.
\*   MC_CfRegistry_Red_TxnUnfenced    a transaction member is not checked:
\*                                    NoWriteAfterDrop breaks.
\*
\* Lean, proofs/lean/Regolith/CfRegistry.lean, proves the same rules for
\* every number of families, writers, group members and steps.

\* We use numbers, sequences and finite sets.
EXTENDS Naturals, Sequences, FiniteSets

\* The fixed inputs of a configuration.
CONSTANTS
  \* The family ids.
  Families,
  \* The writers, numbered from 1 (0 means "nobody").
  Writers,
  \* [Writers -> Families]: the family each writer writes to.
  WriteTo,
  \* [Writers -> {"plain", "txn", "ingest"}]: how each writer writes: a
  \* plain write or batch, an optimistic transaction's commit, or an ingest.
  Kind,
  \* The readers that watch a family's life.
  Readers,
  \* [Readers -> Families]: the family each reader watches.
  Watch,
  \* How many observations a reader makes.
  Looks,
  \* "none" for the real code, or the name of one planted bug.
  Mutant

\* Every writer writes to one family.
ASSUME WriteTo \in [Writers -> Families]
\* Every writer writes one way.
ASSUME Kind \in [Writers -> {"plain", "txn", "ingest"}]
\* Writers are numbered from 1, so 0 can mean "nobody".
ASSUME Writers \subseteq Nat \ {0}
\* Every reader watches one family.
ASSUME Watch \in [Readers -> Families]
\* The bug names this model knows.
ASSUME Mutant \in {"none", "FenceOutside", "RetireLate", "ReuseId",
                   "FenceAtHandOff", "TxnUnfenced"}

\* For the configurations: every writer and reader is on family 1.
OnFamilyOne(S) == [x \in S |-> 1]
\* Writers 1, 2 and 3 all write to family 1.
WriteToThree == OnFamilyOne({1, 2, 3})
\* Writers 1 and 2 both write to family 1.
WriteToOne == OnFamilyOne({1, 2})
\* Writer 1 alone writes to family 1.
WriteToSolo == OnFamilyOne({1})
\* Reader 1 watches family 1.
WatchOne == OnFamilyOne({1})
\* No writer at all.
NoWrites == OnFamilyOne({})
\* Writer 1 writes plainly, writer 2 commits a transaction, writer 3 ingests.
KindsMixed == [w \in {1, 2, 3} |-> IF w = 1 THEN "plain" ELSE IF w = 2 THEN "txn" ELSE "ingest"]
\* Writers 1 and 2 both write plainly.
KindsPlain == [w \in {1, 2} |-> "plain"]
\* Writer 1 commits a transaction.
KindsTxn == [w \in {1} |-> "txn"]
\* No writer, so no kinds.
NoKinds == [w \in {} |-> "plain"]

\* A family's stages, in the only order the code moves them.
Rank(stage) ==
  \* Unborn comes first ...
  CASE stage = "unborn" -> 0
  \* ... then live ...
  []   stage = "live"   -> 1
  \* ... then dead, for good.
  []   stage = "dead"   -> 2

\* The state that changes from step to step.
VARIABLES
  \* [Families -> {"unborn","live","dead"}]: what the registry says.
  life,
  \* The last sequence number handed out.
  seq,
  \* [Families -> Nat]: the sequence of the create (0: not created).
  born,
  \* [Families -> Nat]: the sequence of the drop's tombstone (0: none).
  tomb,
  \* [Families -> BOOLEAN]: bug RetireLate only: the tombstone committed
  \* and the retire has not happened yet.
  retiring,
  \* The committed writes, as <<family, sequence>>.
  landed,
  \* [Writers -> {"start","checked","queued","done","refused"}]: each
  \* writer's step. "queued" covers a ticket on the ring and the held one.
  wpc,
  \* The commit ring: the queued tickets, oldest first.
  ring,
  \* The ticket the hand-off holds for the next group, 0 for none.
  held,
  \* Bug FenceAtHandOff only: the held ticket passed a check at hand-off.
  heldPassed,
  \* [Readers -> Seq(stage)]: what each reader saw, in order.
  seenLife

\* All the variables, for "nothing else changes".
vars == <<life, seq, born, tomb, retiring, landed, wpc, ring, held, heldPassed, seenLife>>

\* Every variable holds the kind of value it should.
TypeOK ==
  \* Each family is in one stage.
  /\ life \in [Families -> {"unborn", "live", "dead"}]
  \* The sequence counter is a number.
  /\ seq \in Nat
  \* Births and tombstones are sequence numbers or 0.
  /\ born \in [Families -> Nat]
  /\ tomb \in [Families -> Nat]
  \* The late-retire flag is a yes or a no per family.
  /\ retiring \in [Families -> BOOLEAN]
  \* Landed writes are (family, sequence) pairs.
  /\ landed \subseteq (Families \X Nat)
  \* Each writer is at one of its steps.
  /\ wpc \in [Writers -> {"start", "checked", "queued", "done", "refused"}]
  \* The ring holds writers.
  /\ ring \in Seq(Writers)
  \* The held ticket is a writer or nobody.
  /\ held \in Writers \cup {0}
  \* The bug's mark is a yes or a no.
  /\ heldPassed \in BOOLEAN

\* The start: no family created, nothing written, nothing queued or seen.
Init ==
  \* Every family id is unborn.
  /\ life = [f \in Families |-> "unborn"]
  \* No sequence handed out yet.
  /\ seq = 0
  \* No create, no tombstone.
  /\ born = [f \in Families |-> 0]
  /\ tomb = [f \in Families |-> 0]
  \* Nothing is waiting to be retired.
  /\ retiring = [f \in Families |-> FALSE]
  \* Nothing has been written.
  /\ landed = {}
  \* Every writer is about to write.
  /\ wpc = [w \in Writers |-> "start"]
  \* The ring is empty ...
  /\ ring = <<>>
  \* ... and the hand-off holds nobody.
  /\ held = 0
  /\ heldPassed = FALSE
  \* No reader has looked yet.
  /\ seenLife = [r \in Readers |-> <<>>]

\* The writers a sequence holds, as a set.
Members(s) == {s[i] : i \in 1..Len(s)}

\* Create family f: in the ordered step, its meta write takes the next
\* sequence and the registry publishes the id (RegolithEngine::create_family,
\* a group of its own). The bug ReuseId may also create an id that was dropped.
Create(f) ==
  \* The id is new, or (bug) dead and taken again.
  /\ \/ life[f] = "unborn"
     \/ Mutant = "ReuseId" /\ life[f] = "dead"
  \* The meta write takes the next sequence.
  /\ seq' = seq + 1
  \* That is the family's birth.
  /\ born' = [born EXCEPT ![f] = seq + 1]
  \* The registry now holds the id: the family is live.
  /\ life' = [life EXCEPT ![f] = "live"]
  \* A reused id starts with no tombstone.
  /\ tomb' = [tomb EXCEPT ![f] = 0]
  \* Nothing else changes.
  /\ UNCHANGED <<retiring, landed, wpc, ring, held, heldPassed, seenLife>>

\* Drop family f: in the ordered step, the tombstone's group of one takes the
\* next sequence; then, still in the ordered step, the registry retires the
\* id (RegolithEngine::drop_family_locked). The queued and held tickets stay
\* where they are: the drop's group admits none of them. The bug RetireLate
\* leaves the retire for a later step of its own.
Drop(f) ==
  \* Only a live family is dropped (a stale handle is refused).
  /\ life[f] = "live"
  \* Not already mid-drop.
  /\ ~retiring[f]
  \* The tombstone takes the next sequence.
  /\ seq' = seq + 1
  /\ tomb' = [tomb EXCEPT ![f] = seq + 1]
  \* The real code retires at once; the bug only marks it as pending.
  /\ IF Mutant = "RetireLate"
     THEN /\ retiring' = [retiring EXCEPT ![f] = TRUE]
          /\ UNCHANGED life
     ELSE /\ life' = [life EXCEPT ![f] = "dead"]
          /\ UNCHANGED retiring
  \* Nothing else changes.
  /\ UNCHANGED <<born, landed, wpc, ring, held, heldPassed, seenLife>>

\* Bug RetireLate: the retire, as a separate step after the ordered step.
RetireLater(f) ==
  \* The tombstone committed and the retire is pending.
  /\ retiring[f]
  \* Now the registry drops the id.
  /\ life' = [life EXCEPT ![f] = "dead"]
  /\ retiring' = [retiring EXCEPT ![f] = FALSE]
  \* Nothing else changes.
  /\ UNCHANGED <<seq, born, tomb, landed, wpc, ring, held, heldPassed, seenLife>>

\* Writer w's early check at the API boundary (Db::put_cf's
\* validate_cf_handle; an ingest's key validation): a family that is not
\* live is refused at once.
ApiCheck(w) ==
  \* The writer is about to write.
  /\ wpc[w] = "start"
  \* It passes if the family is live now, and is refused otherwise.
  /\ wpc' = [wpc EXCEPT ![w] = IF life[WriteTo[w]] = "live" THEN "checked" ELSE "refused"]
  \* Nothing else changes.
  /\ UNCHANGED <<life, seq, born, tomb, retiring, landed, ring, held, heldPassed, seenLife>>

\* Writer w finds the pipeline taken and queues its ticket on the ring
\* (commit_through_pipeline's push). An ingest never queues: it installs on
\* its own.
Queue(w) ==
  \* The writer passed the API check and writes through the pipeline.
  /\ wpc[w] = "checked"
  /\ Kind[w] # "ingest"
  \* Its ticket joins the end of the ring.
  /\ ring' = Append(ring, w)
  /\ wpc' = [wpc EXCEPT ![w] = "queued"]
  \* Nothing else changes.
  /\ UNCHANGED <<life, seq, born, tomb, retiring, landed, held, heldPassed, seenLife>>

\* Whether member m passes the check when its group runs. The real code
\* checks every member against the registry right now (fence_group). The
\* bugs: FenceOutside checks nobody; TxnUnfenced skips transactions;
\* FenceAtHandOff takes the held ticket's check at hand-off as its pass.
Passes(m) ==
  \* Bug FenceOutside: every member passes, whatever the family is now.
  CASE Mutant = "FenceOutside" -> TRUE
  \* Bug TxnUnfenced: a transaction member passes unchecked.
  []   Mutant = "TxnUnfenced" /\ Kind[m] = "txn" -> TRUE
  \* Bug FenceAtHandOff: the held ticket passed its check already.
  []   Mutant = "FenceAtHandOff" /\ m = held /\ heldPassed -> TRUE
  \* The real code: the family is live right now, in the ordered step.
  []   OTHER -> life[WriteTo[m]] = "live"

\* Run one group whose members are `group`, in that order, in the ordered
\* step (run_and_complete): every member is checked (Passes), and those that
\* pass take the next sequences in group order and land; the others are
\* refused and take none (fence_group turns them into requests that write
\* nothing).
RunGroup(group) ==
  \* The members that pass, in group order.
  LET passing == SelectSeq(group, Passes) IN
    \* They take the next sequences, one each, in order.
    /\ seq' = seq + Len(passing)
    \* Each lands in its family at its own sequence.
    /\ landed' = landed \cup {<<WriteTo[passing[i]], seq + i>> : i \in 1..Len(passing)}
    \* Every member learns its outcome: landed, or refused.
    /\ wpc' = [w \in Writers |->
                 IF w \in Members(passing) THEN "done"
                 ELSE IF w \in Members(group) THEN "refused"
                 ELSE wpc[w]]

\* The ticket the hand-off holds, as a sequence of zero or one member.
HeldSeq == IF held = 0 THEN <<>> ELSE <<held>>

\* Writer w finds the pipeline free and leads a group (lead_with): its own
\* request first, then the held ticket, then the first k tickets of the ring
\* (admit_from_ring). The held ticket is consumed.
Lead(w) ==
  \* The writer passed the API check and writes through the pipeline.
  /\ wpc[w] = "checked"
  /\ Kind[w] # "ingest"
  \* It admits some number of queued tickets, from none to all.
  /\ \E k \in 0..Len(ring) :
       \* The group: own request, held ticket, then the ring's first k.
       /\ RunGroup(<<w>> \o HeldSeq \o SubSeq(ring, 1, k))
       \* Those k leave the ring.
       /\ ring' = SubSeq(ring, k + 1, Len(ring))
  \* The held ticket is in this group now.
  /\ held' = 0
  /\ heldPassed' = FALSE
  \* Nothing else changes.
  /\ UNCHANGED <<life, born, tomb, retiring, seenLife>>

\* A thread with no request of its own leads a group (try_drain, lead_one):
\* the held ticket, then the first k tickets of the ring. A queued writer's
\* park loop does this, as does any writer that gets the pipeline first.
Drain ==
  \* It admits some number of queued tickets, from none to all ...
  /\ \E k \in 0..Len(ring) :
       \* ... and the group is not empty.
       /\ HeldSeq \o SubSeq(ring, 1, k) # <<>>
       \* The group: the held ticket, then the ring's first k.
       /\ RunGroup(HeldSeq \o SubSeq(ring, 1, k))
       \* Those k leave the ring.
       /\ ring' = SubSeq(ring, k + 1, Len(ring))
  \* The held ticket is in this group now.
  /\ held' = 0
  /\ heldPassed' = FALSE
  \* Nothing else changes.
  /\ UNCHANGED <<life, born, tomb, retiring, seenLife>>

\* The end of a leadership turn (hand_off, E21): the ticket at the head of
\* the ring is taken out and held for the next group, and its writer woken.
\* The real code checks nothing here. The bug FenceAtHandOff checks it now,
\* refusing it if its family is gone and marking it passed otherwise.
HandOff ==
  \* Nobody is held, and somebody is queued.
  /\ held = 0
  /\ ring # <<>>
  \* The head leaves the ring.
  /\ ring' = Tail(ring)
  /\ IF Mutant = "FenceAtHandOff" /\ life[WriteTo[Head(ring)]] # "live"
     \* The bug's check at hand-off refuses it.
     THEN /\ wpc' = [wpc EXCEPT ![Head(ring)] = "refused"]
          /\ UNCHANGED <<held, heldPassed>>
     \* Otherwise the head is held for the next group; the bug marks it
     \* as having passed its check.
     ELSE /\ held' = Head(ring)
          /\ heldPassed' = (Mutant = "FenceAtHandOff")
          /\ UNCHANGED wpc
  \* Nothing else changes.
  /\ UNCHANGED <<life, seq, born, tomb, retiring, landed, seenLife>>

\* Ingest w installs its table in the ordered step (ingest.rs install): the
\* families its table holds are checked (cf_fence_ids), then it takes one
\* sequence. The real code checks; FenceOutside does not.
Install(w) ==
  \* The ingest validated its table at the API boundary.
  /\ wpc[w] = "checked"
  /\ Kind[w] = "ingest"
  \* A group of one: the ingest's table.
  /\ RunGroup(<<w>>)
  \* Nothing else changes.
  /\ UNCHANGED <<life, born, tomb, retiring, ring, held, heldPassed, seenLife>>

\* Reader r looks at its family in the registry and notes what it saw.
Look(r) ==
  \* It has looks left.
  /\ Len(seenLife[r]) < Looks
  \* It notes the family's stage now.
  /\ seenLife' = [seenLife EXCEPT ![r] = Append(seenLife[r], life[Watch[r]])]
  \* Nothing else changes.
  /\ UNCHANGED <<life, seq, born, tomb, retiring, landed, wpc, ring, held, heldPassed>>

\* Every step anyone can take.
Next ==
  \* A create, a drop, or the bug's late retire.
  \/ \E f \in Families : Create(f) \/ Drop(f) \/ RetireLater(f)
  \* A writer checks, queues, leads, or installs.
  \/ \E w \in Writers : ApiCheck(w) \/ Queue(w) \/ Lead(w) \/ Install(w)
  \* A group with no request of its own, or a hand-off.
  \/ Drain
  \/ HandOff
  \* A reader looks.
  \/ \E r \in Readers : Look(r)

\* A bound on the run for TLC: the real code creates and drops an id once,
\* but the bug ReuseId could go on forever.
Bounded == seq <= 8

\* The behaviours: start in Init, take Next steps.
Spec == Init /\ [][Next]_vars

\* ===========================================================================
\* THE RULES
\* ===========================================================================

\* Every write that landed in a dropped family is below its tombstone, so
\* the tombstone deletes it. Rules out: W checked "live", the drop
\* committed at 7, W landed at 8, visible in a family nobody can read.
NoWriteAfterDrop ==
  \* Each landed write (family, sequence): its family has no tombstone, or the
  \* write's sequence is below the tombstone's.
  \A pair \in landed : tomb[pair[1]] = 0 \/ pair[2] < tomb[pair[1]]

\* Every write that landed is above its family's birth. Rules out: a write
\* to an id that was not created yet.
NoWriteBeforeBirth ==
  \* Each landed write: its family was created, at a sequence below the write.
  \A pair \in landed : born[pair[1]] # 0 /\ born[pair[1]] < pair[2]

\* What a reader saw never goes back: unborn, then live, then dead. Rules
\* out: a reader that saw a family dropped and then, through the same id,
\* saw it live again, with a new family's data.
LifeInOrder ==
  \* For every reader ...
  \A r \in Readers :
    \* ... and every look it made ...
    \A i \in 1..Len(seenLife[r]) :
      \* ... and every later look ...
      \A j \in i..Len(seenLife[r]) :
        \* ... the later look saw the same stage or a later one.
        Rank(seenLife[r][i]) <= Rank(seenLife[r][j])

====
