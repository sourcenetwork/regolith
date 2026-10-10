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
\*   wpc,wf    each writer's step and the family it writes
\*   seenLife  each reader's observations of one family, in order
\*
\* WHAT IS LEFT OUT, and why that loses nothing:
\*   - Group commit: a group is several requests admitted one by one in
\*     the ordered step; each admission is one Admit step here.
\*   - The name map: a name finds an id, but liveness is the id alone.
\*   - Ingest: an ingested table is fenced at its install exactly as a write
\*     is fenced at admission (one Admit).
\*
\* CONFIGURATIONS (each GREEN must pass, each RED must break the one
\* invariant it names):
\*   MC_CfRegistry_Green              two writers, a create and a drop of
\*                                    one family, a reader watching.
\*   MC_CfRegistry_Red_FenceOutside   the family is checked only at the API
\*                                    boundary, not in the ordered step:
\*                                    NoWriteAfterDrop breaks.
\*   MC_CfRegistry_Red_RetireLate     the drop retires the family after the
\*                                    ordered step, so writes admitted in
\*                                    between land past the tombstone:
\*                                    NoWriteAfterDrop breaks.
\*   MC_CfRegistry_Red_ReuseId        a create may take a dropped family's
\*                                    id again: LifeInOrder breaks.
\*
\* Lean, proofs/lean/Regolith/CfRegistry.lean, proves the same rules for
\* every number of families, writers and steps.

\* We use numbers and sequences.
EXTENDS Naturals, Sequences

\* The fixed inputs of a configuration.
CONSTANTS
  \* The family ids.
  Families,
  \* The writers.
  Writers,
  \* [Writers -> Families]: the family each writer writes to.
  WriteTo,
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
\* Every reader watches one family.
ASSUME Watch \in [Readers -> Families]
\* The bug names this model knows.
ASSUME Mutant \in {"none", "FenceOutside", "RetireLate", "ReuseId"}

\* For the configurations: every writer and reader is on family 1.
OnFamilyOne(S) == [x \in S |-> 1]
\* Writers 1 and 2 both write to family 1.
WriteToOne == OnFamilyOne({1, 2})
\* Reader 1 watches family 1.
WatchOne == OnFamilyOne({1})
\* No writer at all.
NoWrites == OnFamilyOne({})

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
  \* [Writers -> {"start","checked","done","refused"}]: each writer's step.
  wpc,
  \* [Readers -> Seq(stage)]: what each reader saw, in order.
  seenLife

\* All the variables, for "nothing else changes".
vars == <<life, seq, born, tomb, retiring, landed, wpc, seenLife>>

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
  /\ wpc \in [Writers -> {"start", "checked", "done", "refused"}]

\* The start: no family created, nothing written, nothing seen.
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
  \* No reader has looked yet.
  /\ seenLife = [r \in Readers |-> <<>>]

\* Create family f: in the ordered step, its meta write takes the next
\* sequence and the registry publishes the id (RegolithEngine::create_family).
\* The bug ReuseId may also create an id that was dropped.
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
  /\ UNCHANGED <<retiring, landed, wpc, seenLife>>

\* Drop family f: in the ordered step, the tombstone's group takes the next
\* sequence; then, still in the ordered step, the registry retires the id
\* (RegolithEngine::drop_family). The bug RetireLate leaves the retire for a
\* later step of its own.
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
  /\ UNCHANGED <<born, landed, wpc, seenLife>>

\* Bug RetireLate: the retire, as a separate step after the ordered step.
RetireLater(f) ==
  \* The tombstone committed and the retire is pending.
  /\ retiring[f]
  \* Now the registry drops the id.
  /\ life' = [life EXCEPT ![f] = "dead"]
  /\ retiring' = [retiring EXCEPT ![f] = FALSE]
  \* Nothing else changes.
  /\ UNCHANGED <<seq, born, tomb, landed, wpc, seenLife>>

\* Writer w's early check at the API boundary (Db::put_cf's
\* validate_cf_handle): a family that is not live is refused at once.
ApiCheck(w) ==
  \* The writer is about to write.
  /\ wpc[w] = "start"
  \* It passes if the family is live now, and is refused otherwise.
  /\ wpc' = [wpc EXCEPT ![w] = IF life[WriteTo[w]] = "live" THEN "checked" ELSE "refused"]
  \* Nothing else changes.
  /\ UNCHANGED <<life, seq, born, tomb, retiring, landed, seenLife>>

\* Writer w is admitted in the ordered step (cf_fence, then run_group's
\* sequence). The real code checks the family again here; the bug
\* FenceOutside trusts the API check.
Admit(w) ==
  \* The writer passed the API check.
  /\ wpc[w] = "checked"
  /\ LET f == WriteTo[w] IN
       \* Live now (or the bug does not look) ...
       IF life[f] = "live" \/ Mutant = "FenceOutside"
       \* ... so the write takes the next sequence and lands.
       THEN /\ seq' = seq + 1
            /\ landed' = landed \cup {<<f, seq + 1>>}
            /\ wpc' = [wpc EXCEPT ![w] = "done"]
       \* ... otherwise it is refused, with no sequence taken.
       ELSE /\ wpc' = [wpc EXCEPT ![w] = "refused"]
            /\ UNCHANGED <<seq, landed>>
  \* Nothing else changes.
  /\ UNCHANGED <<life, born, tomb, retiring, seenLife>>

\* Reader r looks at its family in the registry and notes what it saw.
Look(r) ==
  \* It has looks left.
  /\ Len(seenLife[r]) < Looks
  \* It notes the family's stage now.
  /\ seenLife' = [seenLife EXCEPT ![r] = Append(seenLife[r], life[Watch[r]])]
  \* Nothing else changes.
  /\ UNCHANGED <<life, seq, born, tomb, retiring, landed, wpc>>

\* Every step anyone can take.
Next ==
  \/ \E f \in Families : Create(f) \/ Drop(f) \/ RetireLater(f)
  \/ \E w \in Writers : ApiCheck(w) \/ Admit(w)
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
