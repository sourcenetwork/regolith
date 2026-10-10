---- MODULE TombstoneLog ----
\* ===========================================================================
\* THE STORY
\* ===========================================================================
\* A range delete ("delete every key from a to m") is stored in the
\* memtable as a range tombstone, beside the point writes. Every read in
\* that memtable checks the tombstones: a key a tombstone covers is deleted.
\* So the tombstones are read all the time, by many threads at once, while
\* the commit leader appends new ones (src/engine/memtable/tombstones.rs).
\*
\* They live in an append-only log that readers walk without a lock:
\*   - the writer (only ever one: the commit leader) puts the new tombstone
\*     into the next free slot first, and only then raises the published
\*     length by one;
\*   - a reader reads the published length first, then only the slots
\*     below it.
\* Then the commit that wrote the tombstone is made visible: the leader
\* raises the read horizon, and a reader takes its snapshot from that
\* horizon before it reads anything.
\*
\* Tiny example. The leader writes tombstone 1 into slot 1, publishes
\* length 1, then publishes the horizon 1. A reader samples horizon 1, reads
\* length 1, reads slot 1, and finds the tombstone whole.
\*
\* What can go wrong, and what this model checks cannot happen:
\*   - a reader sees an append before its contents are written: it reads a
\*     slot the writer has not filled yet (PrefixWhole);
\*   - a reader whose snapshot includes a commit misses the tombstone that
\*     commit wrote (PublishedSeen).
\*
\* WHAT IS MODELLED, and the code each piece mirrors:
\*   slots     the log's slots: slot i holds append i once written, 0 before
\*             (TombstoneLog::segments)
\*   len       the published length (TombstoneLog::len)
\*   wstep     where the writer is inside one append and its commit
\*   next      which append the writer is on
\*   horizon   the read horizon: appends whose commit is visible
\*   rstate    a reader's progress; rsnap, rlen and rseen what it sampled,
\*             read and saw
\*
\* WHAT IS LEFT OUT, and why that loses nothing:
\*   - The sorted index a writer publishes every few appends. It is built
\*     only from published slots and read beside the tail scan, so it is a
\*     faster way to read the same prefix; the property tests check that it
\*     answers exactly what the scan does.
\*   - What a tombstone covers. Only whether a reader sees it whole matters.
\*   - Memory ordering: the loom models in src/engine/loom_model/tombstones.rs
\*     run the real log and catch a slot read that is not ordered after its
\*     write. Here each store and load is one atomic step.
\*
\* CONFIGURATIONS (each GREEN must pass, each RED must break the one
\* invariant it names):
\*   MC_TombstoneLog_Green              write the slot, publish the length,
\*                                      then publish the horizon.
\*   MC_TombstoneLog_Red_LenFirst       the length is published before the
\*                                      slot is written: PrefixWhole breaks.
\*   MC_TombstoneLog_Red_HorizonFirst   the horizon is published before the
\*                                      length: PublishedSeen breaks.
\*
\* Lean, proofs/lean/Regolith/TombstoneLog.lean, proves the same rules for
\* any number of appends and readers.

\* Numbers and sequences (what a reader saw, in order).
EXTENDS Naturals, Sequences

\* The fixed inputs of a configuration.
CONSTANTS
  \* How many tombstones the writer appends.
  Appends,
  \* The reader threads.
  Readers,
  \* "Green" for the real code, or the name of one planted bug.
  Mode

\* The bug names this model knows.
ASSUME Mode \in {"Green", "LenFirst", "HorizonFirst"}
\* At least one append.
ASSUME Appends \in Nat /\ Appends >= 1

\* The state that changes from step to step.
VARIABLES
  \* [1..Appends -> 0..Appends]: slot i holds i once append i is written.
  slots,
  \* The published length.
  len,
  \* The writer's next step for the append it is on.
  wstep,
  \* The append the writer is on (Appends + 1 once all are done).
  next,
  \* The read horizon: how many appends' commits are visible.
  horizon,
  \* [Readers -> {"idle", "sampled", "reading", "done"}].
  rstate,
  \* [Readers -> Nat]: the horizon a reader sampled, its snapshot.
  rsnap,
  \* [Readers -> Nat]: the length a reader read.
  rlen,
  \* [Readers -> Seq(Nat)]: the slots a reader read, in order.
  rseen

\* Every variable, so a step that changes none of them is a stutter.
vars == <<slots, len, wstep, next, horizon, rstate, rsnap, rlen, rseen>>

\* The writer's three steps for one append, in the order it takes them.
\* Green: write the slot, publish the length, publish the horizon.
\* LenFirst: publish the length before writing the slot.
\* HorizonFirst: publish the horizon before the length.
Order ==
  \* The real order.
  CASE Mode = "Green"        -> <<"write", "length", "horizon">>
    \* The length before the slot.
    [] Mode = "LenFirst"     -> <<"length", "write", "horizon">>
    \* The horizon before the length.
    [] Mode = "HorizonFirst" -> <<"write", "horizon", "length">>

\* The start: nothing written, nothing published, every reader idle.
Init ==
  \* No slot is written ...
  /\ slots = [i \in 1..Appends |-> 0]
  \* ... nothing is published ...
  /\ len = 0
  \* ... and the writer begins with the first step ...
  /\ wstep = 1
  \* ... of the first append.
  /\ next = 1
  \* No commit is visible.
  /\ horizon = 0
  \* Every reader is idle ...
  /\ rstate = [r \in Readers |-> "idle"]
  \* ... with no snapshot ...
  /\ rsnap = [r \in Readers |-> 0]
  \* ... no length read ...
  /\ rlen = [r \in Readers |-> 0]
  \* ... and nothing seen.
  /\ rseen = [r \in Readers |-> <<>>]

\* The writer takes its next step on append `next`.
WriterStep ==
  \* Only while appends remain.
  /\ next <= Appends
  \* Do whichever step comes next in this mode's order.
  /\ LET step == Order[wstep] IN
       \* Write the tombstone into its slot.
       /\ slots' = IF step = "write" THEN [slots EXCEPT ![next] = next] ELSE slots
       \* Publish the length: append `next` is now in the readable prefix.
       /\ len' = IF step = "length" THEN next ELSE len
       \* Publish the horizon: the commit is visible to new snapshots.
       /\ horizon' = IF step = "horizon" THEN next ELSE horizon
  \* After the third step, start over at the first step ...
  /\ wstep' = IF wstep = 3 THEN 1 ELSE wstep + 1
  \* ... of the next append.
  /\ next' = IF wstep = 3 THEN next + 1 ELSE next
  \* Readers are not touched.
  /\ UNCHANGED <<rstate, rsnap, rlen, rseen>>

\* A reader takes its snapshot: it samples the horizon (an acquire load of
\* the read horizon) before it reads anything.
Sample(r) ==
  \* An idle reader ...
  /\ rstate[r] = "idle"
  \* ... takes the horizon as its snapshot ...
  /\ rsnap' = [rsnap EXCEPT ![r] = horizon]
  \* ... and is ready to read.
  /\ rstate' = [rstate EXCEPT ![r] = "sampled"]
  \* Nothing else changes.
  /\ UNCHANGED <<slots, len, wstep, next, horizon, rlen, rseen>>

\* The reader reads the published length (TombstoneLog::len, acquire).
ReadLen(r) ==
  \* A reader with its snapshot ...
  /\ rstate[r] = "sampled"
  \* ... reads the published length ...
  /\ rlen' = [rlen EXCEPT ![r] = len]
  \* ... and starts on the slots below it.
  /\ rstate' = [rstate EXCEPT ![r] = "reading"]
  \* Nothing else changes.
  /\ UNCHANGED <<slots, len, wstep, next, horizon, rsnap, rseen>>

\* The reader reads its next slot below the length it read.
ReadSlot(r) ==
  \* A reading reader ...
  /\ rstate[r] = "reading"
  \* ... with slots left below its length ...
  /\ Len(rseen[r]) < rlen[r]
  \* ... reads the next one, whatever it holds right now.
  /\ rseen' = [rseen EXCEPT ![r] = Append(@, slots[Len(@) + 1])]
  \* Nothing else changes.
  /\ UNCHANGED <<slots, len, wstep, next, horizon, rstate, rsnap, rlen>>

\* The reader has read every slot below its length.
Finish(r) ==
  \* A reading reader ...
  /\ rstate[r] = "reading"
  \* ... that has read every slot below its length ...
  /\ Len(rseen[r]) = rlen[r]
  \* ... is done.
  /\ rstate' = [rstate EXCEPT ![r] = "done"]
  \* Nothing else changes.
  /\ UNCHANGED <<slots, len, wstep, next, horizon, rsnap, rlen, rseen>>

\* Every step the system can take.
Next ==
  \* The writer takes a step ...
  \/ WriterStep
  \* ... or some reader does.
  \/ \E r \in Readers : Sample(r) \/ ReadLen(r) \/ ReadSlot(r) \/ Finish(r)

\* Every behaviour: start in Init, then take Next steps or stutter.
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  \* Each slot holds an append number or 0 ...
  /\ slots \in [1..Appends -> 0..Appends]
  \* ... the length ...
  /\ len \in 0..Appends
  \* ... and the horizon stay within the appends ...
  /\ horizon \in 0..Appends
  \* ... and every reader is in one of its states.
  /\ rstate \in [Readers -> {"idle", "sampled", "reading", "done"}]

\* THE HEADLINE. What a reader reads is a prefix of the appends, each one
\* whole: its i-th slot holds append i. Rules out: the writer publishes
\* length 1, a reader reads slot 1 before the tombstone is in it, and a
\* deleted key reads back as live. Lean: prefix_whole.
PrefixWhole ==
  \* For every reader and every slot it read: it found that append, whole.
  \A r \in Readers : \A i \in 1..Len(rseen[r]) : rseen[r][i] = i

\* A reader whose snapshot includes a commit sees the tombstone that commit
\* wrote: the length it reads is at least the horizon it sampled. Rules out:
\* the horizon covers append 1, a reader samples it, reads length 0 and
\* misses the delete its own snapshot includes. Lean: published_seen.
PublishedSeen ==
  \* For every reader past its length read: it read at least its snapshot.
  \A r \in Readers : rstate[r] \in {"reading", "done"} => rlen[r] >= rsnap[r]

====
