---- MODULE CommitPipeline ----
\* The lock-free commit pipeline (plan 4.7): commits are descriptors in a
\* ring, reserved by one fetch_add, decided in ring order by any thread,
\* written at their offsets, made durable, applied and published by any
\* thread. No thread waits for another: a thread with work in the ring
\* finishes every earlier slot itself (helping).
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/Pipeline.lean:
\*   seqs_dense                 deciding in ring order hands the commit
\*                              slots consecutive sequences, and an abort or
\*                              a void slot takes none: no hole (NoHole)
\*   seqs_strictly_increasing   sequence order is ring order
\*                              (SeqInRingOrder)
\*   publication_order          publishing the longest publishable prefix
\*                              publishes sequences base+1, base+2, ... in
\*                              ring order (PublishedPrefix)
\*   reader_sees_published      a reader at the published horizon sees
\*                              exactly the committed slots below the
\*                              frontier (ReadersSeePrefix)
\*   abort_with_seq_leaves_hole, fetch_max_breaks_prefix
\*                              the RED cases AbortHole and OutOfOrder, as
\*                              counterexamples
\* And in Regolith/GroupCommit.lean, group_eq_serial: a helper validates
\* slot i against the published view plus the keys written by the slots
\* decided to commit but not yet published, and that equals validating it
\* against every earlier commit, the form Conflict states below
\* (NoLostUpdate). The RED ValidatePublished drops the second part, as
\* view_only_breaks_serial does.
\* Lock-freedom, helping and the stopped thread are properties of
\* interleavings, so they are checked here by TLC only.
\*
\* THE ENGINE TODAY, which this replaces (4.6, 4.10).
\*   RegolithEngine::submit             src/engine/commit/mod.rs
\*     A writer pushes a ticket into an ArrayQueue, retrying with
\*     yield_now when it is full, and parks until a leader that holds the
\*     pipeline mutex completes its group (the protocol GroupCommit.tla
\*     models). A leader descheduled while it holds the mutex stops every
\*     writer.
\*
\* THE DESIGN (4.7), step by step.
\*   Reserve   A committer takes ring index i with one fetch_add.
\*   Fill      It installs its descriptor (snapshot, writes, durability)
\*             in slot i with a CAS from claimed to ready.
\*   Decide    Slots are decided in ring order; any thread may decide slot
\*             i. Validation is deterministic: the writes of the slots
\*             below i decided to commit, against the snapshot. A commit
\*             takes the next sequence (which stands for its sequence
\*             range, log positions, allocations and WAL byte range); an
\*             abort takes nothing.
\*   Write     Any thread writes a decided slot's record at its offset (an
\*             idempotent positional write).
\*   Sync      Any thread fsyncs the written prefix and raises the durable
\*             watermark over it.
\*   Apply     Any thread inserts a decided slot's versions (idempotent per
\*             key and sequence).
\*   Publish   Any thread advances the visible horizon over the next slot
\*             when it is an abort or a void, or a commit that is applied
\*             (and durable, at Immediate).
\*   E8        An ingest takes a slot like a commit. Its table install is
\*             queued work any helping thread may run; until it runs, the
\*             slot is not written or applied, so neither the durable
\*             watermark nor the horizon passes it.
\*
\* CHOICES WHERE THE PLAN IS SILENT.
\*   - The window between fetch_add and the descriptor's install. A thread
\*     stopped there would hold an empty slot every later slot waits on. So
\*     a helper that reaches an empty reserved slot in ring order voids it
\*     with a CAS from claimed to void; the owner's own install CAS then
\*     fails, and it reserves again. A void slot takes no sequence. This is
\*     what makes "a stopped thread cannot block others" hold.
\*   - A thread helps while its own slot is unpublished, and helps only
\*     slots at or below its own (4.7 item 10). That is enough for
\*     progress, and nobody does work it does not need.
\*   - The ingest's install is helpable, as a queued background job (4.10:
\*     ingest returns a ticket and runs as a background job or under
\*     poll_io). Were it runnable only by the ingesting thread, a stopped
\*     ingest would block every later commit: the NoHelping shape.
\*   - The ingest is not validated and conflicts with later commits that
\*     write a key it installs from a snapshot below it.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - One sequence per commit, and the WAL offset of a record is its
\*     sequence: each decided commit takes one contiguous range of each,
\*     in the same order, so one number stands for all of them.
\*   - The ring's capacity: a reservation that finds its physical slot
\*     still in use helps publish the slots before it, the same helping
\*     step as here. Slot indices here only grow, up to MaxSlots, and
\*     BoundNeverBinds checks that bound never stops a live thread.
\*   - Rotation (an epoch in the reservation), WAL errors (a latch that
\*     aborts later slots) and recovery: WalRotation.tla and
\*     Regolith/WalRecovery.lean.
\*   - Snapshots taken by readers: a reader reads at visible, so the reader
\*     invariants below quantify over the horizon itself.
\*
\* CONFIGURATIONS.
\*   MC_CommitPipeline_Green                    Mutant = "none", one stop
\*     Every invariant, LockFree and EveryLiveCommitCompletes hold.
\*   MC_CommitPipeline_Red_OutOfOrder           visible is a fetch_max over
\*     any applied slot. ReadersSeePrefix fails.
\*   MC_CommitPipeline_Red_AbortHole            an aborted slot takes a
\*     sequence. NoHole fails.
\*   MC_CommitPipeline_Red_NoHelping            a slot advances only by its
\*     owner. NoLiveThreadBlocked fails: a stopped owner blocks everyone.
\*   MC_CommitPipeline_Red_SyncPastGap          the durable watermark jumps
\*     past an unwritten slot. DurableImpliesWritten fails.
\*   MC_CommitPipeline_Red_ValidatePublished    a slot is validated against
\*     published slots only. NoLostUpdate fails.

EXTENDS Naturals, FiniteSets

CONSTANTS
  Committers,  \* threads that commit one transaction each: positive naturals
  Ingesters,   \* threads that ingest one table each (E8): positive naturals
  Writes,      \* [Committers \cup Ingesters -> SUBSET Nat]: the keys each
               \* commit writes or each ingest installs
  Immediate,   \* the committers whose commit is at Immediate durability
  MaxSlots,    \* the most ring indices fetch_add hands out in the model
  MaxStops,    \* how many threads may stop for good, anywhere
  Mutant       \* "none", "OutOfOrder", "AbortHole", "NoHelping",
               \* "SyncPastGap" or "ValidatePublished"

\* Every thread with a slot to fill.
Actors == Committers \cup Ingesters

ASSUME Actors \subseteq Nat \ {0} /\ Committers \cap Ingesters = {}
ASSUME Writes \in [Actors -> SUBSET Nat]
ASSUME Immediate \subseteq Committers
ASSUME MaxSlots \in Nat /\ MaxStops \in Nat
ASSUME Mutant \in {"none", "OutOfOrder", "AbortHole", "NoHelping", "SyncPastGap",
                   "ValidatePublished"}

\* The ring indices of the model.
Slots == 1..MaxSlots

VARIABLES
  tail,     \* the ring index: the last index fetch_add handed out
  dto,      \* the decided prefix: slots 1..dto are decided, the rest are not
  owner,    \* [Slots -> Actors \cup {0}]: who reserved each slot, 0 for none
  st,       \* [Slots -> state]: "free", "claimed" (reserved, no descriptor),
            \* "ready" (descriptor installed), "commit", "abort" or "void"
  sq,       \* [Slots -> Nat]: the sequence a slot took when decided, 0 for none
  wr,       \* [Slots -> BOOLEAN]: its record is written (an ingest: installed)
  ap,       \* [Slots -> BOOLEAN]: its versions are applied (an ingest: installed)
  lastSeq,  \* the last sequence a decision handed out
  durable,  \* the durable watermark: the last sequence an fsync covered
  pub,      \* the publish frontier: every slot at or below it is published
  visible,  \* the visible horizon a new snapshot reads at
  pc,       \* [Actors -> phase]: "idle", "begun", "claimed", "ready", "done"
  snap,     \* [Actors -> Nat]: the snapshot each transaction began at
  mine,     \* [Actors -> 0..MaxSlots]: the slot each thread holds now
  stopped   \* the threads that stopped for good

\* Every variable, so a step that changes none of them is a stutter.
vars == <<tail, dto, owner, st, sq, wr, ap, lastSeq, durable, pub, visible, pc, snap, mine,
          stopped>>

----------------------------------------------------------------------------
\* Helpers.

\* The greatest element of a finite, nonempty set of naturals.
Max(S) == CHOOSE m \in S : \A n \in S : n <= m

\* Slot i has its verdict: it commits, aborts, or was voided empty.
Decided(i) == st[i] \in {"commit", "abort", "void"}

\* A slot is done with the WAL: decided, and written if it commits.
WalDone(i) == Decided(i) /\ (st[i] = "commit" => wr[i])

\* The written-prefix tracker: the largest w with slots 1..w all done with
\* the WAL. An fsync makes that prefix durable.
WrittenTo ==
  CHOOSE w \in 0..tail : (\A j \in 1..w : WalDone(j)) /\ (w = tail \/ ~WalDone(w + 1))

\* The durable watermark an fsync can publish now: the last sequence in the
\* written prefix. Mutant SyncPastGap: the last sequence written anywhere,
\* gaps and all.
SyncTarget ==
  IF Mutant = "SyncPastGap"
    THEN Max({durable} \cup {sq[j] : j \in {i \in 1..tail : st[i] = "commit" /\ wr[i]}})
    ELSE Max({durable} \cup {sq[j] : j \in {i \in 1..WrittenTo : sq[i] # 0}})

\* Slot i may be published: an abort or a void slot at once; a commit once
\* applied, and durable when it asked for Immediate.
Publishable(i) ==
  \/ st[i] \in {"abort", "void"}
  \/ /\ st[i] = "commit"
     /\ ap[i]
     /\ (owner[i] \in Immediate => sq[i] <= durable)

\* Thread a has not stopped.
Live(a) == a \notin stopped

\* Thread a has a filled slot that is not yet published, so it helps.
Helping(a) == Live(a) /\ pc[a] = "ready" /\ mine[a] > pub

\* Thread a may work on slot i: a helping thread works on any slot at or
\* below its own. Mutant NoHelping: only on its own slot.
MayWork(a, i) ==
  IF Mutant = "NoHelping" THEN Helping(a) /\ mine[a] = i ELSE Helping(a) /\ i <= mine[a]

\* The validation of slot i: some slot below it decided to commit wrote a
\* key slot i writes, at a sequence i's snapshot does not see. Mutant
\* ValidatePublished: only published slots below it count. An ingest is
\* not validated.
Conflict(i) ==
  /\ owner[i] \in Committers
  /\ \E j \in 1..(i - 1) :
       /\ st[j] = "commit"
       /\ sq[j] > snap[owner[i]]
       /\ Writes[owner[j]] \cap Writes[owner[i]] # {}
       /\ (Mutant = "ValidatePublished" => j <= pub)

----------------------------------------------------------------------------
\* Actions. Each is one atomic step of thread a: a fetch_add, a CAS, an
\* idempotent write or an atomic store.

\* The start: an empty ring, nothing decided, written or published.
Init ==
  /\ tail    = 0
  /\ dto     = 0
  /\ owner   = [i \in Slots |-> 0]
  /\ st      = [i \in Slots |-> "free"]
  /\ sq      = [i \in Slots |-> 0]
  /\ wr      = [i \in Slots |-> FALSE]
  /\ ap      = [i \in Slots |-> FALSE]
  /\ lastSeq = 0
  /\ durable = 0
  /\ pub     = 0
  /\ visible = 0
  /\ pc      = [a \in Actors |-> "idle"]
  /\ snap    = [a \in Actors |-> 0]
  /\ mine    = [a \in Actors |-> 0]
  /\ stopped = {}

\* Thread a begins its transaction (or ingest) at the visible horizon.
Begin(a) ==
  /\ pc[a] = "idle"
  /\ pc'   = [pc EXCEPT ![a] = "begun"]
  /\ snap' = [snap EXCEPT ![a] = visible]
  /\ UNCHANGED <<tail, dto, owner, st, sq, wr, ap, lastSeq, durable, pub, visible, mine, stopped>>

\* Thread a reserves the next ring index with one fetch_add.
Reserve(a) ==
  LET i == tail + 1
  IN /\ pc[a] = "begun"
     /\ tail < MaxSlots
     /\ tail'  = i
     /\ owner' = [owner EXCEPT ![i] = a]
     /\ st'    = [st EXCEPT ![i] = "claimed"]
     /\ mine'  = [mine EXCEPT ![a] = i]
     /\ pc'    = [pc EXCEPT ![a] = "claimed"]
     /\ UNCHANGED <<dto, sq, wr, ap, lastSeq, durable, pub, visible, snap, stopped>>

\* Thread a installs its descriptor: the CAS from claimed to ready wins.
Fill(a) ==
  /\ pc[a] = "claimed"
  /\ st[mine[a]] = "claimed"
  /\ st' = [st EXCEPT ![mine[a]] = "ready"]
  /\ pc' = [pc EXCEPT ![a] = "ready"]
  /\ UNCHANGED <<tail, dto, owner, sq, wr, ap, lastSeq, durable, pub, visible, snap, mine, stopped>>

\* Thread a's install CAS lost: a helper voided its slot. It reserves again,
\* keeping its snapshot.
Retry(a) ==
  /\ pc[a] = "claimed"
  /\ st[mine[a]] = "void"
  /\ pc' = [pc EXCEPT ![a] = "begun"]
  /\ UNCHANGED <<tail, dto, owner, st, sq, wr, ap, lastSeq, durable, pub, visible, snap, mine, stopped>>

\* Helping thread a reaches slot i, next in ring order, reserved but empty,
\* and voids it with a CAS from claimed to void. That decides it. Mutant
\* NoHelping never does.
Void(a) ==
  LET i == dto + 1
  IN /\ Mutant # "NoHelping"
     /\ Helping(a)
     /\ i < mine[a]
     /\ st[i] = "claimed"
     /\ st'  = [st EXCEPT ![i] = "void"]
     /\ dto' = i
     /\ UNCHANGED <<tail, owner, sq, wr, ap, lastSeq, durable, pub, visible, pc, snap, mine,
                    stopped>>

\* Thread a decides slot i, next in ring order, with a CAS from ready to
\* the verdict. A commit takes the next sequence; an abort takes none
\* (Mutant AbortHole: it takes one too).
Decide(a) ==
  LET i      == dto + 1
      aborts == Conflict(i)
      takes  == ~aborts \/ Mutant = "AbortHole"
  IN /\ i <= tail
     /\ st[i] = "ready"
     /\ MayWork(a, i)
     /\ st'      = [st EXCEPT ![i] = IF aborts THEN "abort" ELSE "commit"]
     /\ sq'      = IF takes THEN [sq EXCEPT ![i] = lastSeq + 1] ELSE sq
     /\ lastSeq' = IF takes THEN lastSeq + 1 ELSE lastSeq
     /\ dto'     = i
     /\ UNCHANGED <<tail, owner, wr, ap, durable, pub, visible, pc, snap, mine, stopped>>

\* Thread a writes committed slot i's record at its offset.
Write(a, i) ==
  /\ st[i] = "commit"
  /\ ~wr[i]
  /\ owner[i] \in Committers
  /\ MayWork(a, i)
  /\ wr' = [wr EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<tail, dto, owner, st, sq, ap, lastSeq, durable, pub, visible, pc, snap, mine, stopped>>

\* Thread a runs the queued install of ingest slot i: its table, rewritten
\* at the slot's sequence, enters the version. That is the ingest's record
\* and its apply at once.
InstallTable(a, i) ==
  /\ st[i] = "commit"
  /\ ~ap[i]
  /\ owner[i] \in Ingesters
  /\ MayWork(a, i)
  /\ wr' = [wr EXCEPT ![i] = TRUE]
  /\ ap' = [ap EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<tail, dto, owner, st, sq, lastSeq, durable, pub, visible, pc, snap, mine, stopped>>

\* Thread a inserts committed slot i's versions into the memtable.
Apply(a, i) ==
  /\ st[i] = "commit"
  /\ ~ap[i]
  /\ owner[i] \in Committers
  /\ MayWork(a, i)
  /\ ap' = [ap EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<tail, dto, owner, st, sq, wr, lastSeq, durable, pub, visible, pc, snap, mine, stopped>>

\* Helping thread a fsyncs the written prefix and raises the durable
\* watermark over it.
Sync(a) ==
  /\ Helping(a)
  /\ SyncTarget > durable
  /\ durable' = SyncTarget
  /\ UNCHANGED <<tail, dto, owner, st, sq, wr, ap, lastSeq, pub, visible, pc, snap, mine, stopped>>

\* Thread a publishes the slot after the frontier: the frontier moves over
\* it, and the horizon moves to its sequence if it commits.
Publish(a) ==
  LET p == pub + 1
  IN /\ p <= tail
     /\ Decided(p)
     /\ Publishable(p)
     /\ MayWork(a, p)
     /\ pub'     = p
     /\ visible' = IF st[p] = "commit" THEN sq[p] ELSE visible
     /\ UNCHANGED <<tail, dto, owner, st, sq, wr, ap, lastSeq, durable, pc, snap, mine, stopped>>

\* Mutant OutOfOrder: the horizon is a fetch_max, raised by a thread whose
\* later slot is applied while an earlier one is not.
PublishAny(a, i) ==
  /\ Mutant = "OutOfOrder"
  /\ i > pub + 1
  /\ st[i] = "commit"
  /\ Publishable(i)
  /\ MayWork(a, i)
  /\ visible < sq[i]
  /\ visible' = sq[i]
  /\ UNCHANGED <<tail, dto, owner, st, sq, wr, ap, lastSeq, durable, pub, pc, snap, mine, stopped>>

\* Thread a's slot is published: its commit (or abort) is final and its
\* call returns.
Finish(a) ==
  /\ pc[a] = "ready"
  /\ mine[a] <= pub
  /\ pc' = [pc EXCEPT ![a] = "done"]
  /\ UNCHANGED <<tail, dto, owner, st, sq, wr, ap, lastSeq, durable, pub, visible, snap, mine, stopped>>

\* Any step of live thread a.
LiveStep(a) ==
  /\ Live(a)
  /\ \/ Begin(a) \/ Reserve(a) \/ Fill(a) \/ Retry(a) \/ Void(a) \/ Decide(a)
     \/ Sync(a) \/ Publish(a) \/ Finish(a)
     \/ \E i \in Slots : Write(a, i) \/ InstallTable(a, i) \/ Apply(a, i) \/ PublishAny(a, i)

\* Thread a stops for good in the middle of its commit (descheduled
\* forever, or its task dropped), at most MaxStops threads in all.
Stop(a) ==
  /\ Cardinality(stopped) < MaxStops
  /\ a \notin stopped
  /\ pc[a] \in {"begun", "claimed", "ready"}
  /\ stopped' = stopped \cup {a}
  /\ UNCHANGED <<tail, dto, owner, st, sq, wr, ap, lastSeq, durable, pub, visible, pc, snap, mine>>

\* A step of some live thread.
LiveNext == \E a \in Actors : LiveStep(a)

\* Every step the system can take.
Next == LiveNext \/ \E a \in Actors : Stop(a)

\* Every behaviour: start in Init, take Next steps, and the live threads
\* keep taking steps while any can (weak fairness of the live threads as a
\* whole). A stopped thread is owed nothing, and no thread is promised a
\* turn of its own: that is lock-freedom's scheduler, which may starve any
\* one thread. No step here spins or waits, so every behaviour is finite
\* and ends where no live step is possible; per-thread fairness adds
\* nothing (MC_CommitPipeline_Green with WF_vars(LiveStep(a)) for each
\* thread gives the same verdict over the same states, at about twice the
\* time).
Spec == Init /\ [][Next]_vars /\ WF_vars(LiveNext)

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ tail \in 0..MaxSlots
  /\ dto \in 0..tail
  /\ owner \in [Slots -> Actors \cup {0}]
  /\ st \in [Slots -> {"free", "claimed", "ready", "commit", "abort", "void"}]
  /\ sq \in [Slots -> 0..lastSeq]
  /\ wr \in [Slots -> BOOLEAN] /\ ap \in [Slots -> BOOLEAN]
  /\ durable <= lastSeq /\ visible <= lastSeq /\ pub <= tail
  /\ pc \in [Actors -> {"idle", "begun", "claimed", "ready", "done"}]
  /\ stopped \subseteq Actors
  /\ \A i \in Slots : (i <= tail) <=> st[i] # "free"

\* Slots are decided in ring order: exactly the slots up to dto are
\* decided.
DecidedIsPrefix == dto <= tail /\ \A i \in Slots : Decided(i) <=> i <= dto

\* Publication is a prefix of decided slots in ring order, each publishable.
\* Lean: publication_order.
PublishedPrefix == \A i \in 1..pub : Decided(i) /\ Publishable(i)

\* No reader sees a later slot without every earlier one: a reader at the
\* horizon sees a committed slot exactly when the slot is below the
\* frontier, and then its versions are applied. Lean: reader_sees_published.
ReadersSeePrefix ==
  \A i \in 1..tail : st[i] = "commit" =>
    /\ (sq[i] <= visible <=> i <= pub)
    /\ (i <= pub => ap[i])

\* No hole: the committed slots hold exactly the sequences 1..lastSeq, and
\* only a committed slot holds one. An abort or a void slot takes nothing.
\* Lean: seqs_dense.
NoHole ==
  /\ {sq[i] : i \in {j \in 1..tail : st[j] = "commit"}} = 1..lastSeq
  /\ \A i \in 1..tail : sq[i] # 0 => st[i] = "commit"

\* Sequence order is ring order. Lean: seqs_strictly_increasing.
SeqInRingOrder ==
  \A i, j \in 1..tail : i < j /\ st[i] = "commit" /\ st[j] = "commit" => sq[i] < sq[j]

\* Durable implies written: every sequence the durable watermark covers
\* belongs to a written record.
DurableImpliesWritten == \A i \in 1..tail : sq[i] # 0 /\ sq[i] <= durable => wr[i]

\* At Immediate a commit is visible only once durable.
DurableBeforeVisible ==
  \A i \in 1..tail : st[i] = "commit" /\ owner[i] \in Immediate /\ sq[i] <= visible =>
    sq[i] <= durable

\* E8: the horizon never passes an ingest slot whose table is not
\* installed.
IngestNotPassed ==
  \A i \in 1..tail : owner[i] \in Ingesters /\ st[i] = "commit" /\ ~ap[i] => visible < sq[i]

\* No lost update: of two committed slots writing a common key, the later
\* one's snapshot saw the earlier one.
NoLostUpdate ==
  \A i, j \in 1..tail :
    /\ i < j
    /\ st[i] = "commit" /\ st[j] = "commit"
    /\ owner[j] \in Committers
    /\ Writes[owner[i]] \cap Writes[owner[j]] # {}
    => sq[i] <= snap[owner[j]]

\* No live thread is ever blocked: when no live thread can take a step,
\* every live thread's commit is done.
NoLiveThreadBlocked ==
  (~ENABLED (\E a \in Actors : LiveStep(a))) => \A a \in Actors \ stopped : pc[a] = "done"

\* The model's slot bound never stops a live thread from reserving, so the
\* liveness results are not artefacts of the bound.
BoundNeverBinds == \A a \in Actors \ stopped : pc[a] = "begun" => tail < MaxSlots

----------------------------------------------------------------------------
\* Liveness.

\* Some live thread has a commit in flight that is not yet published.
LivePending ==
  \E a \in Actors \ stopped :
    \/ pc[a] \in {"begun", "claimed"}
    \/ pc[a] = "ready" /\ mine[a] > pub

\* A step that publishes a slot: the frontier moves.
FrontierMoves == pub' > pub

\* Lock-freedom: some slot always completes. Either slots keep being
\* published forever, or there comes a time after which no live thread
\* has work left. A behaviour in which a live thread holds work and the
\* frontier stops moving for good satisfies neither.
LockFree == []<><<FrontierMoves>>_vars \/ <>[](~LivePending)

\* A stopped thread cannot block others: there comes a time when every
\* thread's commit is done, except the commits of threads that stopped.
EveryLiveCommitCompletes == <>(\A a \in Actors : pc[a] = "done" \/ a \in stopped)

----------------------------------------------------------------------------
\* Workloads, chosen by the configurations.

\* Committer 1 writes key 1; committer 2 writes keys 1 and 2; the ingest
\* installs key 2. The two committers conflict on key 1, and committer 2
\* conflicts with the ingest on key 2, so aborts happen either way. Committer
\* 1 shares no key with the ingest, so it can commit and be applied behind
\* an ingest whose table is not installed yet: the E8 window.
Overlapping == [a \in Actors |-> CASE a = 1 -> {1} [] a = 2 -> {1, 2} [] OTHER -> {2}]

====
