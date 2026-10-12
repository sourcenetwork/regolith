---- MODULE CommitPipeline ----
\* The lock-free commit pipeline as built (plan 4.7; src/engine/commit).
\*
\* THE PICTURE. Think of a bakery with a ticket machine. Every customer (a
\* commit) pulls a numbered ticket (a slot of the ring). Orders are handled
\* strictly in ticket order, but by whoever is standing at the counter: any
\* customer may do the next step of any order ahead of their own. So a
\* customer who wanders off never holds the queue up: the next one finishes
\* their order for them, or throws their unused ticket away.
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/Pipeline.lean:
\*   seqs_dense, seqs_strictly_increasing
\*       NoHole, SeqInRingOrder.
\*   publication_order, reader_sees_published
\*       PublishedPrefix, ReadersSeePrefix.
\*   rollback_as_if_never_decided
\*       NoHole across a rollback: the sequences are the ones the kept and
\*       the later slots would have taken had the discarded ones never
\*       been decided.
\*   rollback_keeps_published, rollback_finishes_everything
\*       a rollback touches nothing published and leaves nothing waiting
\*       (G2, PublishedPrefix).
\*   sync_covers_only_written
\*       DurableImpliesWritten.
\* In proofs/lean/Regolith/PipelineHelping.lean:
\*   first_unfinished_can_step, helper_alone_finishes, no_step_goes_back,
\*   helping_is_bounded
\*       the safety half of lock-freedom: every ordering rule looks only at
\*       earlier slots, so the first unfinished slot always has a step any
\*       thread at or behind it may take; no step of any thread undoes
\*       another's; so one live thread alone finishes every slot up to its
\*       own in a bounded number of its own steps (E21), wherever the
\*       others stopped.
\*   held_round_blocks
\*       the stated limit: a thread that stops holding the round stops the
\*       commits that wait for the sync (RED StopHoldsClaim).
\* And in Regolith/GroupCommit.lean, group_eq_serial and early_check_split:
\* validating slot i against a view that holds every slot decided before it
\* equals validating it against every earlier commit, and checking up to a
\* horizon on the committer's own thread and above it when the slot is
\* decided equals one check (NoLostUpdate, AbortsHaveCause).
\* The other half of lock-freedom, that the interleavings of several
\* threads keep finishing slots (LockFree, EveryLiveCommitCompletes), is
\* checked here by TLC, on small instances.
\*
\* THE CODE, step by step, and the action that stands for each step.
\*   Begin, EarlyAbort
\*               Transaction::begin, and RegolithEngine::check_early
\*               (early.rs): before it takes a slot a transaction samples
\*               the read horizon and checks itself, on its own thread,
\*               against everything visible up to it; a conflict there
\*               aborts it at once. Whichever thread decides its slot then
\*               looks only above that horizon (Conflict).
\*   Reserve     Ring::reserve, one fetch_add on the tail.
\*   Fill        Ring::install, one compare-and-swap of the cell's stamp.
\*   Void        Ring::void by a helper that reaches a reserved cell with
\*               nothing in it; the owner's install then fails (Retry).
\*   ReadTip, DecideCas
\*               RegolithEngine::decide: read the tip (the state after the
\*               newest decided slot), check the slot is next, compute the
\*               decision, install it with one compare-and-swap
\*               (Descriptor::decide). An abort takes nothing. "Abort" here
\*               is every decision that lands nothing: a lost conflict, a
\*               dropped column family (the fence), a database that is
\*               closed, a validation read that would block (R11).
\*   Apply, TipMove, MarkStale, Pass
\*               RegolithEngine::settle: apply the slot to its memtable,
\*               move the tip to its decision, pass the decided frontier. A
\*               decision whose epoch is not the tip's is stale: its slot is
\*               failed instead.
\*   Write, WriteFail
\*               write_slot: a positional write of the record, behind the
\*               log's epoch gate (Log::write_record). A failed write
\*               poisons the log.
\*   ClaimRound, SyncBegin, SyncOk, SyncFail
\*               round.rs: the round is one claim on the log's device step.
\*               Whoever claims it syncs the written prefix.
\*   RbFreeze, RbFinish
\*               ordered.rs roll_back, run by the thread that holds the
\*               round when the log is poisoned: freeze the frontiers, move
\*               to a new epoch, publish what is publishable, fail the rest,
\*               cut the log, replace the memtable, thaw.
\*   PubHorizon, PubFrontier
\*               publish_upto: raise the read horizon, then pass the
\*               published frontier.
\*   ClaimNext, UnitRun, TurnRun
\*               ordered.rs: an ordered unit (an ingest's install, a column
\*               family's create or drop, a close) takes a slot, and the
\*               rotation check takes the turn of the write that finds the
\*               memtable full. Either is a job claimed with one
\*               compare-and-swap by whichever thread reaches the slot, and
\*               runs with everything before it published.
\*
\* WHAT IS NOT A STOPPED THREAD. A thread that holds the round, or that
\* claimed an ordered unit, is taken to be at work on the device (an fsync,
\* a truncate, a flush, a new log file), and the model never stops it
\* there. This is a limit of the code and not only of the model: between
\* its claim and its end such a thread also runs ordinary code, and a
\* thread descheduled for good in that window holds up every commit that
\* needs the round or stands behind the unit. The RED StopHoldsClaim shows
\* exactly that. Everywhere else a thread may stop for good.
\*
\* SMALL STEPS AND ONE-GO STEPS. Deciding an order is four steps in the
\* code (install the verdict, apply, move the tip, pass the frontier) and
\* publishing it is two (horizon, frontier). Whatever another thread does
\* between two of those steps it could as well have done before the first
\* or after the last, and come out the same, with one exception: a
\* rollback, which may fall between any two of them. So a configuration may
\* set Coarse: the steps are then taken one by one for as long as a rollback
\* can still happen (the log may still fail, or a failure is being dealt
\* with), and in one go otherwise. With Coarse unset every step is always
\* taken on its own. The run that checks every invariant for three threads
\* and the runs of two threads leave it unset; the other runs of three set
\* it, which is what lets them finish in seconds. Each .cfg says which it
\* is, and what it gave up.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - One sequence per commit, and a record's offset is its sequence: each
\*     decided commit takes one contiguous range of each, in the same order,
\*     so one number stands for both.
\*   - The ring's capacity. A reservation that finds its cell in use helps
\*     publish the slot a lap before, the same helping as here; indices here
\*     only grow, up to MaxSlots, and BoundNeverBinds checks the bound never
\*     stops a live thread.
\*   - The pins that keep a loaded descriptor alive, the parking on a job,
\*     and the two loads a decider makes around a rotation: loom models in
\*     src/engine/commit/loom_model.rs.
\*   - commit_nowait. Its commits take the same steps; where a blocking
\*     call waits for a round or a unit another thread claimed, such a
\*     commit leaves the job on its own queue and returns. The queue and
\*     the delivery of the completion are NonBlocking.tla.
\*   - Two threads writing one verdict at once. Both work it out from the
\*     same tip, so both write the same one, and one compare-and-swap
\*     keeps one; the model writes it once. The exception is a thread
\*     whose tip a rollback has since discarded, and that one the model
\*     has (ReadTip, DecideCas).
\*   - Recovery: WalRecovery.tla and Regolith/WalRecovery.lean.
\*
\* CONFIGURATIONS are listed with what each shows in the .cfg files.
\*
\* THE MODEL IS IN THREE MODULES, each small enough to read in one go:
\*   CommitPipelineBase.tla   what a configuration chooses, the state, and
\*                            the small questions the steps ask;
\*   CommitPipelineSteps.tla  the steps, one action each;
\*   CommitPipeline.tla       this one: what must be true of them.

\* The state, the helpers and the steps.
EXTENDS CommitPipelineSteps

\* Invariants: what is true in every reachable state.

\* Every variable holds the kind of thing its comment says.
TypeOK ==
  \* The tail is a ticket number or zero.
  /\ tail \in 0..MaxSlots
  \* Cells hold one of the four states.
  /\ cell \in [Slots -> {"free", "claimed", "ready", "void"}]
  \* Owners are threads, or nobody.
  /\ owner \in [Slots -> Actors \cup {0}]
  \* Verdicts are one of the four.
  /\ dec \in [Slots -> {"none", "commit", "abort", "unit"}]
  \* Sequences and epochs are numbers...
  /\ sq \in [Slots -> Nat] /\ ep \in [Slots -> Nat]
  \* ...and so are log generations and memtable numbers.
  /\ logOf \in [Slots -> Nat] /\ memOf \in [Slots -> Nat]
  \* The three flags are yes or no.
  /\ ap \in [Slots -> BOOLEAN] /\ wr \in [Slots -> BOOLEAN] /\ failed \in [Slots -> BOOLEAN]
  \* The frontiers lie within the tickets handed out, published behind decided.
  /\ dto \in 0..tail /\ pub \in 0..dto /\ tipIdx \in 0..tail
  \* The switches are yes or no.
  /\ frozen \in BOOLEAN /\ poisoned \in BOOLEAN
  \* The round's holders are threads, and so is a claimant.
  /\ round \subseteq Actors /\ claimant \in Actors \cup {0}
  \* A sync's promise is a sequence, or zero for none.
  /\ target \in [Actors -> Nat]
  \* Every thread is at a known point.
  /\ pc \in [Actors -> {"idle", "open", "begun", "claimed", "ready", "done", "failed", "aborted"}]
  \* The stopped are threads.
  /\ stopped \subseteq Actors
  \* A cell is free exactly when its ticket has not been handed out.
  /\ \A i \in Slots : (i <= tail) <=> cell[i] # "free"

\* R1, one fate per ticket: an owner who believes its order is in the ring
\* is right. Fails under VoidNotCas.
OwnerSeesItsFate ==
  \A a \in Actors : pc[a] \in {"ready", "done", "failed"} => cell[mine[a]] = "ready"

\* One thread at a time on the log's device step.
OneRound == Cardinality(round) <= 1

\* Orders are settled in ticket order: everything up to the frontier has a
\* verdict or was thrown away, and nothing beyond the next order has one.
DecidedIsPrefix ==
  \* Up to the frontier, settled.
  /\ \A i \in 1..dto : cell[i] = "void" \/ dec[i] # "none"
  \* Beyond the next order, untouched.
  /\ \A i \in Slots : i > dto + 1 => dec[i] = "none"
  \* The tip is never more than one order ahead of the frontier.
  /\ tipIdx <= dto + 1

\* No hole: the sequences held by the orders the tip covers are exactly
\* 1, 2, ..., up to the last one handed out, and only an order that landed
\* holds one. An abort, a thrown-away ticket and a thrown-out order hold
\* none. Fails under AbortHole, SettleAnyEpoch and NoFreeze.
NoHole ==
  \* The sequences that count are exactly 1..tipNext.
  /\ {sq[i] : i \in {j \in 1..tipIdx : Takes(j)}} = 1..tipNext
  \* Only a commit or a unit holds a sequence that counts.
  /\ \A i \in 1..tipIdx : Takes(i) => dec[i] \in {"commit", "unit"}

\* Sequence order is ticket order.
SeqInRingOrder ==
  \A i, j \in 1..tipIdx : i < j /\ Takes(i) /\ Takes(j) => sq[i] < sq[j]

\* P2: an order the line has moved past that landed is in the memtable, so
\* the order after it was checked against it. Fails under PassBeforeApply.
AppliedBeforePassed ==
  \A i \in 1..dto : (Brings(i) \/ dec[i] = "unit") /\ ~failed[i] => InMem(i)

\* Outside a rollback, the memtable readers are shown holds no order that
\* was thrown out. Fails under KeepMemtable.
MemtableOnlyLive == rbLast = 0 => \A i \in Slots : InMem(i) => ~failed[i]

\* The same for the log: no record of a thrown-out order. Fails under
\* NoEpochGate.
RecordsAreLive == rbLast = 0 => \A i \in Slots : wr[i] => ~failed[i]

\* Everything behind the published frontier is settled and was allowed to
\* be finished. Fails under RollbackForgets.
PublishedPrefix == \A i \in 1..pub : Publishable(i)

\* P3: an order behind the published frontier is visible. Its owner, told
\* it is finished, reads its own write. Fails under FrontierFirst.
PublishedIsVisible == \A i \in 1..pub : Takes(i) => sq[i] <= visible

\* No reader sees a later order without every earlier one: whatever the
\* horizon covers is in the memtable, is the next order to finish at most,
\* and was allowed to be finished. Fails under OutOfOrder.
ReadersSeePrefix ==
  \A i \in 1..tipIdx : Takes(i) /\ sq[i] <= visible =>
    \* Its writes are there to be read.
    /\ InMem(i)
    \* It is finished, or the very next to be.
    /\ i <= pub + 1
    \* And it met the conditions for finishing.
    /\ Publishable(i)

\* What the durable mark covers is written. Fails under SyncPastGap,
\* TwoSyncs and UnitNoDrain.
DurableImpliesWritten ==
  \A i \in 1..tipIdx : Takes(i) /\ dec[i] = "commit" /\ sq[i] <= durable => wr[i]

\* The durable mark never passes the last sequence handed out: a rollback
\* hands back no sequence a sync vouched for. Fails under TwoSyncs.
DurableWithinDecided == durable <= tipNext

\* At Immediate, visible only once durable.
DurableBeforeVisible ==
  \A i \in 1..tipIdx :
    Takes(i) /\ dec[i] = "commit" /\ owner[i] \in Immediate /\ sq[i] <= visible => sq[i] <= durable

\* No lost update: a transaction that commits read no key an earlier
\* landed order wrote after it began reading. Of two transactions that
\* read and write one key from the same snapshot, at most one commits.
\* Fails under ValidatePublished, PassBeforeApply and TrustEarly.
NoLostUpdate ==
  \A i, j \in 1..tipIdx :
    \* Two orders in ticket order...
    /\ i < j
    \* ...the earlier one landed and counts...
    /\ Takes(i)
    \* ...the later one a transaction that committed and counts...
    /\ dec[j] = "commit" /\ ~failed[j] /\ owner[j] \in Committers \ Plain
    \* ...and read a key the earlier one wrote.
    /\ Writes[owner[i]] \cap Reads[owner[j]] # {}
    \* Then the later one began reading after the earlier one landed.
    => sq[i] <= snap[owner[j]]

\* No transaction is turned away for nothing: one that aborted, in its
\* slot or at its early check, lost to an order that landed after it began
\* reading and wrote a key it read. With NoLostUpdate this says the
\* pipeline decides each transaction as committing them one at a time, in
\* sequence order, would.
AbortsHaveCause ==
  \* An abort decided in a slot that still counts...
  /\ \A i \in 1..tipIdx : dec[i] = "abort" /\ ~failed[i] =>
       \* ...has an earlier order that landed...
       \E j \in 1..(i - 1) : /\ Takes(j)
                              \* ...after its transaction began reading...
                              /\ sq[j] > snap[owner[i]]
                              \* ...on a key it read.
                              /\ Writes[owner[j]] \cap Reads[owner[i]] # {}
  \* An abort at the early check...
  /\ \A a \in Actors : pc[a] = "aborted" =>
       \* ...has an order that landed...
       \E j \in 1..tipIdx : /\ Takes(j)
                             \* ...after the transaction began reading...
                             /\ sq[j] > snap[a]
                             \* ...on a key it read.
                             /\ Writes[owner[j]] \cap Reads[a] # {}

\* A rotation runs alone: a commit still in flight belongs to the log that
\* is current, so a rotation never leaves a record to be written in a log
\* it sealed. Fails under UnitNoDrain.
InFlightInCurrentLog ==
  \A i \in 1..tipIdx : i > pub /\ Brings(i) /\ ~failed[i] => logOf[i] = gen

\* G2: nobody is told "done" for an order that was thrown out, nobody is
\* told "failed" for one that landed, and a commit told "done" has its
\* record in the log.
NoFalseAck ==
  \A a \in Actors :
    \* "done" means the order counts...
    /\ (pc[a] = "done" => ~failed[mine[a]])
    \* ...and, if it committed with writes, that its record is written.
    /\ (pc[a] = "done" /\ Brings(mine[a]) => wr[mine[a]])
    \* "failed" means it was thrown out.
    /\ (pc[a] = "failed" => failed[mine[a]])

\* A note is only ever for an order with no verdict: the others were used
\* up when the verdict was written.
NotesAreForUndecided ==
  \A a \in Actors : seen[a] # NoNote => dec[seen[a][1]] = "none"

\* No live thread is ever stuck: when no live thread can take a step,
\* every live thread's call has returned. Fails under NoHelping and
\* StopHoldsClaim.
NoLiveThreadBlocked ==
  (~ENABLED LiveNext) => \A a \in Actors \ stopped : pc[a] \in {"done", "failed", "aborted"}

\* The run's ticket bound never stops a live thread, so nothing above is an
\* artefact of the bound.
BoundNeverBinds ==
  \A a \in Actors \ stopped : pc[a] \in {"idle", "open", "begun"} => tail < MaxSlots

----------------------------------------------------------------------------
\* Witnesses. Each of these is FALSE somewhere in the design: a run that
\* checks one as an invariant must break it. That shows the GREEN runs
\* really reach the case, and are not green because nothing happened.

\* "No order is ever thrown out." Broken once a rollback discards one.
NothingThrownOut == \A i \in Slots : ~failed[i]

\* "No verdict is ever found stale." Broken once an order is failed at its
\* settling, ahead of the tip, because its verdict came from a state a
\* rollback had discarded.
NoStaleVerdict == \A i \in Slots : failed[i] => i <= tipIdx

\* "No ticket is ever thrown away." Broken once a helper voids one.
NothingVoided == \A i \in Slots : cell[i] # "void"

\* "A stopped thread's order is never finished." Broken once the others
\* have carried it through.
StoppedStaysUnfinished == \A a \in stopped : pc[a] = "ready" => mine[a] > pub

\* "The log is never rotated." Broken once a rotation check seals it.
NeverRotated == gen = 0

\* "No transaction is ever turned away by its own early check." Broken
\* once one is.
NoEarlyAbort == \A a \in Actors : pc[a] # "aborted"

----------------------------------------------------------------------------
\* Liveness: what eventually happens.

\* Some live thread has a commit in flight.
LivePending == \E a \in Actors \ stopped : pc[a] \in {"begun", "claimed", "ready"}

\* A step that finishes an order: the published frontier moves.
FrontierMoves == pub' > pub

\* Lock-freedom: either orders keep being finished forever, or there comes
\* a time after which no live thread has work left. A run in which a live
\* thread has work and the frontier stops for good is neither.
LockFree == []<><<FrontierMoves>>_vars \/ <>[](~LivePending)

\* A stopped thread blocks nobody: eventually every thread's call has
\* returned, except the threads that walked away.
EveryLiveCommitCompletes ==
  <>(\A a \in Actors : pc[a] \in {"done", "failed", "aborted"} \/ a \in stopped)

----------------------------------------------------------------------------
\* Workloads, chosen by the configurations.

\* Thread 1 writes key 1; thread 2 writes keys 1 and 2; any other thread
\* writes key 2. So threads 1 and 2 conflict on key 1, and thread 2
\* conflicts on key 2 with whoever else is there.
Overlapping == [a \in Actors |-> CASE a = 1 -> {1} [] a = 2 -> {1, 2} [] OTHER -> {2}]

\* Nobody shares a key: every commit lands.
Apart == [a \in Actors |-> {a}]

\* What thread 2 writes when it is a transaction that only reads: nothing.
\* Everybody else writes key 1.
OnlyOneWrites == [a \in Actors |-> IF a = 2 THEN {} ELSE {1}]

\* Everybody read key 1.
AllReadOne == [a \in Actors |-> {1}]

====
