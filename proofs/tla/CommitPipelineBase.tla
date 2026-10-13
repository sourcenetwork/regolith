---- MODULE CommitPipelineBase ----
\* The lock-free commit pipeline: what a configuration chooses, the state
\* of the pipeline and of each thread in it, and the small questions the
\* steps ask about that state. The steps themselves are in
\* CommitPipelineSteps.tla, and what must be true of them, with the whole
\* story of the model, in CommitPipeline.tla.

\* The model counts with whole numbers and asks how big a set is.
EXTENDS Naturals, FiniteSets

\* What a configuration chooses.
CONSTANTS
  \* The threads that commit one transaction each: positive numbers.
  Committers,
  \* The committers that are plain writes (Db::put, Db::write): no
  \* snapshot, no validation, they always land. The rest are transactions.
  Plain,
  \* The transactions that begin as a step of their own, before they
  \* commit, so that other commits can land in between. The others begin
  \* at the moment they commit.
  EarlyBegin,
  \* The threads that ask for one ordered unit each (an ingest, say).
  Units,
  \* Which keys each thread writes, as a function from thread to key set.
  \* A transaction that writes none only reads: it is checked like any
  \* other, and takes no sequence and no record.
  Writes,
  \* Which keys each transaction read and asks to have checked.
  Reads,
  \* The committers who wait until their record is on stable storage.
  Immediate,
  \* The most tickets the machine hands out in this run.
  MaxSlots,
  \* How many threads may walk away for good...
  MaxStops,
  \* ...and which threads those may be.
  Stoppers,
  \* The thread that pulls the first ticket of the run; 0 for whichever
  \* gets there first.
  Head,
  \* How many times the log may fail (a write or a sync).
  MaxFails,
  \* How many commits the memtable holds before it is rotated.
  Buffer,
  \* Whether steps nothing can fall between are taken in one go.
  Coarse,
  \* Whether a record's write takes two steps, counted in at the log's gate
  \* and landed, so a helper's copy of a record can be in flight beside its
  \* owner's (WG4). FALSE: one step, as the model was before copies.
  Copies,
  \* Which rule is deliberately broken; "none" is the real design.
  Mutant

\* Everybody who takes a ticket.
Actors == Committers \cup Units

\* Thread names are positive numbers, and nobody is both kinds.
ASSUME Actors \subseteq Nat \ {0} /\ Committers \cap Units = {}
\* Every thread has a set of keys it writes, and one it read.
ASSUME Writes \in [Actors -> SUBSET Nat] /\ Reads \in [Actors -> SUBSET Nat]
\* Only committers can ask to wait for the disk.
ASSUME Immediate \subseteq Committers
\* Plain writes are committers, and so are the transactions that begin
\* early; a plain write has no transaction to begin.
ASSUME Plain \subseteq Committers /\ EarlyBegin \subseteq Committers \ Plain
\* Only a thread of the run can walk away, or be the first in line.
ASSUME Stoppers \subseteq Actors /\ Head \in Actors \cup {0}
\* The bounds are plain counts, and the memtable holds at least one commit.
ASSUME MaxSlots \in Nat /\ MaxStops \in Nat /\ MaxFails \in Nat /\ Buffer \in Nat \ {0}
\* The switches are yes or no.
ASSUME Coarse \in BOOLEAN /\ Copies \in BOOLEAN
\* The list of rules a run may break, one at a time.
ASSUME Mutant \in {"none", "OutOfOrder", "AbortHole", "NoHelping", "SyncPastGap",
                   "ValidatePublished", "VoidNotCas", "TwoSyncs", "FrontierFirst",
                   "UnitNoDrain", "SettleAnyEpoch", "KeepMemtable", "NoEpochGate",
                   "PassBeforeApply", "RollbackForgets", "NoFreeze", "StopHoldsClaim",
                   "TrustEarly", "PublishBeforeSync", "DecideAnyOrder", "WorkBeyond",
                   "SyncNoWait", "SkipOnPublished"}

\* The ticket numbers of the run.
Slots == 1..MaxSlots

\* "Nothing read yet": what a thread's note holds before it reads the tip.
NoNote == <<0, 0, 0, 0>>

\* The state of the pipeline, and of each thread in it.
VARIABLES
  \* The last ticket number handed out.
  tail,
  \* What each cell of the ring holds: "free" (no ticket yet), "claimed"
  \* (ticket pulled, order not written down), "ready" (order written down)
  \* or "void" (ticket thrown away).
  cell,
  \* Who pulled each ticket; 0 for nobody.
  owner,
  \* The verdict on each order, written once: "none" (not yet), "commit",
  \* "abort" (it lands nothing) or "unit" (an ordered unit ran).
  dec,
  \* The sequence number each order took; 0 for none.
  sq,
  \* The epoch of the state each verdict was worked out from.
  ep,
  \* Whether each order's writes were put into the memtable its verdict
  \* names (which a rollback may since have replaced: see InMem).
  ap,
  \* Whether each order's record is in the log.
  wr,
  \* Whether each order was thrown out by a rollback.
  failed,
  \* The log generation each order's record belongs to.
  logOf,
  \* The memtable each order's verdict names, by its number.
  memOf,
  \* The decided frontier: every ticket up to here has its verdict.
  dto,
  \* Whether a rollback is holding both frontiers still.
  frozen,
  \* The tip: the ticket whose verdict is the pipeline's current state...
  tipIdx,
  \* ...the last sequence handed out in that state...
  tipNext,
  \* ...and how many commits its memtable was charged for.
  tipUsed,
  \* The pipeline's epoch: how many rollbacks have begun.
  epoch,
  \* The log's write epoch: records of any other epoch are turned away.
  logEp,
  \* The number of the memtable readers are shown: how many times a
  \* rollback has replaced it.
  memGen,
  \* The log generation commits are written to now (a rotation moves it).
  gen,
  \* The last sequence an fsync has made safe.
  durable,
  \* The published frontier: every ticket up to here is finished.
  pub,
  \* The newest sequence a reader may see.
  visible,
  \* Who holds the round, the one claim on the log's device step.
  round,
  \* How far the sync each thread has under way will vouch; 0 for no sync.
  target,
  \* Who claimed the ordered unit or the rotation check at the next
  \* ticket; 0 for nobody.
  claimant,
  \* While a rollback runs, one more than the last ticket of the state it
  \* discards from; 0 when no rollback runs.
  rbLast,
  \* Whether the log failed and has not been rolled back yet.
  poisoned,
  \* How many log failures have happened so far.
  fails,
  \* Where each thread is in its own commit: "idle" (not started), "open"
  \* (its transaction has begun and has not asked to commit), "begun" (its
  \* ticket was thrown away, it needs another), "claimed" (it holds a
  \* ticket with no order on it), "ready" (its order is in the ring),
  \* "done" or "failed" (its call returned), or "aborted" (its own early
  \* check found a conflict, and it never took a ticket).
  pc,
  \* The sequence each transaction started reading at.
  snap,
  \* The horizon each transaction's early check covered: everything
  \* visible at or below it was checked on the committer's own thread.
  hor,
  \* The ticket each thread holds now.
  mine,
  \* The note a thread made of the tip it read: <<ticket, last sequence,
  \* epoch, memtable>>.
  seen,
  \* The threads that walked away for good.
  stopped,
  \* The record whose write each thread has in flight: counted in at the
  \* log's gate, its bytes not yet with the host; 0 for none.
  fly

\* All of the above, so "nothing changed" can be said in one word.
vars == <<tail, cell, owner, dec, sq, ep, ap, wr, failed, logOf, memOf, dto, frozen, tipIdx,
          tipNext, tipUsed, epoch, logEp, memGen, gen, durable, pub, visible, round, target, claimant,
          rbLast, poisoned, fails, pc, snap, hor, mine, seen, stopped, fly>>

\* Groups of variables an action leaves alone, named once so each action
\* can say so in a line.
\* The ring's cells and who owns them.
ringVars == <<tail, cell, owner>>
\* What is decided for each order.
decVars == <<dec, sq, ep, logOf, memOf>>
\* The pipeline's state after the newest decided order.
tipVars == <<tipIdx, tipNext, tipUsed>>
\* The epochs and the log generation.
epochVars == <<epoch, logEp, memGen, gen>>
\* The round, the syncs under way and the claim on an ordered unit.
claimVars == <<round, target, claimant>>
\* The log's failure state.
failVars == <<poisoned, fails, rbLast, frozen>>
\* What each thread knows of itself.
threadVars == <<pc, snap, hor, mine, seen, stopped>>

----------------------------------------------------------------------------
\* Helpers: small questions the actions ask.

\* The biggest number in a set of numbers.
Max(S) == CHOOSE m \in S : \A n \in S : n <= m

\* Order i holds a sequence that still counts: it took one and was not
\* thrown out.
Takes(i) == sq[i] # 0 /\ ~failed[i]

\* Order i's writes are in the memtable readers are shown: they were
\* applied, and to that memtable, not to one a rollback replaced.
InMem(i) == ap[i] /\ memOf[i] = memGen

\* Order i is a commit that brought writes: it holds a sequence, and has a
\* record to write and writes to apply. (A transaction that only read
\* commits with none of those.)
Brings(i) == dec[i] = "commit" /\ sq[i] # 0

\* Order i has nothing left to do with the log: it writes no record (its
\* ticket was thrown away, it was thrown out, it aborted, or it is a unit),
\* or its record is written.
WalDone(i) ==
  \* A thrown-away ticket writes nothing.
  \/ cell[i] = "void"
  \* A thrown-out order's record was cut from the log.
  \/ failed[i]
  \* An abort and a unit write no record.
  \/ dec[i] \in {"abort", "unit"}
  \* A commit is done once its record is in the log, or at once if it
  \* brought no writes.
  \/ dec[i] = "commit" /\ (wr[i] \/ sq[i] = 0)

\* The last ticket the pipeline's state covers: the decided frontier, or
\* the tip when it has moved one ahead of the frontier.
Covered == IF tipIdx > dto THEN tipIdx ELSE dto

\* How far the log is written with no gap: the largest w such that every
\* order up to w is done with the log. A sync makes that prefix safe.
WrittenTo ==
  \* The one w with every order up to it written and the next one not.
  CHOOSE w \in 0..Covered : (\A j \in 1..w : WalDone(j)) /\ (w = Covered \/ ~WalDone(w + 1))

\* The last sequence held by an order up to ticket p that still counts.
SeqUpTo(p) == Max({0} \cup {sq[j] : j \in {k \in 1..p : Takes(k)}})

\* What a sync may promise: the last sequence in the gap-free prefix.
\* Mutant SyncPastGap promises the last sequence written anywhere.
SyncTarget ==
  \* Which promise is made?
  IF Mutant = "SyncPastGap"
    \* The mutant's: the last sequence of any written commit, gaps or not.
    THEN Max({0} \cup {sq[j] : j \in {i \in 1..Covered : Takes(i) /\ dec[i] = "commit" /\ wr[i]}})
    \* The real one: the last sequence of the written prefix.
    ELSE SeqUpTo(WrittenTo)

\* Order i may be marked finished: it has nothing to show (thrown away,
\* thrown out, an abort, or a unit), or it is a commit whose record is
\* written and, if it asked, safe on disk. Its writes are in the memtable
\* already: that happened before the next order was decided.
Publishable(i) ==
  \* A thrown-away ticket is finished at once.
  \/ cell[i] = "void"
  \* So is an order a rollback threw out: its owner only needs to be told.
  \/ failed[i]
  \* So is an abort, and a unit.
  \/ dec[i] \in {"abort", "unit"}
  \* So is a commit that brought no writes: it has no record to wait for.
  \/ dec[i] = "commit" /\ sq[i] = 0
  \* A commit that brought writes...
  \/ /\ Brings(i)
     \* ...needs its record written...
     /\ wr[i]
     \* ...and on stable storage if it asked to wait for that (mutant
     \* PublishBeforeSync does not wait).
     /\ (owner[i] \in Immediate => sq[i] <= durable \/ Mutant = "PublishBeforeSync")

\* Thread a has not walked away.
Live(a) == a \notin stopped

\* Thread a has an order in the ring that is not finished, so it helps.
Helping(a) == Live(a) /\ pc[a] = "ready"

\* Thread a stands behind an ordered unit another thread claimed: it waits
\* for that thread to finish the unit and does nothing else meanwhile.
Parked(a) == claimant # 0 /\ claimant # a /\ mine[a] > dto

\* Thread a may work on ticket i: any ticket up to its own, never beyond
\* (a thread does no work it does not need: E21). Mutant NoHelping: its own
\* only. Mutant WorkBeyond: any ticket at all, so a thread goes on with the
\* orders behind its own for as long as its own is not finished.
MayWork(a, i) ==
  \* It is helping and not waiting for a claimed unit...
  /\ Helping(a) /\ ~Parked(a)
  \* ...and the ticket is its own or an earlier one.
  /\ IF Mutant = "NoHelping" THEN mine[a] = i ELSE (i <= mine[a] \/ Mutant = "WorkBeyond")

\* A rollback can still happen: the log may still fail, or a failure is
\* being dealt with.
RollbackPossible == fails < MaxFails \/ poisoned \/ rbLast # 0

\* Whether the steps of deciding and of publishing are taken one by one
\* (see SMALL STEPS AND ONE-GO STEPS).
SmallSteps == ~Coarse \/ RollbackPossible

\* Does order i lose a conflict? Some earlier order whose writes are in the
\* memtable wrote a key its transaction read, after it began reading. The
\* memtable holds every earlier order, because each was applied before the
\* next was decided. The check is in two parts: the transaction's own early
\* check covered everything up to its horizon (EarlyConflict), and this one
\* looks above the horizon only. Mutant ValidatePublished looks at finished
\* orders only; mutant TrustEarly looks at nothing, taking the early check
\* for the whole check.
Conflict(i) ==
  \* Only a transaction is checked; a plain write and a unit are not.
  /\ owner[i] \in Committers \ Plain
  \* The broken version that trusts the early check finds nothing here.
  /\ Mutant # "TrustEarly"
  \* Look for an earlier order...
  /\ \E j \in 1..(i - 1) :
       \* ...that landed (a commit or a unit) and is in the memtable...
       /\ dec[j] \in {"commit", "unit"} /\ InMem(j) /\ ~failed[j]
       \* ...above the horizon this transaction's early check covered...
       /\ sq[j] > hor[owner[i]]
       \* ...and wrote a key this one read.
       /\ Writes[owner[j]] \cap Reads[owner[i]] # {}
       \* (The broken version only counts finished orders.)
       /\ (Mutant = "ValidatePublished" => j <= pub)

\* The early check of transaction a, on its own thread, before it takes a
\* ticket: does something readers can see, written since the transaction
\* began, touch a key it read? If so it aborts at once and takes nothing.
EarlyConflict(a) ==
  \* Look at every order decided so far...
  \E j \in 1..tipIdx :
    \* ...that holds a sequence a reader can see, in the memtable...
    /\ Takes(j) /\ InMem(j) /\ sq[j] <= visible
    \* ...taken after this transaction began reading...
    /\ sq[j] > snap[a]
    \* ...by an order that wrote a key this one read.
    /\ Writes[owner[j]] \cap Reads[a] # {}

\* Thread a is a transaction that read a key some other thread writes: the
\* only kind of thread whose snapshot is ever looked at.
Contends(a) ==
  \* A transaction, and another thread writes a key it read.
  a \in Committers \ Plain /\ \E b \in Actors \ {a} : Reads[a] \cap Writes[b] # {}

\* The ticket a thread decides: the next in line (mutant DecideAnyOrder:
\* its own, whether or not the tickets before it are decided).
DecideSlot(a) == IF Mutant = "DecideAnyOrder" THEN mine[a] ELSE dto + 1

\* Does the deciding thread skip the look above the horizon for order i?
\* It skips when nothing was handed a sequence above the horizon: nx, the
\* last sequence handed out in the tip the thread read, is at or below it
\* (RegolithEngine::validate and decide_txn, `ceiling <= early.horizon`). A
\* commit nobody committed under then finishes its check with no lookup at
\* all. Picture a baker who knows the last ticket served before yours was
\* number 5, and that you already checked the board up to number 5: there
\* is nothing newer to look at.
\* Mutant SkipOnPublished asks the published horizon instead of nx: an order
\* decided and not yet published is above the horizon but not visible, so
\* the look that would have found it is skipped.
SkipsCheck(i, nx) ==
  \* The broken version compares what readers can see...
  IF Mutant = "SkipOnPublished" THEN visible <= hor[owner[i]]
  \* ...the design compares the last sequence handed out.
  ELSE nx <= hor[owner[i]]

\* Does order i lose a conflict, decided from a tip whose last sequence is
\* nx? Only a transaction can; the skip, when it applies, finds nothing
\* above the horizon because nothing is there (ceiling_skips_the_check_above
\* in PipelineCheck.lean).
Loses(i, nx) ==
  \* A conflict above the horizon...
  /\ Conflict(i)
  \* ...that the deciding thread looks for.
  /\ ~SkipsCheck(i, nx)

\* The verdict on order i, decided from a tip whose last sequence is nx:
\* "abort" if it loses a conflict.
VerdictOf(i, nx) == IF Loses(i, nx) THEN "abort" ELSE "commit"

\* The sequence order i takes when the last one handed out is nx: the next
\* one for a commit that brings writes, none for one that only read, and
\* none for an abort (mutant AbortHole: an abort takes the next one too).
SeqOf(i, nx) ==
  \* A commit with writes, or the broken version's abort, takes one.
  IF (~Loses(i, nx) /\ Writes[owner[i]] # {}) \/ (Loses(i, nx) /\ Mutant = "AbortHole")
    \* The next one.
    THEN nx + 1
    \* Anything else takes none.
    ELSE 0

\* The next ticket in line holds an order nobody decided yet.
NextUndecided ==
  \* It has been handed out...
  /\ dto < tail
  \* ...its order is written down...
  /\ cell[dto + 1] = "ready"
  \* ...and it has no verdict.
  /\ dec[dto + 1] = "none"

\* The next order is an ordered unit waiting to run.
NextIsUnit == NextUndecided /\ owner[dto + 1] \in Units

\* The next order is a write that finds the memtable full: the rotation
\* check runs first, in that write's turn.
NextIsTurn == NextUndecided /\ owner[dto + 1] \in Committers /\ tipUsed >= Buffer

\* The order thread a would decide is a write the memtable has room for:
\* it can be decided now, if a may work on it.
CanDecide(a) ==
  \* The ticket to decide: the next in line.
  LET i == DecideSlot(a)
  \* It has been handed out, holds an order, and has no verdict.
  IN /\ i >= 1 /\ i <= tail /\ cell[i] = "ready" /\ dec[i] = "none"
     \* No rollback holds the frontier: the slot really is next.
     /\ ~frozen
     \* It is a commit (a unit is run, not decided: UnitRun)...
     /\ owner[i] \in Committers
     \* ...and the memtable has room (else the rotation check runs first).
     /\ tipUsed < Buffer
     \* The thread may work on it.
     /\ MayWork(a, i)

\* Everything before ticket i is finished: the pipeline is drained up to i.
\* Mutant UnitNoDrain does not wait for that.
Drained(i) == pub = i - 1 \/ Mutant = "UnitNoDrain"

\* What the owner of a finished order is told, given who was thrown out.
ToldAs(isFailed) == IF isFailed THEN "failed" ELSE "done"

====
