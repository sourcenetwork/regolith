---- MODULE CommitPipelineSteps ----
\* The lock-free commit pipeline: its steps, one action each, in the order
\* a commit meets them. The state they act on is in
\* CommitPipelineBase.tla, and what must be true of them, with the whole
\* story of the model, in CommitPipeline.tla.

\* The state and the helpers.
EXTENDS CommitPipelineBase

\* Actions. Each is one small step of one thread: an add, a
\* compare-and-swap, a write that is safe to repeat, or a store.

\* The start: an empty ring and an empty database.
Init ==
  \* No ticket has been handed out.
  /\ tail     = 0
  \* Every cell is free.
  /\ cell     = [i \in Slots |-> "free"]
  \* Nobody owns a ticket.
  /\ owner    = [i \in Slots |-> 0]
  \* No order has a verdict.
  /\ dec      = [i \in Slots |-> "none"]
  \* No order has a sequence.
  /\ sq       = [i \in Slots |-> 0]
  \* No verdict has an epoch.
  /\ ep       = [i \in Slots |-> 0]
  \* Nothing is in the memtable.
  /\ ap       = [i \in Slots |-> FALSE]
  \* Nothing is in the log.
  /\ wr       = [i \in Slots |-> FALSE]
  \* No write is in flight.
  /\ fly      = [a \in Actors |-> {}]
  \* Nobody holds the write claim.
  /\ claim    = 0
  \* Nobody is parked on a write.
  /\ asleep   = {}
  \* Nothing was thrown out.
  /\ failed   = [i \in Slots |-> FALSE]
  \* No record belongs to a log yet.
  /\ logOf    = [i \in Slots |-> 0]
  \* No verdict names a memtable yet.
  /\ memOf    = [i \in Slots |-> 0]
  \* Nothing is decided.
  /\ dto      = 0
  \* No rollback is running.
  /\ frozen   = FALSE
  \* The tip is "before the first ticket"...
  /\ tipIdx   = 0
  \* ...with no sequence handed out...
  /\ tipNext  = 0
  \* ...and an empty memtable.
  /\ tipUsed  = 0
  \* No rollback has happened: the pipeline is of epoch zero...
  /\ epoch    = 0
  \* ...the log takes records of epoch zero...
  /\ logEp    = 0
  \* ...and the memtable is the first one.
  /\ memGen   = 0
  \* The first log.
  /\ gen      = 0
  \* Nothing is safe on disk.
  /\ durable  = 0
  \* Nothing is finished.
  /\ pub      = 0
  \* A reader sees nothing.
  /\ visible  = 0
  \* Nobody holds the round.
  /\ round    = {}
  \* No sync is under way.
  /\ target   = [a \in Actors |-> 0]
  \* Nobody claimed a unit.
  /\ claimant = 0
  \* No rollback is running.
  /\ rbLast   = 0
  \* The log is healthy.
  /\ poisoned = FALSE
  \* Nothing has failed.
  /\ fails    = 0
  \* Nobody has started.
  /\ pc       = [a \in Actors |-> "idle"]
  \* No transaction has a snapshot.
  /\ snap     = [a \in Actors |-> 0]
  \* No early check has run.
  /\ hor      = [a \in Actors |-> 0]
  \* Nobody holds a ticket.
  /\ mine     = [a \in Actors |-> 0]
  \* Nobody has read the tip.
  /\ seen     = [a \in Actors |-> NoNote]
  \* Nobody has walked away.
  /\ stopped  = {}

\* Transaction a begins, as a step of its own: it reads at what is visible
\* now, and will ask to commit later.
Begin(a) ==
  \* It is one of the transactions that begin early, and has not begun.
  /\ a \in EarlyBegin /\ pc[a] = "idle"
  \* Its snapshot is the newest sequence a reader may see (a transaction
  \* that shares no key with anybody is never checked, so none is kept).
  /\ snap' = [snap EXCEPT ![a] = IF Contends(a) THEN visible ELSE snap[a]]
  \* It is open.
  /\ pc'   = [pc EXCEPT ![a] = "open"]
  \* Nothing else changes.
  /\ UNCHANGED <<flyVars, ringVars, decVars, ap, wr, failed, dto, tipVars, epochVars, durable, pub, visible,
                 claimVars, failVars, hor, mine, seen, stopped>>

\* Transaction a asks to commit, and its own early check finds that
\* something visible changed one of its keys since it began: it aborts at
\* once, on its own thread, and takes no ticket.
EarlyAbort(a) ==
  \* It is open: it began and has not committed.
  /\ pc[a] = "open"
  \* The early check finds a conflict.
  /\ EarlyConflict(a)
  \* Its call returns with the conflict.
  /\ pc' = [pc EXCEPT ![a] = "aborted"]
  \* Nothing else changes.
  /\ UNCHANGED <<flyVars, ringVars, decVars, ap, wr, failed, dto, tipVars, epochVars, durable, pub, visible,
                 claimVars, failVars, snap, hor, mine, seen, stopped>>

\* Thread a pulls the next ticket: one add on the tail. A transaction
\* that has not begun yet begins here, reading at what is visible now; one
\* that began early has just passed its early check.
Reserve(a) ==
  \* The ticket it is about to get.
  LET i == tail + 1
  \* It has not started, or its last ticket was thrown away, or it is open
  \* and its early check found nothing.
  IN /\ \/ pc[a] = "begun"
        \* (A transaction that begins early does not start here.)
        \/ pc[a] = "idle" /\ a \notin EarlyBegin
        \* (The early check is the step before this one.)
        \/ pc[a] = "open" /\ ~EarlyConflict(a)
     \* The machine still has tickets in this run.
     /\ tail < MaxSlots
     \* A run that names who is first in line gives that thread ticket 1.
     /\ (tail = 0 /\ Head # 0 => a = Head)
     \* The machine moves on by one.
     /\ tail'  = i
     \* The ticket is this thread's.
     /\ owner' = [owner EXCEPT ![i] = a]
     \* The cell is claimed, with no order in it yet.
     /\ cell'  = [cell EXCEPT ![i] = "claimed"]
     \* The thread remembers its ticket.
     /\ mine'  = [mine EXCEPT ![a] = i]
     \* A transaction that starts here takes its snapshot; any other keeps
     \* the one it has. (One that shares no key with anybody is never
     \* checked against anything, so the model keeps no snapshot for it.)
     /\ snap'  = [snap EXCEPT ![a] = IF pc[a] = "idle" /\ Contends(a) THEN visible ELSE snap[a]]
     \* Its early check has covered everything visible now; a thread that
     \* pulls again keeps the horizon it had.
     /\ hor'   = [hor EXCEPT ![a] = IF pc[a] # "begun" /\ Contends(a) THEN visible ELSE hor[a]]
     \* It now has to write its order down.
     /\ pc'    = [pc EXCEPT ![a] = "claimed"]
     \* Nothing else changes.
     /\ UNCHANGED <<flyVars, decVars, ap, wr, failed, dto, tipVars, epochVars, durable, pub, visible,
                    claimVars, failVars, seen, stopped>>

\* Thread a writes its order into its cell: the compare-and-swap wins.
Fill(a) ==
  \* It holds a ticket with no order in it.
  /\ pc[a] = "claimed"
  \* Nobody threw the ticket away in the meantime.
  /\ cell[mine[a]] = "claimed"
  \* The order is in the cell.
  /\ cell' = [cell EXCEPT ![mine[a]] = "ready"]
  \* From now on the thread helps.
  /\ pc'   = [pc EXCEPT ![a] = "ready"]
  \* Nothing else changes.
  /\ UNCHANGED <<flyVars, tail, owner, decVars, ap, wr, failed, dto, tipVars, epochVars, durable, pub,
                 visible, claimVars, failVars, snap, hor, mine, seen, stopped>>

\* Thread a finds its ticket was thrown away: it must pull another one.
Retry(a) ==
  \* It was about to write its order down...
  /\ pc[a] = "claimed"
  \* ...but a helper voided the cell first.
  /\ cell[mine[a]] = "void"
  \* Back to the ticket machine, with the same snapshot.
  /\ pc' = [pc EXCEPT ![a] = "begun"]
  \* Nothing else changes.
  /\ UNCHANGED <<flyVars, ringVars, decVars, ap, wr, failed, dto, tipVars, epochVars, durable, pub, visible,
                 claimVars, failVars, snap, hor, mine, seen, stopped>>

\* Helper a reaches the next ticket in line and finds no order on it: its
\* owner pulled it and went no further. The helper throws it away, which
\* also settles it. Mutant NoHelping never does this; mutant VoidNotCas
\* throws away a ticket whose order is already written.
Void(a) ==
  \* The next ticket in line.
  LET i == dto + 1
  \* The broken "nobody helps" version has no such step.
  IN /\ Mutant # "NoHelping"
     \* The thread is helping, and not parked behind a claimed unit...
     /\ Helping(a) /\ ~Parked(a)
     \* ...and the ticket is ahead of its own.
     /\ i < mine[a]
     \* No rollback holds the frontier.
     /\ ~frozen
     \* The cell has a ticket and no order...
     /\ \/ cell[i] = "claimed"
        \* ...(the broken version does not look, and also takes one whose
        \* order is in but not yet decided).
        \/ Mutant = "VoidNotCas" /\ cell[i] = "ready" /\ dec[i] = "none"
     \* The ticket is thrown away.
     /\ cell' = [cell EXCEPT ![i] = "void"]
     \* The line moves past it.
     /\ dto'  = i
     \* Nothing else changes.
     /\ UNCHANGED <<flyVars, tail, owner, decVars, ap, wr, failed, tipVars, epochVars, durable, pub, visible,
                    claimVars, failVars, threadVars>>

\* Thread a looks at the next order in line and notes down the tip: the
\* state it will work the verdict out from. (A thread that dawdles between
\* this and writing the verdict matters only if a rollback can fall in
\* between. A configuration that sets Coarse takes the two as one step,
\* DecideNow, once no rollback can.)
ReadTip(a) ==
  \* The next order can be decided by this thread.
  /\ CanDecide(a)
  \* The steps are taken one by one.
  /\ SmallSteps
  \* The thread is not in the middle of another verdict.
  /\ seen[a] = NoNote
  \* It notes the ticket, the last sequence, the epoch and the memtable.
  /\ seen' = [seen EXCEPT ![a] = <<DecideSlot(a), tipNext, epoch, memGen>>]
  \* Nothing else changes.
  /\ UNCHANGED <<flyVars, ringVars, decVars, ap, wr, failed, dto, tipVars, epochVars, durable, pub,
                 visible, claimVars, failVars, pc, snap, hor, mine, stopped>>

\* Thread a writes the verdict it worked out from its note, with one
\* compare-and-swap: if another thread's verdict is already there, that one
\* stands and this one is dropped. A commit takes the next sequence; an
\* abort takes nothing (mutant AbortHole: it takes one too).
DecideCas(a) ==
  \* What the thread's note says. The ticket it is for...
  LET i  == seen[a][1]
      \* ...the last sequence handed out when it was made...
      nx == seen[a][2]
      \* ...the pipeline's epoch then...
      e  == seen[a][3]
      \* ...and the memtable in use then.
      m  == seen[a][4]
  \* The thread has a note.
  IN /\ seen[a] # NoNote
     \* It is still here.
     /\ Live(a)
     \* If there is no verdict yet, this one is written...
     /\ IF dec[i] = "none"
          \* ...commit or abort...
          THEN /\ dec'   = [dec EXCEPT ![i] = VerdictOf(i, nx)]
               \* ...with the next sequence if it takes one...
               /\ sq'    = [sq EXCEPT ![i] = SeqOf(i, nx)]
               \* ...stamped with the epoch of the state it came from...
               /\ ep'    = [ep EXCEPT ![i] = e]
               \* ...its record belongs to the current log...
               /\ logOf' = [logOf EXCEPT ![i] = gen]
               \* ...and its writes go to the memtable the note names.
               /\ memOf' = [memOf EXCEPT ![i] = m]
          \* Otherwise the other thread's verdict stands.
          ELSE UNCHANGED decVars
     \* Every note for this ticket is used up: the others would lose the
     \* compare-and-swap, which changes nothing.
     /\ seen' = [b \in Actors |-> IF seen[b][1] = i THEN NoNote ELSE seen[b]]
     \* Nothing else changes.
     /\ UNCHANGED <<flyVars, ringVars, ap, wr, failed, dto, tipVars, epochVars, durable, pub, visible,
                    claimVars, failVars, pc, snap, hor, mine, stopped>>

\* Thread a decides the next order in one go, when no rollback can fall
\* between the steps: the verdict, its writes into the memtable, the tip
\* and the frontier.
DecideNow(a) ==
  \* The ticket to decide: the next in line.
  LET i == DecideSlot(a)
  \* The next order can be decided by this thread.
  IN /\ CanDecide(a)
     \* The steps are taken in one go.
     /\ ~SmallSteps
     \* The verdict is written: commit or abort...
     /\ dec'     = [dec EXCEPT ![i] = VerdictOf(i, tipNext)]
     \* ...with the next sequence if it takes one...
     /\ sq'      = [sq EXCEPT ![i] = SeqOf(i, tipNext)]
     \* ...of the current state...
     /\ ep'      = [ep EXCEPT ![i] = epoch]
     \* ...of the current log...
     /\ logOf'   = [logOf EXCEPT ![i] = gen]
     \* ...and of the current memtable.
     /\ memOf'   = [memOf EXCEPT ![i] = memGen]
     \* A commit's writes, if it brought any, go into the memtable.
     /\ ap'      = [ap EXCEPT ![i] = ~Loses(i, tipNext) /\ Writes[owner[i]] # {}]
     \* The tip is this order...
     /\ tipIdx'  = i
     \* ...with the sequence it took, if any, the last handed out...
     /\ tipNext' = IF SeqOf(i, tipNext) # 0 THEN SeqOf(i, tipNext) ELSE tipNext
     \* ...and a commit that brought writes charged to the memtable.
     /\ tipUsed' = IF ~Loses(i, tipNext) /\ Writes[owner[i]] # {} THEN tipUsed + 1 ELSE tipUsed
     \* The line moves past it.
     /\ dto'     = i
     \* A note another thread made for this ticket before the last rollback
     \* is used up: its compare-and-swap would lose.
     /\ seen'    = [b \in Actors |-> IF seen[b][1] = i THEN NoNote ELSE seen[b]]
     \* Nothing else changes.
     /\ UNCHANGED <<flyVars, ringVars, wr, failed, epochVars, durable, pub, visible, claimVars, failVars,
                    pc, snap, hor, mine, stopped>>

\* Thread a puts order i's writes into the memtable its verdict names.
\* That is the memtable readers are shown unless a rollback replaced it
\* since (the thread does not look: it may have read the tip long ago).
\* This comes before the line moves past the order, so the order after it
\* is checked against these writes.
Apply(a, i) ==
  \* It is a commit that brought writes...
  /\ Brings(i)
  \* ...and they are not in yet.
  /\ ~ap[i]
  \* It is the order being settled, the next in line, and the tip has not
  \* moved to it yet...
  /\ \/ i = dto + 1 /\ tipIdx < i
     \* ...(mutant PassBeforeApply: any order the line has passed too,
     \* however late).
     \/ Mutant = "PassBeforeApply" /\ i <= dto
  \* The thread may work on it.
  /\ MayWork(a, i)
  \* The writes are in the memtable the verdict names.
  /\ ap' = [ap EXCEPT ![i] = TRUE]
  \* Nothing else changes.
  /\ UNCHANGED <<flyVars, ringVars, decVars, wr, failed, dto, tipVars, epochVars, durable, pub, visible,
                 claimVars, failVars, threadVars>>

\* Thread a moves the tip to the next order's verdict: from now on the
\* pipeline's state is the state after that order. Only a verdict of the
\* current epoch may become the tip (mutant SettleAnyEpoch: any), and a
\* commit only once applied (mutant PassBeforeApply: at once).
TipMove(a) ==
  \* The order being settled.
  LET i == dto + 1
  \* It exists.
  IN /\ i <= tail
     \* It has a verdict.
     /\ dec[i] # "none"
     \* The tip is still before it.
     /\ tipIdx < i
     \* The verdict is of the current state.
     /\ (ep[i] = epoch \/ Mutant = "SettleAnyEpoch")
     \* A commit's writes are in the memtable first.
     /\ (Brings(i) => ap[i] \/ Mutant = "PassBeforeApply")
     \* The thread may work on it.
     /\ MayWork(a, i)
     \* The tip is this order now...
     /\ tipIdx'  = i
     \* ...the last sequence is the one it took, if it took one...
     /\ tipNext' = IF sq[i] # 0 THEN sq[i] ELSE tipNext
     \* ...and a commit that brought writes is charged to the memtable.
     /\ tipUsed' = IF Brings(i) THEN tipUsed + 1 ELSE tipUsed
     \* Nothing else changes.
     /\ UNCHANGED <<flyVars, ringVars, decVars, ap, wr, failed, dto, epochVars, durable, pub, visible,
                    claimVars, failVars, threadVars>>

\* Thread a finds the next order's verdict came from a state a rollback
\* has since thrown away: nothing of it may be used, so the order is
\* failed. (Mutant SettleAnyEpoch never notices.)
MarkStale(a) ==
  \* The order being settled.
  LET i == dto + 1
  \* It exists.
  IN /\ i <= tail
     \* It has a verdict...
     /\ dec[i] # "none"
     \* ...the tip is still before it...
     /\ tipIdx < i
     \* ...and the verdict's epoch is not the current one.
     /\ ep[i] # epoch
     \* The broken version skips this check.
     /\ Mutant # "SettleAnyEpoch"
     \* It is not failed already.
     /\ ~failed[i]
     \* The thread may work on it.
     /\ MayWork(a, i)
     \* The order is thrown out.
     /\ failed' = [failed EXCEPT ![i] = TRUE]
     \* Nothing else changes.
     /\ UNCHANGED <<flyVars, ringVars, decVars, ap, wr, dto, tipVars, epochVars, durable, pub, visible,
                    claimVars, failVars, threadVars>>

\* Thread a moves the line past the next order: it is settled, either as
\* the tip or as a failed order.
Pass(a) ==
  \* The order being settled.
  LET i == dto + 1
  \* It exists.
  IN /\ i <= tail
     \* No rollback holds the frontier.
     /\ ~frozen
     \* It has a verdict.
     /\ dec[i] # "none"
     \* The tip reached it, or it was thrown out.
     /\ (tipIdx >= i \/ failed[i])
     \* The thread may work on it.
     /\ MayWork(a, i)
     \* The line moves past it.
     /\ dto' = i
     \* Nothing else changes.
     /\ UNCHANGED <<flyVars, ringVars, decVars, ap, wr, failed, tipVars, epochVars, durable, pub, visible,
                    claimVars, failVars, threadVars>>

\* Order i's record may be written by thread a. A thread writes its own
\* record, and the record of the next order to finish; the round's holder,
\* before it syncs, writes every record the pipeline's state covers.
CanWrite(a, i) ==
  \* The order is a commit with a record, and the record is not written.
  /\ Brings(i) /\ ~wr[i]
  \* The epoch gate: the record was placed in the log's current epoch
  \* (mutant NoEpochGate: any epoch).
  /\ (ep[i] = logEp \/ Mutant = "NoEpochGate")
  \* The thread is still here.
  /\ Live(a)
  \* Either it holds the round of a healthy log, has not begun its sync,
  \* and the order is one the pipeline's state covers...
  /\ \/ a \in round /\ target[a] = 0 /\ ~poisoned /\ rbLast = 0 /\ i <= Covered
     \* ...or the order is settled, the thread may work on it, and it is
     \* the thread's own or the next to finish.
     \/ i <= dto /\ MayWork(a, i) /\ (i = mine[a] \/ i = pub + 1)

\* Thread a writes order i's record into the log at its place, in one step.
Write(a, i) ==
  \* Writes are not taken in two steps in this run.
  /\ ~Copies
  \* The record may be written.
  /\ CanWrite(a, i)
  \* The record is in the log.
  /\ wr' = [wr EXCEPT ![i] = TRUE]
  \* Nothing else changes.
  /\ UNCHANGED <<flyVars, ringVars, decVars, ap, failed, dto, tipVars, epochVars, durable, pub, visible,
                 claimVars, failVars, threadVars>>

\* With copies, the first of a write's two steps: thread a counts in at the
\* log's gate and looks again at whether order i's record is written (WG4).
\* It is not, so the write goes ahead: from here its bytes are on their way
\* to the host. Its owner and a helper may both be here for one record.
WriteStart(a, i) ==
  \* Writes take two steps in this run.
  /\ Copies
  \* The thread has no other write in flight.
  /\ fly[a] = {}
  \* The record may be written, and is not written yet (the look again).
  /\ CanWrite(a, i)
  \* Its write is in flight: one record, written as a copy, without the claim.
  /\ fly' = [fly EXCEPT ![a] = {i}]
  \* Nothing else changes.
  /\ UNCHANGED <<claim, asleep, ringVars, decVars, ap, wr, failed, dto, tipVars, epochVars, durable,
                 pub, visible, claimVars, failVars, threadVars>>

\* Order j's record may go into a batch: it is a commit with a record, not
\* thrown out, placed in the log's current epoch, and not written yet when
\* the batch looks, which is after its count in (W2, WG4). Mutant
\* BatchNoRecheck takes a record that is written already: the batch looked
\* before its count in, and a sync began in between.
Usable(j) == Brings(j) /\ ~failed[j] /\ ep[j] = logEp /\ (~wr[j] \/ Mutant = "BatchNoRecheck")

\* The batch that starts at order f: every settled order from f on whose
\* record may go in, as long as no record between f and it may not (W1: a
\* batch is one contiguous run; a written record in the middle ends it).
\* Orders with no record (an abort, a thrown-away ticket) take no bytes and
\* do not end it.
Gather(f) == {j \in f..dto : Usable(j) /\ \A k \in f..j : Brings(k) => Usable(k)}

\* With copies, thread a takes the log's write claim in the step that counts
\* its write in (WG6), and gathers a batch: from the first settled order
\* past the published frontier whose record may be written, every record
\* after it in one run. The batch may hold records of orders after the
\* thread's own: one batch past its own at most (P5). Tiny example: orders
\* 1 and 2 are decided and neither record is written; thread 2 writes both
\* with one write while thread 1 sleeps until its record is in.
BatchStart(a) ==
  \* Writes take two steps in this run, and nobody holds the claim.
  /\ Copies /\ claim = 0
  \* The thread has no write in flight, and a record it may write now.
  /\ fly[a] = {} /\ \E i \in Slots : CanWrite(a, i)
  \* The first record that may go in a batch...
  /\ LET firsts == {j \in (pub + 1)..dto : Usable(j)}
     \* ...exists, and the batch starts there.
     IN /\ firsts # {}
        \* The batch is in flight...
        /\ fly'   = [fly EXCEPT ![a] = Gather(Min(firsts))]
        \* ...and the claim is the thread's.
        /\ claim' = a
  \* Nothing else changes.
  /\ UNCHANGED <<asleep, ringVars, decVars, ap, wr, failed, dto, tipVars, epochVars, durable, pub,
                 visible, claimVars, failVars, threadVars>>

\* Thread a needs its own record written, finds the claim held by another
\* thread whose batch holds that record, and parks: the record's write is
\* device I/O under way. A record the batch does not hold, the thread
\* writes itself after a short wait (write_stage.rs), which the model takes
\* as no park at all: a wait that ends by itself changes nothing. Mutant
\* ParkUncovered parks on a record the batch does not hold, with nothing to
\* end the wait but that record being written.
Park(a) ==
  \* Writes take two steps in this run; the thread is helping, holds
  \* neither the round nor a unit, and has no write in flight.
  /\ Copies /\ Helping(a) /\ a \notin round /\ claimant # a /\ fly[a] = {}
  \* Another thread holds the claim.
  /\ claim # 0 /\ claim # a
  \* Its own record is settled and not written.
  /\ Brings(mine[a]) /\ ~wr[mine[a]] /\ mine[a] <= dto
  \* The batch under way holds it (the broken version does not look).
  /\ IF Mutant = "ParkUncovered" THEN TRUE ELSE mine[a] \in fly[claim]
  \* The thread sleeps.
  /\ asleep' = asleep \cup {a}
  \* Nothing else changes.
  /\ UNCHANGED <<fly, claim, ringVars, decVars, ap, wr, failed, dto, tipVars, epochVars, durable,
                 pub, visible, claimVars, failVars, threadVars>>

\* Thread a wakes: its record is written (the batch marked it, which wakes
\* whoever sleeps on it), or its order was thrown out. In the design it also
\* wakes when the claim is let go or the batch does not hold its record (the
\* hand-on and the end of the short wait); the broken version waits only
\* for its record.
Wake(a) ==
  \* It sleeps, and has not walked away.
  /\ a \in asleep /\ Live(a)
  \* Its record is in, or its order is gone, or (in the design) the claim
  \* is free or its record is not in the batch. An IF, not an or: TLC tries
  \* every branch of an or in a step, and fly[0] is no value.
  /\ IF wr[mine[a]] \/ failed[mine[a]] THEN TRUE
     \* The broken version waits for nothing else.
     ELSE IF Mutant = "ParkUncovered" THEN FALSE
     \* The claim was let go: the hand-on wakes the next writer.
     ELSE IF claim = 0 THEN TRUE
     \* The batch does not hold its record: the short wait ends.
     ELSE mine[a] \notin fly[claim]
  \* It is awake.
  /\ asleep' = asleep \ {a}
  \* Nothing else changes.
  /\ UNCHANGED <<fly, claim, ringVars, decVars, ap, wr, failed, dto, tipVars, epochVars, durable,
                 pub, visible, claimVars, failVars, threadVars>>

\* The second step: thread a's write lands, and its records are in the
\* log, whoever's copy got there first. They are marked written before the
\* count out (W3), and the count out lets the claim go.
WriteLand(a) ==
  \* The thread has a write in flight.
  /\ fly[a] # {}
  \* Every record of it is in the log.
  /\ wr'    = [j \in Slots |-> wr[j] \/ j \in fly[a]]
  \* The write is over.
  /\ fly'   = [fly EXCEPT ![a] = {}]
  \* A batch lets the claim go with its count out.
  /\ claim' = IF claim = a THEN 0 ELSE claim
  \* Nothing else changes.
  /\ UNCHANGED <<asleep, ringVars, decVars, ap, failed, dto, tipVars, epochVars, durable, pub, visible,
                 claimVars, failVars, threadVars>>

\* Thread a writes order i's record and the device says no: the log is
\* poisoned, and nothing may vouch for it until it is rolled back.
WriteFail(a, i) ==
  \* The record was about to be written.
  /\ CanWrite(a, i)
  \* The run still has a failure to spend.
  /\ fails < MaxFails
  \* The log is poisoned.
  /\ poisoned' = TRUE
  \* One more failure happened.
  /\ fails'    = fails + 1
  \* Nothing else changes: the record is not in the log.
  /\ UNCHANGED <<flyVars, ringVars, decVars, ap, wr, failed, dto, tipVars, epochVars, durable, pub, visible,
                 claimVars, rbLast, frozen, threadVars>>

\* Thread a has a reason to claim the round: the next order to finish is a
\* commit that cannot be finished as it stands, because it waits for a
\* sync or because the log failed; or the thread claimed a unit, the
\* pipeline is drained, and the log failed (the unit rolls it back first).
WantsRound(a) ==
  \* The order after the published frontier.
  LET p == pub + 1
  \* It is settled, and the thread may work on it...
  IN \/ /\ p <= dto /\ MayWork(a, p)
        \* ...it is a commit that is not publishable...
        /\ dec[p] = "commit" /\ ~Publishable(p)
        \* ...and it is written (so it waits for a sync) or the log failed.
        /\ (wr[p] \/ poisoned)
     \* Or: the thread's unit waits for a failed log to be rolled back.
     \/ claimant = a /\ Live(a) /\ poisoned /\ pub = dto

\* Thread a claims the round: it will do the log's device step. One
\* compare-and-swap, so one holder at a time (mutant TwoSyncs: a load and a
\* store, so two).
ClaimRound(a) ==
  \* The thread has a reason to.
  /\ WantsRound(a)
  \* Nobody holds the round (the broken version does not check).
  /\ (round = {} \/ Mutant = "TwoSyncs")
  \* This thread does not hold it already.
  /\ a \notin round
  \* Now it does.
  /\ round' = round \cup {a}
  \* Nothing else changes.
  /\ UNCHANGED <<flyVars, ringVars, decVars, ap, wr, failed, dto, tipVars, epochVars, durable, pub, visible,
                 target, claimant, failVars, threadVars>>

\* The round's holder starts the sync: it works out how far the log is
\* written with no gap, and will vouch for exactly that.
SyncBegin(a) ==
  \* The thread holds the round and has no sync under way.
  /\ a \in round /\ target[a] = 0
  \* The log is healthy.
  /\ ~poisoned
  \* There is something to make safe.
  /\ SyncTarget > durable
  \* No write still in flight is of a record it will vouch for: it waited
  \* for those to land (WG4; mutant SyncNoWait does not wait). An IF, not an
  \* or: TLC tries every branch of an or in a step, the order of one too.
  /\ \/ Mutant = "SyncNoWait"
     \* The real code.
     \/ \A b \in Actors : \A j \in fly[b] : sq[j] > SyncTarget
  \* It notes how far it will vouch.
  /\ target' = [target EXCEPT ![a] = SyncTarget]
  \* Nothing else changes.
  /\ UNCHANGED <<flyVars, ringVars, decVars, ap, wr, failed, dto, tipVars, epochVars, durable, pub, visible,
                 round, claimant, failVars, threadVars>>

\* The sync returns: what the holder noted is safe now. The round is free
\* again, unless the log failed meanwhile: then the holder rolls back next.
SyncOk(a) ==
  \* The thread has a sync under way.
  /\ a \in round /\ target[a] # 0
  \* The durable mark moves to what the sync vouched for.
  /\ durable' = target[a]
  \* The sync is over.
  /\ target'  = [target EXCEPT ![a] = 0]
  \* The round is given up, or kept for the rollback.
  /\ round'   = IF poisoned THEN round ELSE round \ {a}
  \* Nothing else changes.
  /\ UNCHANGED <<flyVars, ringVars, decVars, ap, wr, failed, dto, tipVars, epochVars, pub, visible, claimant,
                 failVars, threadVars>>

\* The sync returns and the device says no. The log is poisoned; the
\* holder keeps the round and rolls back next.
SyncFail(a) ==
  \* The thread has a sync under way.
  /\ a \in round /\ target[a] # 0
  \* The run still has a failure to spend.
  /\ fails < MaxFails
  \* The log is poisoned.
  /\ poisoned' = TRUE
  \* One more failure happened.
  /\ fails'    = fails + 1
  \* The sync is over, and vouched for nothing.
  /\ target'   = [target EXCEPT ![a] = 0]
  \* Nothing else changes.
  /\ UNCHANGED <<flyVars, ringVars, decVars, ap, wr, failed, dto, tipVars, epochVars, durable, pub, visible,
                 round, claimant, rbLast, frozen, threadVars>>

\* The round's holder finds nothing to do and lets the round go. In the
\* design this never happens (a round is claimed only for work, and only
\* its holder can do that work); it is here for the mutant with two
\* holders, where one finds the other did it.
RoundIdle(a) ==
  \* The thread holds the round with no sync under way...
  /\ a \in round /\ target[a] = 0
  \* ...the log is healthy and nothing waits to be made safe...
  /\ ~poisoned /\ SyncTarget <= durable
  \* ...and no rollback is running.
  /\ rbLast = 0
  \* The round is given up.
  /\ round' = round \ {a}
  \* Nothing else changes.
  /\ UNCHANGED <<flyVars, ringVars, decVars, ap, wr, failed, dto, tipVars, epochVars, durable, pub, visible,
                 target, claimant, failVars, threadVars>>

\* The rollback's first step, by the round's holder: both frontiers stop
\* (mutant NoFreeze: they do not), and the pipeline moves to a new epoch,
\* so every verdict worked out from the old state is recognisable as stale.
\* The holder notes the last ticket the old state reached.
RbFreeze(a) ==
  \* The thread holds the round with no sync under way.
  /\ a \in round /\ target[a] = 0
  \* The log failed.
  /\ poisoned
  \* No rollback has started.
  /\ rbLast = 0
  \* The frontiers stop.
  /\ frozen' = (Mutant # "NoFreeze")
  \* A new epoch begins.
  /\ epoch'  = epoch + 1
  \* The last ticket of the old state, kept as one more than it.
  /\ rbLast' = Covered + 1
  \* Nothing else changes.
  /\ UNCHANGED <<flyVars, ringVars, decVars, ap, wr, failed, dto, tipVars, logEp, memGen, gen, durable, pub,
                 visible, claimVars, poisoned, fails, threadVars>>

\* The rollback's second step: finish what can be finished, throw out the
\* rest, cut their records from the log and their writes from the
\* memtable, hand their sequences back, tell the owners, and let the
\* pipeline go on.
RbFinish(a) ==
  \* The last ticket of the old state.
  LET last == rbLast - 1
      \* (Only a broken version lets the frontier get ahead of it.)
      hi   == IF pub > last THEN pub ELSE last
      \* How far the orders can be finished as they are.
      upto == CHOOSE p \in pub..hi :
                \* Every order up to p may be finished, and the next may not.
                (\A j \in (pub + 1)..p : Publishable(j)) /\ (p = hi \/ ~Publishable(p + 1))
      \* The orders to throw out: every order past that point (mutant
      \* RollbackForgets throws none out).
      out  == IF Mutant = "RollbackForgets" THEN {}
              \* The real code: every order in the ring past that point.
              ELSE {j \in (upto + 1)..last : cell[j] = "ready"}
      \* Is the memtable replaced? Always (mutant KeepMemtable: only when
      \* an order being thrown out had written to it).
      swap == Mutant # "KeepMemtable" \/ \E j \in out : InMem(j)
  \* The thread holds the round...
  IN /\ a \in round
     \* ...and its rollback is under way.
     /\ rbLast # 0
     \* The writes in flight have landed: it cuts the log only after (WG2).
     /\ \A b \in Actors : fly[b] = {}
     \* The publishable orders are finished here: readers see them.
     /\ visible' = Max({visible, SeqUpTo(upto)})
     \* The rest are thrown out.
     /\ failed'  = [j \in Slots |-> failed[j] \/ j \in out]
     \* Readers are shown a new memtable from now on...
     /\ memGen'  = IF swap THEN memGen + 1 ELSE memGen
     \* ...into which the rebuild copied the orders up to that point and
     \* nothing past it.
     /\ memOf'   = [j \in Slots |-> IF swap /\ j <= upto /\ InMem(j) THEN memGen + 1 ELSE memOf[j]]
     \* The log is cut back to that point...
     /\ wr'      = [j \in Slots |-> wr[j] /\ j <= upto]
     \* ...and turns away every record placed before now.
     /\ logEp'   = epoch
     \* The tip is the state after the last finished order...
     /\ tipIdx'  = last
     \* ...so the sequences of the thrown-out orders are handed out again.
     /\ tipNext' = IF Mutant = "RollbackForgets" THEN tipNext ELSE SeqUpTo(upto)
     \* The decided frontier jumps past everything the rollback dealt with...
     /\ dto'     = hi
     \* ...and so does the published one.
     /\ pub'     = hi
     \* Every owner the frontier passed is told: "failed" if thrown out.
     /\ pc'      = [b \in Actors |->
                      IF pc[b] = "ready" /\ Live(b) /\ mine[b] > pub /\ mine[b] <= hi
                        THEN ToldAs(failed[mine[b]] \/ mine[b] \in out)
                        ELSE pc[b]]
     \* The frontiers move again.
     /\ frozen'  = FALSE
     \* The log is healthy again.
     /\ poisoned' = FALSE
     \* The rollback is over.
     /\ rbLast'  = 0
     \* The round is given up.
     /\ round'   = round \ {a}
     \* Nothing else changes.
     /\ UNCHANGED <<flyVars, ringVars, dec, sq, ep, logOf, ap, tipUsed, epoch, gen, durable, target,
                    claimant, fails, snap, hor, mine, seen, stopped>>

\* Thread a raises the read horizon to the next order's sequence: the
\* first half of publishing it.
PubHorizon(a) ==
  \* The order after the published frontier.
  LET p == pub + 1
  \* It is decided and settled.
  IN /\ p <= dto
     \* The steps are taken one by one.
     /\ SmallSteps
     \* No rollback holds the frontier.
     /\ ~frozen
     \* It may be finished.
     /\ Publishable(p)
     \* It holds a sequence readers do not see yet.
     /\ Takes(p) /\ visible < sq[p]
     \* The thread may work on it.
     /\ MayWork(a, p)
     \* Readers now see it.
     /\ visible' = sq[p]
     \* Nothing else changes.
     /\ UNCHANGED <<flyVars, ringVars, decVars, ap, wr, failed, dto, tipVars, epochVars, durable, pub,
                    claimVars, failVars, threadVars>>

\* Thread a moves the published frontier past the next order: the second
\* half. The horizon is there already (mutant FrontierFirst does not wait
\* for it), so an owner who sees its order finished can read its own write.
\* The owner's call returns: it is told "done", or "failed" if a rollback
\* threw the order out. When the steps are taken in one go, this step
\* raises the horizon too.
PubFrontier(a) ==
  \* The order after the published frontier...
  LET p == pub + 1
      \* ...and who owns it.
      o == owner[p]
  \* It is decided and settled.
  IN /\ p <= dto
     \* No rollback holds the frontier.
     /\ ~frozen
     \* It may be finished.
     /\ Publishable(p)
     \* Taken one by one: if it holds a sequence, readers see it already.
     /\ (SmallSteps /\ Takes(p) => visible >= sq[p] \/ Mutant = "FrontierFirst")
     \* The thread may work on it.
     /\ MayWork(a, p)
     \* The order is finished.
     /\ pub' = p
     \* Taken in one go: the horizon is raised here.
     /\ visible' = IF ~SmallSteps /\ Takes(p) /\ sq[p] > visible THEN sq[p] ELSE visible
     \* Its owner, if it is waiting on this very order, is told.
     /\ pc' = IF o # 0 /\ pc[o] = "ready" /\ mine[o] = p /\ Live(o)
                \* It learns "done", or "failed" for an order thrown out.
                THEN [pc EXCEPT ![o] = ToldAs(failed[p])]
                \* Nobody is waiting on it here: no thread is told.
                ELSE pc
     \* Nothing else changes.
     /\ UNCHANGED <<flyVars, ringVars, decVars, ap, wr, failed, dto, tipVars, epochVars, durable,
                    claimVars, failVars, snap, hor, mine, seen, stopped>>

\* Mutant OutOfOrder only: the horizon jumps to a later order that happens
\* to be ready, over an earlier one that is not.
PublishAny(a, i) ==
  \* Only the broken version has this step.
  /\ Mutant = "OutOfOrder"
  \* An order beyond the next one...
  /\ i > pub + 1 /\ i <= dto
  \* ...that commits and could be finished on its own...
  /\ dec[i] = "commit" /\ Takes(i) /\ Publishable(i)
  \* ...which the thread may work on...
  /\ MayWork(a, i)
  \* ...and readers do not see yet.
  /\ visible < sq[i]
  \* The horizon jumps to it.
  /\ visible' = sq[i]
  \* Nothing else changes.
  /\ UNCHANGED <<flyVars, ringVars, decVars, ap, wr, failed, dto, tipVars, epochVars, durable, pub,
                 claimVars, failVars, threadVars>>

\* Thread a claims the job at the next ticket: an ordered unit, or the
\* rotation check of a write that finds the memtable full. One
\* compare-and-swap; the thread that asked for the unit is only the
\* likeliest to win it.
ClaimNext(a) ==
  \* The next ticket holds a unit, or a write whose turn needs the check.
  /\ (NextIsUnit \/ NextIsTurn)
  \* No rollback holds the frontier.
  /\ ~frozen
  \* Nobody claimed it.
  /\ claimant = 0
  \* The thread may work on that ticket.
  /\ MayWork(a, dto + 1)
  \* The job is this thread's.
  /\ claimant' = a
  \* Nothing else changes.
  /\ UNCHANGED <<flyVars, ringVars, decVars, ap, wr, failed, dto, tipVars, epochVars, durable, pub, visible,
                 round, target, failVars, threadVars>>

\* The claimant can run its job: everything before the ticket is finished,
\* nobody is on the log's device step, and the log is healthy (a failed log
\* is rolled back first).
CanRunNext(a) ==
  \* The job is this thread's, and the thread is still here.
  /\ claimant = a /\ Live(a)
  \* No rollback is running and the log is healthy.
  /\ ~frozen /\ ~poisoned
  \* Nobody holds the round: the job holds it for its own length.
  /\ round = {}
  \* No write is in flight: the job syncs the log, and waited for those
  \* first (WG4).
  /\ \A b \in Actors : fly[b] = {}
  \* The pipeline is drained up to the ticket.
  /\ Drained(dto + 1)

\* The claimant runs the ordered unit at the next ticket: an ingest's
\* install, say. It syncs the log, takes a sequence if it brings keys,
\* installs its table, and its verdict becomes the tip, all with the round
\* held, so the model takes it as one step.
UnitRun(a) ==
  \* The next ticket in line.
  LET i == dto + 1
  \* It holds a unit not yet run.
  IN /\ NextIsUnit
     \* The claimant may run it now.
     /\ CanRunNext(a)
     \* The unit ran.
     /\ dec'     = [dec EXCEPT ![i] = "unit"]
     \* It takes the next sequence if it brings keys (an ingested table
     \* reads at it); a unit that brings none takes none.
     /\ sq'      = [sq EXCEPT ![i] = IF Writes[owner[i]] # {} THEN tipNext + 1 ELSE 0]
     \* Its verdict is of the current state...
     /\ ep'      = [ep EXCEPT ![i] = epoch]
     \* ...of the current log...
     /\ logOf'   = [logOf EXCEPT ![i] = gen]
     \* ...and of the current memtable.
     /\ memOf'   = [memOf EXCEPT ![i] = memGen]
     \* Its table is installed: readers at its sequence find it.
     /\ ap'      = [ap EXCEPT ![i] = TRUE]
     \* It synced the log first: everything decided before it is safe.
     /\ durable' = IF tipNext > durable THEN tipNext ELSE durable
     \* The tip is the state the unit left...
     /\ tipIdx'  = i
     \* ...with its sequence, if any, the last handed out.
     /\ tipNext' = IF Writes[owner[i]] # {} THEN tipNext + 1 ELSE tipNext
     \* The line moves past it.
     /\ dto'     = i
     \* The job is done.
     /\ claimant' = 0
     \* Nothing else changes.
     /\ UNCHANGED <<flyVars, ringVars, wr, failed, tipUsed, epochVars, pub, visible, round, target, failVars,
                    threadVars>>

\* The claimant runs the rotation check in the turn of the write at the
\* next ticket: the full memtable is sealed behind a fresh one and a fresh
\* log, after the old log is synced to its end. The state it leaves takes
\* the tip's place, and the write is then decided from it.
TurnRun(a) ==
  \* The next ticket holds a write that finds the memtable full.
  /\ NextIsTurn
  \* The claimant may run the check now.
  /\ CanRunNext(a)
  \* The old log is synced to its end before the next one exists.
  /\ durable' = IF tipNext > durable THEN tipNext ELSE durable
  \* Commits after this go to the next log...
  /\ gen'     = gen + 1
  \* ...and to an empty memtable.
  /\ tipUsed' = 0
  \* The job is done.
  /\ claimant' = 0
  \* Nothing else changes: the write itself is decided next.
  /\ UNCHANGED <<flyVars, ringVars, decVars, ap, wr, failed, dto, tipIdx, tipNext, epoch, logEp, memGen, pub,
                 visible, round, target, failVars, threadVars>>

\* Any one step of a thread that has not walked away.
LiveStep(a) ==
  \* The thread is still here...
  /\ Live(a)
  \* ...and takes one of the steps above. A transaction beginning early:
  /\ \/ Begin(a) \/ EarlyAbort(a)
     \* Getting into the ring:
     \/ Reserve(a) \/ Fill(a) \/ Retry(a) \/ Void(a)
     \* Deciding and settling the next order:
     \/ ReadTip(a) \/ DecideCas(a) \/ DecideNow(a) \/ TipMove(a) \/ MarkStale(a) \/ Pass(a)
     \* The round: a sync...
     \/ ClaimRound(a) \/ SyncBegin(a) \/ SyncOk(a) \/ SyncFail(a) \/ RoundIdle(a)
     \* ...or a rollback. And publishing:
     \/ RbFreeze(a) \/ RbFinish(a) \/ PubHorizon(a) \/ PubFrontier(a)
     \* An ordered unit or a rotation check:
     \/ ClaimNext(a) \/ UnitRun(a) \/ TurnRun(a)
     \* The steps that name an order: applying it, writing its record.
     \/ \E i \in Slots : Apply(a, i) \/ Write(a, i) \/ WriteFail(a, i) \/ PublishAny(a, i)
     \* With copies, a write in two steps: counted in for an order, then landed.
     \/ \E i \in Slots : WriteStart(a, i)
     \* A batch under the write claim, and a park on it and the wake.
     \/ BatchStart(a) \/ Park(a) \/ Wake(a)
     \* The landing.
     \/ WriteLand(a)

\* Thread a walks away for good, anywhere in its commit: descheduled
\* forever, or its task dropped. It never does so while it holds the round
\* or a claimed unit: see WHAT IS NOT A STOPPED THREAD (mutant
\* StopHoldsClaim allows it).
Stop(a) ==
  \* The run still allows another thread to stop.
  /\ Cardinality(stopped) < MaxStops
  \* This thread is one of those that may...
  /\ a \in Stoppers
  \* ...and has not stopped yet.
  /\ a \notin stopped
  \* It is somewhere inside its commit.
  /\ pc[a] \in {"begun", "claimed", "ready"}
  \* It holds neither the round nor a claimed unit.
  /\ ((a \notin round /\ claimant # a) \/ Mutant = "StopHoldsClaim")
  \* It has no write in flight: those bytes are with the host, which
  \* finishes the write whatever the thread does next.
  /\ fly[a] = {}
  \* It is gone.
  /\ stopped' = stopped \cup {a}
  \* Nothing else changes.
  /\ UNCHANGED <<flyVars, ringVars, decVars, ap, wr, failed, dto, tipVars, epochVars, durable, pub, visible,
                 claimVars, failVars, pc, snap, hor, mine, seen>>

\* A step of some thread that is still here.
LiveNext == \E a \in Actors : LiveStep(a)

\* Every step the system can take: a live thread's step, or a thread
\* walking away.
Next == LiveNext \/ \E a \in Actors : Stop(a)

\* Every behaviour: start at Init, take steps, and as long as some live
\* thread can take a step, one of them eventually does. No single thread is
\* promised a turn: the scheduler may starve any one of them, which is the
\* scheduler lock-freedom is defined against.
Spec == Init /\ [][Next]_vars /\ WF_vars(LiveNext)

====
