---- MODULE NonBlocking ----
\* ===========================================================================
\* THE STORY
\* ===========================================================================
\* regolith reads a table block from the disk when a reader needs it and the
\* block cache does not hold it. A thread that must never block cannot wait
\* for that disk read. So each such thread holds its own "I/O queue" (an
\* IoQueue in src/io_queue/queue.rs), and reads through a CacheOnly handle:
\*   - the read looks in the cache; on a miss it does NOT touch the disk.
\*     It records the block on its own queue and returns WouldBlock at once;
\*   - later, when the thread has nothing else to do, it polls its queue.
\*     The poll does the disk reads its thread is waiting for, and hands
\*     every waiting read a "you can run again now" note;
\*   - the read runs again and finds its block.
\*
\* Tiny example. Two threads, A and B, both miss block 7 at the same moment.
\* There is ONE "unit" for block 7 (a single-flight read, src/engine/io/unit.rs).
\* A polls first and grabs the unit with one compare-and-swap; B's poll sees
\* it taken and leaves it alone. A reads block 7 once, then puts one "done"
\* note into A's inbox and one into B's inbox. B was asleep ("idle"), so the
\* note to B also wakes B up. A was awake, so nothing wakes A: it just finds
\* the note at its next poll.
\*
\* What can go wrong, and what this model checks cannot happen:
\*   - a note lands in the wrong thread's inbox, so the wrong thread finishes
\*     a read and the right one never hears (OwnQueue);
\*   - a thread is told twice, or a thread that asked is never told
\*     (ExactlyOnce, EveryWaiterTold);
\*   - two threads both grab the same unit and read the block twice
\*     (SingleRun);
\*   - a thread goes to sleep right as a note arrives and sleeps forever with
\*     a note in its inbox (NoLostIdleWakeup);
\*   - a thread that is busy gets woken anyway (BusyNeverWoken);
\*   - some I/O regolith starts by itself is put on nobody's queue, so it
\*     never runs (NoOrphanUnit);
\*   - and, over whole runs: every read and every job finishes, with many
\*     threads or with one (the single-threaded wasm case) (AllDone).
\*
\* THE COMMIT SIDE (commit units). Writes take the same path:
\*   - a group of commits made by commit_nowait that needs an fsync is
\*     written and left as ONE unit, the group's fsync. Each member's commit
\*     puts a note for it on its OWN queue; the first member to poll claims
\*     it with one CAS and runs the fsync; every member's queue is told once.
\*     Any thread that takes the commit pipeline next may land it too
\*     (LandHere), and close lands it. Tiny example: threads A and B commit
\*     into group 4; B polls first, syncs once, and the note to A wakes A.
\*     What can go wrong: the fsync runs twice (SingleRun), the commits are
\*     visible before the fsync (VisibleAfterSync), or B's poll makes A's
\*     ticket ready on B's thread instead of at A's own poll
\*     (DeliveredOnOwnPoll);
\*   - a write a stall stops returns at once with a wait; every writer
\*     stopped during one stall waits on one PASSIVE unit, which no poll
\*     runs and which lands only when the stall clears. A writer installs
\*     or finds the unit, registers on its own queue, and only then looks at
\*     the stall again, landing the unit itself if it cleared meanwhile.
\*     What can go wrong: a writer installs the unit just after the clearer
\*     looked, and nobody ever lands it (StallLandsWhenClear).
\*
\* WHAT IS MODELLED, and the code each piece mirrors:
\*   unit        a single-flight read: Unit, src/engine/io/unit.rs
\*   table       the unit table: IoRuntime::units, src/engine/io/mod.rs
\*   inbox       a queue's lock-free inbox: QueueShared::inbox,
\*               src/engine/io/shared.rs, a Stack with an IDLE flag bit
\*   waiting     the units a queue registered on: IoQueue::waiting
\*   slot        one read's wait: WaitSlot, behind each IoWait
\*   have        what a re-run read finds for its queue: the reads that
\*               landed for the queue (QueueShared::landed). The block cache
\*               is left out on purpose: it only ever makes a re-run find its
\*               block sooner, so this is the hard case, the one where only
\*               the landing carries the read (a disabled cache).
\*
\* WHAT IS LEFT OUT, and why that loses nothing:
\*   - Memory ordering and the exact CAS loops: the loom models check those
\*     (tests/loom_io_queue.rs). Here each CAS is one atomic step.
\*   - The byte bound on a queue: it delays a read (a "room" wait) but never
\*     changes who is told what.
\*   - A dropped queue: it releases its units exactly as close does (Release
\*     below), so it adds no new kind of step.
\*   - Read failures: a failed unit is told to its waiters like a landed one;
\*     only what lands differs.
\*   - Jobs (I/O regolith starts itself: the flush or the bounded step a
\*     write leaves owing with no worker, the disk check, compact_range,
\*     an ingest or a checkpoint run on the caller's queue) take the very
\*     same path as a read's miss (a unit, a request on the starting
\*     thread's own queue, src/engine/io/job.rs); SelfStart stands for all
\*     of them.
\*   - What a group's fsync writes and applies: GroupCommit.tla checks the
\*     group's contents, its order and its failure path. Here a group is a
\*     unit whose finish is its fsync, then its publication.
\*
\* CONFIGURATIONS (each GREEN must pass, each RED must break the one
\* invariant it names):
\*   MC_NonBlocking_Green_Pool       two threads miss one block, and one of
\*                                   them a second block of its own.
\*   MC_NonBlocking_Green_Jobs       two threads miss one block while a
\*                                   call on one of them starts a job.
\*   MC_NonBlocking_Green_Single     one thread does everything (wasm).
\*   (Both pool setups at once, two blocks and a job, also passes: 2,283,135
\*   distinct states, about three minutes on eight workers; too slow for
\*   the recipe's single worker, so the recipe checks the two halves.)
\*   MC_NonBlocking_Red_WrongQueue   a read's request goes to the other
\*                                   thread's queue: OwnQueue breaks.
\*   MC_NonBlocking_Red_LostIdleWakeup  an owner checks "inbox empty" and
\*                                   marks itself idle in two steps:
\*                                   NoLostIdleWakeup breaks.
\*   MC_NonBlocking_Red_DoubleRun    a claim that also succeeds on a claimed
\*                                   unit: SingleRun breaks.
\*   MC_NonBlocking_Red_SelfIoNowhere  a job's unit is put on no queue:
\*                                   NoOrphanUnit breaks.
\*   MC_NonBlocking_Red_BusyWoken    a poll that forgets to clear the idle
\*                                   flag: BusyNeverWoken breaks.
\*   MC_NonBlocking_Green_Commit     two threads commit into one group with
\*                                   commit_nowait; any thread may land it.
\*   MC_NonBlocking_Green_Stall      two writers stopped by one stall.
\*   MC_NonBlocking_Red_DoubleSync   the DoubleRun claim on a group: its
\*                                   fsync runs twice, SingleRun breaks.
\*   MC_NonBlocking_Red_PublishAtWrite  a group visible as soon as it is
\*                                   written: VisibleAfterSync breaks.
\*   MC_NonBlocking_Red_DeliverOnLander  the thread that lands a group makes
\*                                   every member's ticket ready itself:
\*                                   DeliveredOnOwnPoll breaks.
\*   MC_NonBlocking_Red_NoRecheck    a stopped writer that does not look at
\*                                   the stall again after registering:
\*                                   StallLandsWhenClear breaks.
\*
\* Lean, proofs/lean/Regolith/IoQueue.lean, proves the same rules for every
\* number of threads and units, the commit units included: group_sync_once
\* (SingleRun for a group), group_visible_after_sync (VisibleAfterSync),
\* ticket_ready_only_at_own_poll (DeliveredOnOwnPoll) and
\* stall_lands_when_clear (StallLandsWhenClear), with the RED cases
\* lander_delivery_breaks_own_poll and no_recheck_strands_stall.

\* We use numbers, sequences (for inboxes) and finite sets.
EXTENDS Naturals, Sequences, FiniteSets

\* The fixed inputs of a configuration.
CONSTANTS
  \* The threads. Each holds exactly one queue, named after it.
  Threads,
  \* The blocks reads can miss.
  Blocks,
  \* [Threads -> SUBSET Blocks]: the blocks each thread's reads need.
  Want,
  \* Names for I/O regolith starts itself; disjoint from Blocks.
  Jobs,
  \* [Jobs -> Threads]: the thread whose call started each job.
  JobOf,
  \* Names for commit groups' fsyncs; disjoint from Blocks and Jobs.
  Groups,
  \* [Groups -> SUBSET Threads]: the threads with a commit_nowait member in
  \* each group.
  MembersOf,
  \* Names for write stalls; disjoint from the rest.
  Stalls,
  \* [Stalls -> SUBSET Threads]: the threads whose write each stall stops.
  StoppedBy,
  \* How many units may ever be made (each miss of a gone unit makes one).
  MaxUnits,
  \* "none" for the real code, or the name of one planted bug.
  Mutant

\* Unit number 0 means "no unit".
NoUnit == 0
\* The unit numbers that can exist.
Ids == 1..MaxUnits
\* Everything a unit can stand for: a block, a job, a group's fsync, or a
\* stall.
Things == Blocks \cup Jobs \cup Groups \cup Stalls
\* What thread t is waiting to see finished: its reads, its jobs, its
\* commits, and its stopped writes.
Goal(t) == Want[t] \cup {j \in Jobs : JobOf[j] = t}
           \cup {g \in Groups : t \in MembersOf[g]}
           \cup {s \in Stalls : t \in StoppedBy[s]}
\* The other thread (only used by the WrongQueue bug, with two threads).
Other(t) == CHOOSE o \in Threads : o # t

\* Blocks and jobs are different things.
ASSUME Blocks \cap Jobs = {}
\* Groups are neither blocks nor jobs.
ASSUME Groups \cap (Blocks \cup Jobs) = {}
\* Stalls are none of the others.
ASSUME Stalls \cap (Blocks \cup Jobs \cup Groups) = {}
\* Each group has its member threads.
ASSUME MembersOf \in [Groups -> SUBSET Threads]
\* Each stall stops some threads' writes.
ASSUME StoppedBy \in [Stalls -> SUBSET Threads]
\* Each thread wants a set of blocks.
ASSUME Want \in [Threads -> SUBSET Blocks]
\* Each job belongs to one thread.
ASSUME JobOf \in [Jobs -> Threads]
\* Unit counts are natural numbers.
ASSUME MaxUnits \in Nat
\* The bug names this model knows.
ASSUME Mutant \in {"none", "WrongQueue", "LostIdleWakeup", "DoubleRun",
                   "SelfIoNowhere", "BusyWoken", "PublishAtWrite",
                   "DeliverOnLander", "NoRecheck"}

\* The state that changes from step to step.
VARIABLES
  \* [Things -> Ids \cup {NoUnit}]: which unit the table holds for each
  \* block or job right now (IoRuntime::units).
  table,
  \* [Ids -> Things \cup {NoUnit}]: what each unit reads.
  what,
  \* [Ids -> {"none","free","claimed","done"}]: Unit::state. "none" means
  \* the number is not handed out yet.
  state,
  \* [Ids -> {"none","landed","released"}]: how a done unit ended: it read
  \* its block ("landed"), or close let it go without reading ("released").
  outcome,
  \* [Ids -> SUBSET Threads]: queues registered on the unit (its waiter
  \* Stack).
  waiters,
  \* [Ids -> BOOLEAN]: the SHUT flag on the unit's waiter Stack.
  shut,
  \* [Ids -> SUBSET Threads]: ghost, every queue whose registration
  \* succeeded, kept to check who must be told.
  regd,
  \* [Ids -> SUBSET Threads]: threads that claimed the unit and have not
  \* finished running it.
  runners,
  \* [Ids -> Nat]: ghost, how many times the unit's disk read ran.
  runs,
  \* [Ids -> SUBSET Threads]: queues the finishing thread still has to put
  \* a "done" note into.
  toTell,
  \* [Threads -> [Ids -> Nat]]: ghost, "done" notes each queue was given
  \* for each unit.
  told,
  \* The next unit number to hand out.
  next,
  \* [Threads -> Seq(message)]: each queue's inbox, oldest first.
  inbox,
  \* [Threads -> BOOLEAN]: the IDLE flag bit in each inbox's head word.
  idleFlag,
  \* [Threads -> Seq(message)]: notes the owner took out of its inbox and
  \* is still handling, one by one.
  taken,
  \* [Threads -> SUBSET Ids]: units each queue registered on (IoQueue::
  \* waiting).
  waiting,
  \* [Threads -> [Ids -> SUBSET Threads]]: for each queue and unit, the
  \* threads whose reads that queue recorded for it (the WaitSlots kept in
  \* the waiting entry).
  attached,
  \* [Threads -> [Things -> {"none","pending","ready"}]]: each read's wait:
  \* none, waiting, or ready to run again.
  slot,
  \* [Threads -> SUBSET Things]: blocks that landed for each queue.
  have,
  \* [Threads -> SUBSET Things]: reads that returned an answer, and jobs
  \* whose I/O finished.
  done,
  \* The jobs regolith has started.
  started,
  \* [Threads -> {"busy","idle"}]: is the owner thread running or asleep.
  own,
  \* [Threads -> BOOLEAN]: the owner's idle waker fired and it has not run
  \* since.
  woken,
  \* [Threads -> BOOLEAN]: bug LostIdleWakeup only: the owner saw an empty
  \* inbox and has not marked itself idle yet.
  checking,
  \* close() has run.
  closedDb,
  \* [Groups -> Ids \cup {NoUnit}]: the unit each group's fsync got when its
  \* leader wrote it (GroupSync's job).
  gunit,
  \* [Groups -> SUBSET Threads]: the members whose commit_nowait returned.
  joined,
  \* The groups whose fsync ran.
  synced,
  \* The groups readers can see.
  visible,
  \* Ghost: <<thread, thing>> for every wait made ready by a step that was
  \* not that thread's own poll.
  offPoll,
  \* The stalls in force now.
  stalled,
  \* [Threads -> [Stalls -> {"none", "seen", "recheck"}]]: a stopped write's
  \* progress: it saw the stall, or it registered its wait and is about to
  \* look at the stall again.
  spc

\* Every variable, so "nothing changed" can be written once.
vars == <<table, what, state, outcome, waiters, shut, regd, runners, runs,
          toTell, told, next, inbox, idleFlag, taken, waiting, attached,
          slot, have, done, started, own, woken, checking, closedDb,
          gunit, joined, synced, visible, offPoll, stalled, spc>>

\* The commit side's variables, so a step that leaves them alone says so once.
commitVars == <<gunit, joined, synced, visible, offPoll, stalled, spc>>

\* A note in an inbox: "read" (a read recorded unit u for reader r) or
\* "done" (unit u finished).
Msg == [kind : {"read", "done"}, u : Ids, reader : Threads \cup {0}]

\* The start: no unit, empty inboxes, every thread busy, nothing done.
Init ==
  \* No block or job has a unit in the table.
  /\ table = [x \in Things |-> NoUnit]
  \* No unit number reads anything yet.
  /\ what = [u \in Ids |-> NoUnit]
  \* No unit number is in use.
  /\ state = [u \in Ids |-> "none"]
  \* No unit has ended.
  /\ outcome = [u \in Ids |-> "none"]
  \* Nobody waits on any unit.
  /\ waiters = [u \in Ids |-> {}]
  \* Every waiter list is open.
  /\ shut = [u \in Ids |-> FALSE]
  \* Nobody has registered anywhere.
  /\ regd = [u \in Ids |-> {}]
  \* Nobody is running a unit.
  /\ runners = [u \in Ids |-> {}]
  \* No disk read has run.
  /\ runs = [u \in Ids |-> 0]
  \* Nobody is owed a note.
  /\ toTell = [u \in Ids |-> {}]
  \* No note has been given.
  /\ told = [q \in Threads |-> [u \in Ids |-> 0]]
  \* The first unit gets number 1.
  /\ next = 1
  \* Every inbox is empty.
  /\ inbox = [q \in Threads |-> <<>>]
  \* No owner is marked idle.
  /\ idleFlag = [q \in Threads |-> FALSE]
  \* Nobody is in the middle of handling notes.
  /\ taken = [q \in Threads |-> <<>>]
  \* No queue is registered on a unit.
  /\ waiting = [q \in Threads |-> {}]
  \* No queue holds a read for a unit.
  /\ attached = [q \in Threads |-> [u \in Ids |-> {}]]
  \* No read is waiting.
  /\ slot = [t \in Threads |-> [x \in Things |-> "none"]]
  \* Nothing has landed anywhere.
  /\ have = [q \in Threads |-> {}]
  \* No read has answered.
  /\ done = [t \in Threads |-> {}]
  \* No job has started.
  /\ started = {}
  \* Every thread is running.
  /\ own = [t \in Threads |-> "busy"]
  \* No waker has fired.
  /\ woken = [t \in Threads |-> FALSE]
  \* Nobody is half way into going idle.
  /\ checking = [t \in Threads |-> FALSE]
  \* The database is open.
  /\ closedDb = FALSE
  \* No group is written yet.
  /\ gunit = [g \in Groups |-> NoUnit]
  \* No member has committed.
  /\ joined = [g \in Groups |-> {}]
  \* No fsync ran.
  /\ synced = {}
  \* Nothing is visible.
  /\ visible = {}
  \* No wait was made ready off its own poll.
  /\ offPoll = {}
  \* Every stall is in force at the start.
  /\ stalled = Stalls
  \* No write has met a stall yet.
  /\ spc = [t \in Threads |-> [s \in Stalls |-> "none"]]

-----------------------------------------------------------------------------
\* HELPERS

\* Put note m at the back of queue q's inbox (QueueShared::deliver). If q
\* was marked idle, this push is the one that clears the mark and wakes q.
Push(q, m) ==
  \* The note goes to the back of q's inbox.
  /\ inbox' = [inbox EXCEPT ![q] = Append(@, m)]
  \* Any push clears the IDLE bit (the CAS writes a word without it).
  /\ idleFlag' = [idleFlag EXCEPT ![q] = FALSE]
  \* If the bit was set, this push wakes q's idle waker.
  /\ woken' = [woken EXCEPT ![q] = @ \/ idleFlag[q]]

\* Queue q keeps what unit u read, if it read anything, for q's re-runs.
Land(q, u) ==
  \* A landed unit leaves its block for q; a released one leaves nothing.
  have' = [have EXCEPT ![q] = IF outcome[u] = "landed" THEN @ \cup {what[u]} ELSE @]

\* Mark ready the waits of readers rs for thing x (WaitSlot::complete).
Ready(rs, x) ==
  \* Each reader in rs that waits on x is now ready to run again.
  slot' = [t \in Threads |-> IF t \in rs /\ slot[t][x] = "pending"
                             THEN [slot[t] EXCEPT ![x] = "ready"] ELSE slot[t]]

\* Is unit u free and held by nobody: in no queue's waiting set and no
\* inbox? Such a unit would never run.
Held(u) ==
  \* Some queue has registered on u, or has a request for u on its way.
  \E q \in Threads :
    \* q registered on u.
    \/ u \in waiting[q]
    \* A request for u sits in q's inbox.
    \/ \E i \in 1..Len(inbox[q]) : inbox[q][i].kind = "read" /\ inbox[q][i].u = u
    \* A request for u is among the notes q is handling.
    \/ \E i \in 1..Len(taken[q]) : taken[q][i].kind = "read" /\ taken[q][i].u = u

\* Is unit u passive: a stall's, which no poll runs and only the stall's
\* clearing lands?
Passive(u) == what[u] \in Stalls

\* Thread t's tasks have nothing to run: every goal is done or waiting.
Quiet(t) ==
  \* Each read is answered, or waits on the queue.
  /\ \A x \in Goal(t) : x \in done[t] \/ slot[t][x] = "pending"
  \* No stopped write is half way through registering its wait.
  /\ \A s \in Stalls : spc[t][s] = "none"
  \* Every job of t has been started.
  /\ \A j \in Jobs : JobOf[j] = t => j \in started
  \* t is not in the middle of running a unit.
  /\ \A u \in Ids : t \notin runners[u]
  \* t has no notes left to handle.
  /\ taken[t] = <<>>

-----------------------------------------------------------------------------
\* WHAT A READER DOES (on its own thread, while the thread is busy)

\* Thread t runs its read of block x and finds it: it landed for t's queue,
\* or the database is closed (the read then answers Closed). Either way the
\* read is over.
Hit(t, x) ==
  \* Only a running thread runs reads.
  /\ own[t] = "busy"
  \* t wants x and has no answer yet.
  /\ x \in Want[t] \ done[t]
  \* No earlier read of x is still waiting.
  /\ slot[t][x] = "none"
  \* The block is there, or the database is closed.
  /\ x \in have[t] \/ closedDb
  \* The read returns its answer.
  /\ done' = [done EXCEPT ![t] = @ \cup {x}]
  \* Nothing else changes.
  /\ UNCHANGED <<table, what, state, outcome, waiters, shut, regd, runners, runs,
                 toTell, told, next, inbox, idleFlag, taken, waiting, attached,
                 slot, have, started, own, woken, checking, closedDb>>
  \* The commit side is untouched.
  /\ UNCHANGED commitVars

\* Thread t runs its read of block x and misses (IoRuntime::miss). It does
\* not touch the disk: it finds or makes the unit for x, puts a "read" note
\* on its own queue, and returns WouldBlock.
Miss(t, x) ==
  \* The unit the table holds for x now.
  LET cur == table[x]
      \* No live unit: this miss makes a new one (a finished one is replaced).
      fresh == cur = NoUnit \/ state[cur] = "done"
      \* The unit this read waits on.
      u == IF fresh THEN next ELSE cur
      \* The queue the note goes to: t's own, unless the WrongQueue bug.
      q == IF Mutant = "WrongQueue" THEN Other(t) ELSE t
  \* With those names, the step is:
  IN
  \* Only a running thread runs reads.
  /\ own[t] = "busy"
  \* t wants x and has no answer yet.
  /\ x \in Want[t] \ done[t]
  \* No earlier read of x is still waiting.
  /\ slot[t][x] = "none"
  \* The block has not landed for t.
  /\ x \notin have[t]
  \* The database is open (a closed one answers Closed, in Hit). In the code
  \* the read checked this when it started, and checks again as the miss
  \* counts itself in at the close gate (IoRuntime::miss, CloseGate::enter),
  \* so a miss either comes before close's mark or answers Closed.
  /\ ~closedDb
  \* A new unit needs a free number.
  /\ fresh => next <= MaxUnits
  \* A new unit goes into the table for x...
  /\ table' = IF fresh THEN [table EXCEPT ![x] = next] ELSE table
  \* ...reading x...
  /\ what' = IF fresh THEN [what EXCEPT ![next] = x] ELSE what
  \* ...and free: nobody has claimed it.
  /\ state' = IF fresh THEN [state EXCEPT ![next] = "free"] ELSE state
  \* The next number moves on when one was used.
  /\ next' = IF fresh THEN next + 1 ELSE next
  \* The "read" note goes to the queue.
  /\ Push(q, [kind |-> "read", u |-> u, reader |-> t])
  \* The read now waits.
  /\ slot' = [slot EXCEPT ![t][x] = "pending"]
  \* Nothing else changes.
  /\ UNCHANGED <<outcome, waiters, shut, regd, runners, runs, toTell, told, taken,
                 waiting, attached, have, done, started, own, checking, closedDb>>
  \* The commit side is untouched.
  /\ UNCHANGED commitVars

\* A call on thread t makes regolith start job j itself (a flush with no
\* worker). The job takes the miss path: a unit, and a "read" note on the
\* starting thread's own queue. Bug SelfIoNowhere puts it on no queue.
SelfStart(t, j) ==
  \* Only a running thread makes calls.
  /\ own[t] = "busy"
  \* j belongs to t and has not started.
  /\ JobOf[j] = t /\ j \notin started
  \* A free unit number is needed.
  /\ next <= MaxUnits
  \* The job's unit goes into the table...
  /\ table' = [table EXCEPT ![j] = next]
  \* ...doing job j...
  /\ what' = [what EXCEPT ![next] = j]
  \* ...unclaimed.
  /\ state' = [state EXCEPT ![next] = "free"]
  \* The next number moves on.
  /\ next' = next + 1
  \* The job counts as started.
  /\ started' = started \cup {j}
  \* The call that started it waits for it on t's queue.
  /\ slot' = [slot EXCEPT ![t][j] = "pending"]
  \* The note goes to t's own queue; bug SelfIoNowhere sends it nowhere.
  /\ IF Mutant = "SelfIoNowhere"
       \* Nothing is pushed anywhere.
       THEN UNCHANGED <<inbox, idleFlag, woken>>
       \* The note lands on the starting thread's own queue.
       ELSE Push(t, [kind |-> "read", u |-> next, reader |-> t])
  \* Nothing else changes.
  /\ UNCHANGED <<outcome, waiters, shut, regd, runners, runs, toTell, told, taken,
                 waiting, attached, have, done, own, checking, closedDb>>
  \* The commit side is untouched.
  /\ UNCHANGED commitVars

\* Thread t's wait for x is ready: it runs again (Hit or Miss decide what
\* happens). A job's caller sees its job finished, and a commit's caller its
\* ticket ready; a stopped write will run again (WriteTry).
Rerun(t, x) ==
  \* Only a running thread runs tasks.
  /\ own[t] = "busy"
  \* The wait for x is ready.
  /\ slot[t][x] = "ready"
  \* The wait is used up.
  /\ slot' = [slot EXCEPT ![t][x] = "none"]
  \* A job or a commit is finished for its caller; a read or a write will
  \* run again.
  /\ done' = IF x \in Jobs \cup Groups THEN [done EXCEPT ![t] = @ \cup {x}] ELSE done
  \* Nothing else changes.
  /\ UNCHANGED <<table, what, state, outcome, waiters, shut, regd, runners, runs,
                 toTell, told, next, inbox, idleFlag, taken, waiting, attached,
                 have, started, own, woken, checking, closedDb>>
  \* The commit side is untouched.
  /\ UNCHANGED commitVars

-----------------------------------------------------------------------------
\* WHAT A COMMITTER DOES (on its own thread): commit_nowait

\* Thread t's commit_nowait in group g returns. The first member's commit
\* is the leader's: it writes the group and leaves its fsync as one unit
\* (GroupSync's job, src/engine/commit/deferred.rs). Every member, the
\* leader included, puts a note for that unit on its OWN queue and returns
\* with a ticket that waits on it. Bug PublishAtWrite makes the group
\* visible as soon as it is written.
CommitNowait(t, g) ==
  \* The unit the group has, or the one its leader makes now.
  LET fresh == gunit[g] = NoUnit
      \* The unit this member's ticket waits on.
      u == IF fresh THEN next ELSE gunit[g]
  \* With those names, the step is:
  IN
  \* Only a running thread commits.
  /\ own[t] = "busy"
  \* t has a member in g and has not committed it.
  /\ t \in MembersOf[g] /\ t \notin joined[g]
  \* The group was written before close, or the database is open (a group
  \* close came before is CommitClosed).
  /\ ~closedDb \/ ~fresh
  \* A new unit needs a free number.
  /\ fresh => next <= MaxUnits
  \* The leader's write makes the unit, in the table, free.
  /\ table' = IF fresh THEN [table EXCEPT ![g] = next] ELSE table
  \* It stands for the group's fsync.
  /\ what' = IF fresh THEN [what EXCEPT ![next] = g] ELSE what
  \* Nobody has claimed it.
  /\ state' = IF fresh THEN [state EXCEPT ![next] = "free"] ELSE state
  \* The next number moves on when one was used.
  /\ next' = IF fresh THEN next + 1 ELSE next
  \* The group remembers its unit.
  /\ gunit' = IF fresh THEN [gunit EXCEPT ![g] = next] ELSE gunit
  \* t's commit returned.
  /\ joined' = [joined EXCEPT ![g] = @ \cup {t}]
  \* The note goes to t's own queue.
  /\ Push(t, [kind |-> "read", u |-> u, reader |-> t])
  \* The ticket waits.
  /\ slot' = [slot EXCEPT ![t][g] = "pending"]
  \* The bug publishes the group before any fsync.
  /\ visible' = IF Mutant = "PublishAtWrite" THEN visible \cup {g} ELSE visible
  \* Nothing else changes.
  /\ UNCHANGED <<outcome, waiters, shut, regd, runners, runs, toTell, told, taken,
                 waiting, attached, have, done, started, own, checking, closedDb>>
  \* The rest of the commit side is untouched.
  /\ UNCHANGED <<synced, offPoll, stalled, spc>>

\* Thread t's commit_nowait comes after close, and no group was written for
\* it: it is refused with Closed, and its ticket is ready at once, on t.
CommitClosed(t, g) ==
  \* Only a running thread commits.
  /\ own[t] = "busy"
  \* t has a member in g and has not committed it.
  /\ t \in MembersOf[g] /\ t \notin joined[g]
  \* Close came first, before any member wrote the group.
  /\ closedDb /\ gunit[g] = NoUnit
  \* t's commit returned.
  /\ joined' = [joined EXCEPT ![g] = @ \cup {t}]
  \* With Closed: the commit is over for its caller.
  /\ done' = [done EXCEPT ![t] = @ \cup {g}]
  \* Nothing else changes.
  /\ UNCHANGED <<table, what, state, outcome, waiters, shut, regd, runners, runs,
                 toTell, told, next, inbox, idleFlag, taken, waiting, attached,
                 slot, have, started, own, woken, checking, closedDb>>
  \* The rest of the commit side is untouched.
  /\ UNCHANGED <<gunit, synced, visible, offPoll, stalled, spc>>

\* Thread t takes the commit pipeline (to write the next group, to flush,
\* or a blocking member waiting on its own group) and lands the group that
\* is owed first: it claims the group's unit with the same one CAS
\* (land_pending, GroupSync::land_here). It need not be a member.
LandHere(t, u) ==
  \* Only a running thread takes the pipeline.
  /\ own[t] = "busy"
  \* u is a group's fsync.
  /\ what[u] \in Groups
  \* The CAS succeeds only on a free unit (the bug: also on a claimed one).
  /\ \/ state[u] = "free"
     \* The bug: a unit someone else already claimed.
     \/ Mutant = "DoubleRun" /\ state[u] = "claimed" /\ t \notin runners[u]
  \* The unit is claimed.
  /\ state' = [state EXCEPT ![u] = "claimed"]
  \* t is running it now.
  /\ runners' = [runners EXCEPT ![u] = @ \cup {t}]
  \* Nothing else changes.
  /\ UNCHANGED <<table, what, outcome, waiters, shut, regd, runs, toTell, told,
                 next, inbox, idleFlag, taken, waiting, attached, slot, have,
                 done, started, own, woken, checking, closedDb>>
  \* The commit side is untouched.
  /\ UNCHANGED commitVars

-----------------------------------------------------------------------------
\* WHAT A WRITER DOES UNDER A STALL (on its own thread)

\* Thread t runs its write of stall s's kind. With the stall cleared it
\* applies and is done; under the stall it is stopped and goes on to
\* register a wait (it never sleeps).
WriteTry(t, s) ==
  \* Only a running thread writes.
  /\ own[t] = "busy"
  \* The stall stops t's write, which is not done.
  /\ t \in StoppedBy[s] /\ s \notin done[t]
  \* No wait of this write is outstanding, and it is not mid-way.
  /\ slot[t][s] = "none" /\ spc[t][s] = "none"
  \* Applied when clear (or answered Closed); stopped otherwise.
  /\ IF s \notin stalled \/ closedDb
       \* The write is over.
       THEN /\ done' = [done EXCEPT ![t] = @ \cup {s}]
            \* Nothing to register.
            /\ UNCHANGED spc
       \* It saw the stall.
       ELSE /\ spc' = [spc EXCEPT ![t][s] = "seen"]
            \* Not done.
            /\ UNCHANGED done
  \* Nothing else changes.
  /\ UNCHANGED <<table, what, state, outcome, waiters, shut, regd, runners, runs,
                 toTell, told, next, inbox, idleFlag, taken, waiting, attached,
                 slot, have, started, own, woken, checking, closedDb>>
  \* The rest of the commit side is untouched.
  /\ UNCHANGED <<gunit, joined, synced, visible, offPoll, stalled>>

\* The stopped writer finds the stall's unit, or installs a fresh passive
\* one, and puts a note for it on its own queue (StallSignal::wait). It has
\* not looked at the stall again yet.
StallWait(t, s) ==
  \* The unit the table holds for the stall now.
  LET cur == table[s]
      \* None live: this writer installs one.
      fresh == cur = NoUnit \/ state[cur] = "done"
      \* The unit this write waits on.
      u == IF fresh THEN next ELSE cur
  \* With those names, the step is:
  IN
  \* Only a running thread writes.
  /\ own[t] = "busy"
  \* The writer saw the stall.
  /\ spc[t][s] = "seen"
  \* A new unit needs a free number.
  /\ fresh => next <= MaxUnits
  \* A new unit goes into the table, standing for the stall, unlanded.
  /\ table' = IF fresh THEN [table EXCEPT ![s] = next] ELSE table
  \* It stands for the stall.
  /\ what' = IF fresh THEN [what EXCEPT ![next] = s] ELSE what
  \* Free: not landed (and, being passive, never claimed).
  /\ state' = IF fresh THEN [state EXCEPT ![next] = "free"] ELSE state
  \* The next number moves on when one was used.
  /\ next' = IF fresh THEN next + 1 ELSE next
  \* The note goes to t's own queue.
  /\ Push(t, [kind |-> "read", u |-> u, reader |-> t])
  \* The write's wait is pending.
  /\ slot' = [slot EXCEPT ![t][s] = "pending"]
  \* Now it looks at the stall again.
  /\ spc' = [spc EXCEPT ![t][s] = "recheck"]
  \* Nothing else changes.
  /\ UNCHANGED <<outcome, waiters, shut, regd, runners, runs, toTell, told, taken,
                 waiting, attached, have, done, started, own, checking, closedDb>>
  \* The rest of the commit side is untouched.
  /\ UNCHANGED <<gunit, joined, synced, visible, offPoll, stalled>>

\* Land the stall unit u: it ends without a read, its waiter list is shut,
\* and every queue on it is owed a note (Job::release of a passive job).
LandStall(u) ==
  \* u ends here.
  /\ state' = [state EXCEPT ![u] = "done"]
  \* It landed: the stall cleared.
  /\ outcome' = [outcome EXCEPT ![u] = "landed"]
  \* Its waiter list is shut.
  /\ shut' = [shut EXCEPT ![u] = TRUE]
  \* Every registered queue is owed a note.
  /\ toTell' = [toTell EXCEPT ![u] = waiters[u]]
  \* The list was taken whole.
  /\ waiters' = [waiters EXCEPT ![u] = {}]
  \* The table forgets it.
  /\ table' = [table EXCEPT ![what[u]] = NoUnit]

\* The writer looks at the stall again, now that its wait is recorded: if
\* the stall cleared meanwhile, it lands the unit itself, so a clearer that
\* came before the registration is not missed. Bug NoRecheck skips this.
StallRecheck(t, s) ==
  \* The unit the table holds for the stall now.
  LET u == table[s]
  \* With that name, the step is:
  IN
  \* Only a running thread writes.
  /\ own[t] = "busy"
  \* The writer registered and is about to look again.
  /\ spc[t][s] = "recheck"
  \* The look is over.
  /\ spc' = [spc EXCEPT ![t][s] = "none"]
  \* Cleared, with a unit still unlanded: land it (the bug never does).
  /\ IF s \notin stalled /\ u # NoUnit /\ state[u] = "free" /\ Mutant # "NoRecheck"
       \* The writer lands the unit.
       THEN LandStall(u)
       \* Still stalled (the clearer will land it), or nothing to land.
       ELSE UNCHANGED <<state, outcome, shut, toTell, waiters, table>>
  \* Nothing else changes.
  /\ UNCHANGED <<what, regd, runners, runs, told, next, inbox, idleFlag, taken,
                 waiting, attached, slot, have, done, started, own, woken,
                 checking, closedDb>>
  \* The rest of the commit side is untouched.
  /\ UNCHANGED <<gunit, joined, synced, visible, offPoll, stalled>>

\* Background work (a flush, a compaction pass) clears stall s and lands
\* the unit its stopped writers wait on, if there is one (StallSignal::
\* refresh). It records the cleared level before it takes the unit.
Clear(s) ==
  \* The unit the table holds for the stall now.
  LET u == table[s]
  \* With that name, the step is:
  IN
  \* The stall is in force.
  /\ s \in stalled
  \* It is cleared.
  /\ stalled' = stalled \ {s}
  \* A unit still unlanded is landed now.
  /\ IF u # NoUnit /\ state[u] = "free"
       \* Land it.
       THEN LandStall(u)
       \* Nothing to land.
       ELSE UNCHANGED <<state, outcome, shut, toTell, waiters, table>>
  \* Nothing else changes.
  /\ UNCHANGED <<what, regd, runners, runs, told, next, inbox, idleFlag, taken,
                 waiting, attached, slot, have, done, started, own, woken,
                 checking, closedDb>>
  \* The rest of the commit side is untouched.
  /\ UNCHANGED <<gunit, joined, synced, visible, offPoll, spc>>

-----------------------------------------------------------------------------
\* WHAT A QUEUE'S OWNER DOES WHEN IT POLLS (IoQueue::poll)

\* The owner takes its whole inbox in one swap, which also clears IDLE.
Take(t) ==
  \* Only a running owner polls.
  /\ own[t] = "busy"
  \* Something is in the inbox.
  /\ inbox[t] # <<>>
  \* The notes join the ones being handled, oldest first.
  /\ taken' = [taken EXCEPT ![t] = @ \o inbox[t]]
  \* The inbox is empty now.
  /\ inbox' = [inbox EXCEPT ![t] = <<>>]
  \* The swap writes a word with no IDLE bit.
  /\ idleFlag' = [idleFlag EXCEPT ![t] = FALSE]
  \* Nothing else changes.
  /\ UNCHANGED <<table, what, state, outcome, waiters, shut, regd, runners, runs,
                 toTell, told, next, waiting, attached, slot, have, done, started,
                 own, woken, checking, closedDb>>
  \* The commit side is untouched.
  /\ UNCHANGED commitVars

\* The owner handles its oldest taken note.
Handle(t) ==
  \* Only a running owner handles notes.
  /\ own[t] = "busy"
  \* There is a note to handle.
  /\ taken[t] # <<>>
  \* The note, and the unit it names.
  /\ LET m == Head(taken[t])
         \* The unit the note is about.
         u == m.u
     \* With those names, the step is:
     IN
     \* The note is handled now.
     /\ taken' = [taken EXCEPT ![t] = Tail(@)]
     \* What else happens depends on the note and the unit:
     /\ CASE
          \* A read of a unit this queue already registered on: the read
          \* joins it (one more WaitSlot in the waiting entry).
          m.kind = "read" /\ u \in waiting[t] ->
            \* The reader is recorded with the unit.
            /\ attached' = [attached EXCEPT ![t][u] = @ \cup {m.reader}]
            \* Nothing else changes.
            /\ UNCHANGED <<waiters, shut, regd, waiting, slot, have>>
          \* A read of a unit this queue has not registered on, still open:
          \* register (one CAS push onto the unit's waiter Stack).
          [] m.kind = "read" /\ u \notin waiting[t] /\ ~shut[u] ->
            \* This queue is on the unit's waiter list now.
            /\ waiters' = [waiters EXCEPT ![u] = @ \cup {t}]
            \* Ghost: the registration succeeded.
            /\ regd' = [regd EXCEPT ![u] = @ \cup {t}]
            \* The queue waits on the unit.
            /\ waiting' = [waiting EXCEPT ![t] = @ \cup {u}]
            \* The reader is recorded with the unit.
            /\ attached' = [attached EXCEPT ![t][u] = {m.reader}]
            \* Nothing else changes.
            /\ UNCHANGED <<shut, slot, have>>
          \* A read of a unit that finished before the queue could register:
          \* the push is refused, and the queue reads the outcome itself.
          [] m.kind = "read" /\ u \notin waiting[t] /\ shut[u] ->
            \* Whatever the unit read lands for this queue.
            /\ Land(t, u)
            \* The reader's wait is ready.
            /\ Ready({m.reader}, what[u])
            \* Nothing else changes.
            /\ UNCHANGED <<waiters, shut, regd, waiting, attached>>
          \* A unit this queue waits on finished: what it read lands, and
          \* every read the queue recorded for it is ready.
          [] m.kind = "done" /\ u \in waiting[t] ->
            \* The queue stops waiting on the unit.
            /\ waiting' = [waiting EXCEPT ![t] = @ \ {u}]
            \* Whatever the unit read lands for this queue.
            /\ Land(t, u)
            \* Every read recorded here for the unit is ready.
            /\ Ready(attached[t][u], what[u])
            \* The entry is gone.
            /\ attached' = [attached EXCEPT ![t][u] = {}]
            \* Nothing else changes.
            /\ UNCHANGED <<waiters, shut, regd>>
          \* A "done" note for a unit the queue no longer waits on: nothing.
          [] OTHER ->
            \* Nothing changes.
            UNCHANGED <<waiters, shut, regd, waiting, attached, slot, have>>
  \* Nothing else changes.
  /\ UNCHANGED <<table, what, state, outcome, runners, runs, toTell, told, next,
                 inbox, idleFlag, done, started, own, woken, checking, closedDb>>
  \* The commit side is untouched.
  /\ UNCHANGED commitVars

\* The owner claims a unit it waits on with ONE compare-and-swap from free
\* to claimed (Unit::claim). Bug DoubleRun also lets a claimed unit be
\* claimed again.
Claim(t, u) ==
  \* Only a running owner claims.
  /\ own[t] = "busy"
  \* The queue waits on u.
  /\ u \in waiting[t]
  \* A passive unit (a stall's) is never claimed: only its clearing lands it.
  /\ ~Passive(u)
  \* The CAS succeeds only on a free unit (the bug: also on a claimed one).
  /\ \/ state[u] = "free"
     \* The bug: a unit someone else already claimed.
     \/ Mutant = "DoubleRun" /\ state[u] = "claimed" /\ t \notin runners[u]
  \* The unit is claimed.
  /\ state' = [state EXCEPT ![u] = "claimed"]
  \* t is running it now.
  /\ runners' = [runners EXCEPT ![u] = @ \cup {t}]
  \* Nothing else changes.
  /\ UNCHANGED <<table, what, outcome, waiters, shut, regd, runs, toTell, told,
                 next, inbox, idleFlag, taken, waiting, attached, slot, have,
                 done, started, own, woken, checking, closedDb>>
  \* The commit side is untouched.
  /\ UNCHANGED commitVars

\* The claimer reads the block and finishes the unit (Unit::finish): it
\* writes the outcome, marks the unit done, shuts the waiter list in ONE
\* swap (taking every registered queue), and drops the unit from the table.
\* For a group's unit the "read" is the group's fsync: the group is synced,
\* then applied and published (visible). Bug DeliverOnLander also makes
\* every registered member's ticket ready right here, on the lander's
\* thread, instead of at each member's own poll.
Finish(t, u) ==
  \* t is running u.
  /\ t \in runners[u]
  \* t is done running it.
  /\ runners' = [runners EXCEPT ![u] = @ \ {t}]
  \* Ghost: the disk read ran once more.
  /\ runs' = [runs EXCEPT ![u] = @ + 1]
  \* The first finisher ends the unit; under the bug a second finisher
  \* finds it already done and only adds a read.
  /\ IF state[u] = "claimed"
       \* The unit ends here.
       THEN /\ state' = [state EXCEPT ![u] = "done"]
            \* It read its block.
            /\ outcome' = [outcome EXCEPT ![u] = "landed"]
            \* The waiter list is shut: later registrations are refused.
            /\ shut' = [shut EXCEPT ![u] = TRUE]
            \* Every queue on the list is owed one "done" note.
            /\ toTell' = [toTell EXCEPT ![u] = waiters[u]]
            \* The list is empty (it was taken whole).
            /\ waiters' = [waiters EXCEPT ![u] = {}]
            \* The table forgets the unit.
            /\ table' = IF table[what[u]] = u THEN [table EXCEPT ![what[u]] = NoUnit] ELSE table
       \* Already ended by the first finisher.
       ELSE UNCHANGED <<state, outcome, shut, toTell, waiters, table>>
  \* A group's fsync ran: the group is durable, then visible.
  /\ synced' = IF what[u] \in Groups THEN synced \cup {what[u]} ELSE synced
  \* Applied and published only after the fsync.
  /\ visible' = IF what[u] \in Groups THEN visible \cup {what[u]} ELSE visible
  \* The bug readies each registered member's ticket on this thread.
  /\ IF Mutant = "DeliverOnLander" /\ what[u] \in Groups /\ state[u] = "claimed"
       \* Every registered member's wait is ready now, made so by t.
       THEN /\ Ready(regd[u], what[u])
            \* Ghost: each of those, not t, was readied off its own poll.
            /\ offPoll' = offPoll \cup {<<q, what[u]>> : q \in regd[u] \ {t}}
       \* The real code: readiness comes only at each member's poll.
       ELSE UNCHANGED <<slot, offPoll>>
  \* Nothing else changes.
  /\ UNCHANGED <<what, regd, told, next, inbox, idleFlag, taken, waiting,
                 attached, have, done, started, own, woken, checking, closedDb>>
  \* The rest of the commit side is untouched.
  /\ UNCHANGED <<gunit, joined, stalled, spc>>

\* The finishing thread puts the "done" note for u into queue q's inbox:
\* one push per queue it took off the waiter list.
Tell(u, q) ==
  \* q is still owed its note.
  /\ q \in toTell[u]
  \* The note goes to q (and wakes q if q is idle).
  /\ Push(q, [kind |-> "done", u |-> u, reader |-> 0])
  \* q is no longer owed.
  /\ toTell' = [toTell EXCEPT ![u] = @ \ {q}]
  \* Ghost: q was given one more note for u.
  /\ told' = [told EXCEPT ![q][u] = @ + 1]
  \* Nothing else changes.
  /\ UNCHANGED <<table, what, state, outcome, waiters, shut, regd, runners, runs,
                 next, taken, waiting, attached, slot, have, done, started,
                 own, checking, closedDb>>
  \* The commit side is untouched.
  /\ UNCHANGED commitVars

-----------------------------------------------------------------------------
\* GOING IDLE AND WAKING UP (IoQueue::idle_waker, QueueShared::rest)

\* The owner has nothing to run and goes idle: it registers its waker and
\* sets IDLE with one CAS that succeeds only on an empty inbox. If a unit
\* it waits on is still free (only it can run that one), or a note is
\* already in the inbox, it is woken at once instead: this action is then
\* simply not taken. Bug LostIdleWakeup does the "inbox empty?" look and
\* the marking as two steps.
Rest(t) ==
  \* Only a running owner goes idle.
  /\ own[t] = "busy"
  \* Its tasks have nothing to run.
  /\ Quiet(t)
  \* No unit it waits on is left for it to run (a passive one is not its to
  \* run: it waits for the stall to clear).
  /\ \A u \in waiting[t] : state[u] # "free" \/ Passive(u)
  \* Its inbox is empty (the CAS checks this).
  /\ inbox[t] = <<>>
  \* Not already half way into going idle.
  /\ ~checking[t]
  \* How the owner goes idle depends on the bug:
  /\ IF Mutant = "LostIdleWakeup"
       \* The bug: only the look happens now; the mark comes later.
       THEN /\ checking' = [checking EXCEPT ![t] = TRUE]
            \* Nothing else changes yet.
            /\ UNCHANGED <<idleFlag, own>>
       \* The real code: the look and the mark are the same CAS.
       ELSE /\ idleFlag' = [idleFlag EXCEPT ![t] = TRUE]
            \* The owner sleeps.
            /\ own' = [own EXCEPT ![t] = "idle"]
            \* Nothing else changes.
            /\ UNCHANGED checking
  \* Nothing else changes.
  /\ UNCHANGED <<table, what, state, outcome, waiters, shut, regd, runners, runs,
                 toTell, told, next, inbox, taken, waiting, attached, slot, have,
                 done, started, woken, closedDb>>
  \* The commit side is untouched.
  /\ UNCHANGED commitVars

\* Bug LostIdleWakeup, second half: mark idle without looking again. A note
\* pushed between the look and this mark saw no IDLE bit and woke nobody.
MarkIdle(t) ==
  \* The look was done.
  /\ checking[t]
  \* The look is over.
  /\ checking' = [checking EXCEPT ![t] = FALSE]
  \* The IDLE bit is set, whatever the inbox holds now.
  /\ idleFlag' = [idleFlag EXCEPT ![t] = TRUE]
  \* The owner sleeps.
  /\ own' = [own EXCEPT ![t] = "idle"]
  \* Nothing else changes.
  /\ UNCHANGED <<table, what, state, outcome, waiters, shut, regd, runners, runs,
                 toTell, told, next, inbox, taken, waiting, attached, slot, have,
                 done, started, woken, closedDb>>
  \* The commit side is untouched.
  /\ UNCHANGED commitVars

\* An idle owner whose waker fired runs again.
Wake(t) ==
  \* It was asleep.
  /\ own[t] = "idle"
  \* Its waker fired.
  /\ woken[t]
  \* It runs.
  /\ own' = [own EXCEPT ![t] = "busy"]
  \* The wake is used up.
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  \* Nothing else changes.
  /\ UNCHANGED <<table, what, state, outcome, waiters, shut, regd, runners, runs,
                 toTell, told, next, inbox, idleFlag, taken, waiting, attached,
                 slot, have, done, started, checking, closedDb>>
  \* The commit side is untouched.
  /\ UNCHANGED commitVars

\* An idle owner runs again on its own (its executor got other work) and
\* polls, which clears IDLE first (QueueShared::wake_up). Bug BusyWoken
\* forgets to clear it. Not fair: an owner may never do this.
SelfWake(t) ==
  \* It was asleep.
  /\ own[t] = "idle"
  \* It runs.
  /\ own' = [own EXCEPT ![t] = "busy"]
  \* Its poll clears IDLE (the bug leaves it set).
  /\ idleFlag' = IF Mutant = "BusyWoken" THEN idleFlag ELSE [idleFlag EXCEPT ![t] = FALSE]
  \* A wake that fired meanwhile is used up by this run.
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  \* Nothing else changes.
  /\ UNCHANGED <<table, what, state, outcome, waiters, shut, regd, runners, runs,
                 toTell, told, next, inbox, taken, waiting, attached, slot, have,
                 done, started, checking, closedDb>>
  \* The commit side is untouched.
  /\ UNCHANGED commitVars

-----------------------------------------------------------------------------
\* CLOSE (RegolithEngine::close -> IoRuntime::close)
\*
\* Close marks the gate (CloseGate::close), then sweeps the table. A miss
\* already counted in when the mark lands releases its own unit when it
\* counts itself out (CloseGate::leave), so Release below stands for the
\* sweep and for that miss alike, and no unit outlives close. The loom model
\* no_unit_outlives_close checks the gate itself, with a calibration that
\* checks for close only when the miss starts and leaves a unit behind.

\* The database closes. Reads run after this answer Closed.
Close ==
  \* Not closed yet.
  /\ ~closedDb
  \* Closed now.
  /\ closedDb' = TRUE
  \* Nothing else changes.
  /\ UNCHANGED <<table, what, state, outcome, waiters, shut, regd, runners, runs,
                 toTell, told, next, inbox, idleFlag, taken, waiting, attached,
                 slot, have, done, started, own, woken, checking>>
  \* The commit side is untouched.
  /\ UNCHANGED commitVars

\* Close lets a free unit in the table go without reading it: it claims it
\* (so no runner can) and finishes it as "released", telling every
\* registered queue. A unit someone is running finishes on its own. A
\* group's unit is the exception: close lands it, running its fsync (the
\* final sync covers it, so every member's ticket says committed); a stall's
\* unit lands too (close tells every stopped writer).
Release(u) ==
  \* The database is closing.
  /\ closedDb
  \* u is free and in the table.
  /\ state[u] = "free" /\ table[what[u]] = u
  \* u ends here.
  /\ state' = [state EXCEPT ![u] = "done"]
  \* A block or job read nothing; a group or a stall landed.
  /\ outcome' = [outcome EXCEPT ![u] = IF what[u] \in Groups \cup Stalls
                                         THEN "landed" ELSE "released"]
  \* A group's fsync ran once, here.
  /\ runs' = IF what[u] \in Groups THEN [runs EXCEPT ![u] = @ + 1] ELSE runs
  \* So the group is durable...
  /\ synced' = IF what[u] \in Groups THEN synced \cup {what[u]} ELSE synced
  \* ...and then visible.
  /\ visible' = IF what[u] \in Groups THEN visible \cup {what[u]} ELSE visible
  \* Its waiter list is shut.
  /\ shut' = [shut EXCEPT ![u] = TRUE]
  \* Every registered queue is owed a note.
  /\ toTell' = [toTell EXCEPT ![u] = waiters[u]]
  \* The list was taken whole.
  /\ waiters' = [waiters EXCEPT ![u] = {}]
  \* The table forgets it.
  /\ table' = [table EXCEPT ![what[u]] = NoUnit]
  \* Nothing else changes.
  /\ UNCHANGED <<what, regd, runners, told, next, inbox, idleFlag, taken,
                 waiting, attached, slot, have, done, started, own, woken,
                 checking, closedDb>>
  \* The rest of the commit side is untouched.
  /\ UNCHANGED <<gunit, joined, offPoll, stalled, spc>>

-----------------------------------------------------------------------------
\* THE WHOLE SYSTEM

\* Any step of thread t (as reader, owner, or runner).
ThreadStep(t) ==
  \* A read that finds its block, or the database closed.
  \/ \E x \in Blocks : Hit(t, x)
  \* A read that misses.
  \/ \E x \in Blocks : Miss(t, x)
  \* A job regolith starts on t's call.
  \/ \E j \in Jobs : SelfStart(t, j)
  \* A commit_nowait returns.
  \/ \E g \in Groups : CommitNowait(t, g)
  \* A commit_nowait after close is refused.
  \/ \E g \in Groups : CommitClosed(t, g)
  \* t takes the pipeline and lands an owed group.
  \/ \E u \in Ids : LandHere(t, u)
  \* A write runs, or meets a stall.
  \/ \E s \in Stalls : WriteTry(t, s)
  \* A stopped write registers its wait.
  \/ \E s \in Stalls : StallWait(t, s)
  \* A stopped write looks at the stall again.
  \/ \E s \in Stalls : StallRecheck(t, s)
  \* A ready wait runs again.
  \/ \E x \in Things : Rerun(t, x)
  \* The poll takes the inbox.
  \/ Take(t)
  \* The poll handles a note.
  \/ Handle(t)
  \* The poll claims a unit.
  \/ \E u \in Ids : Claim(t, u)
  \* A claimed unit's read finishes.
  \/ \E u \in Ids : Finish(t, u)
  \* The owner goes idle.
  \/ Rest(t)
  \* Bug only: the second half of going idle.
  \/ MarkIdle(t)
  \* A woken owner runs.
  \/ Wake(t)

\* Every possible step.
Next ==
  \* Some thread steps.
  \/ \E t \in Threads : ThreadStep(t)
  \* An owner wakes on its own.
  \/ \E t \in Threads : SelfWake(t)
  \* A finisher tells a queue.
  \/ \E u \in Ids, q \in Threads : Tell(u, q)
  \* The database closes.
  \/ Close
  \* Close lets a unit go.
  \/ \E u \in Ids : Release(u)
  \* Background work clears a stall.
  \/ \E s \in Stalls : Clear(s)

\* The behaviours: start at Init, take Next steps, and never stop a step
\* that stays possible (weak fairness). An owner waking on its own and
\* close are not forced: liveness must not lean on them.
Spec ==
  \* Start.
  /\ Init
  \* Step.
  /\ [][Next]_vars
  \* Each thread keeps going while it can.
  /\ \A t \in Threads :
       \* Its reads that hit.
       /\ WF_vars(\E x \in Blocks : Hit(t, x))
       \* Its reads that miss.
       /\ WF_vars(\E x \in Blocks : Miss(t, x))
       \* Its jobs.
       /\ WF_vars(\E j \in Jobs : SelfStart(t, j))
       \* Its commits.
       /\ WF_vars(\E g \in Groups : CommitNowait(t, g))
       \* Its commits refused after close.
       /\ WF_vars(\E g \in Groups : CommitClosed(t, g))
       \* Its writes.
       /\ WF_vars(\E s \in Stalls : WriteTry(t, s))
       \* Its stopped writes' registrations.
       /\ WF_vars(\E s \in Stalls : StallWait(t, s))
       \* Its stopped writes' second looks.
       /\ WF_vars(\E s \in Stalls : StallRecheck(t, s))
       \* Its ready waits.
       /\ WF_vars(\E x \in Things : Rerun(t, x))
       \* Taking its inbox.
       /\ WF_vars(Take(t))
       \* Handling its notes.
       /\ WF_vars(Handle(t))
       \* Claiming.
       /\ WF_vars(\E u \in Ids : Claim(t, u))
       \* Finishing what it claimed.
       /\ WF_vars(\E u \in Ids : Finish(t, u))
       \* Waking when woken.
       /\ WF_vars(Wake(t))
       \* The bug's second half (the real code has none).
       /\ WF_vars(MarkIdle(t))
  \* Every finisher tells every queue it owes.
  /\ \A u \in Ids : WF_vars(\E q \in Threads : Tell(u, q))
  \* Close, once it began, lets every free unit go.
  /\ \A u \in Ids : WF_vars(Release(u))
  \* Background work catches up: every stall clears in the end.
  /\ \A s \in Stalls : WF_vars(Clear(s))

-----------------------------------------------------------------------------
\* WHAT MUST ALWAYS HOLD

\* Every variable holds the kind of value it should.
TypeOK ==
  \* Table entries are unit numbers or none.
  /\ table \in [Things -> Ids \cup {NoUnit}]
  \* Each unit reads a thing, or nothing yet.
  /\ what \in [Ids -> Things \cup {NoUnit}]
  \* Each unit is in one of four states.
  /\ state \in [Ids -> {"none", "free", "claimed", "done"}]
  \* Each unit has one of three outcomes.
  /\ outcome \in [Ids -> {"none", "landed", "released"}]
  \* Waiter lists are sets of queues.
  /\ waiters \in [Ids -> SUBSET Threads]
  \* SHUT flags are booleans.
  /\ shut \in [Ids -> BOOLEAN]
  \* Inboxes are sequences of notes.
  /\ \A q \in Threads : \A i \in 1..Len(inbox[q]) : inbox[q][i] \in Msg
  \* Taken notes are notes too.
  /\ \A q \in Threads : \A i \in 1..Len(taken[q]) : taken[q][i] \in Msg
  \* Waits have one of three values.
  /\ slot \in [Threads -> [Things -> {"none", "pending", "ready"}]]
  \* Owners are busy or idle.
  /\ own \in [Threads -> {"busy", "idle"}]
  \* Each group has a unit, or none yet.
  /\ gunit \in [Groups -> Ids \cup {NoUnit}]
  \* Synced and visible groups are groups.
  /\ synced \subseteq Groups /\ visible \subseteq Groups
  \* Stalls in force are stalls.
  /\ stalled \subseteq Stalls
  \* Stopped writes are in one of three places.
  /\ spc \in [Threads -> [Stalls -> {"none", "seen", "recheck"}]]

\* A unit's disk read runs at most once: one claim, one run.
\* Rules out: A and B both claiming block 7's unit and reading it twice.
SingleRun == \A u \in Ids : runs[u] <= 1

\* A queue is given at most one "done" note per unit, and only if it
\* registered on that unit.
\* Rules out: B being told twice, or C being told about a read it never
\* asked for.
ExactlyOnce ==
  \* For every queue and unit:
  \A q \in Threads, u \in Ids :
    \* at most one note...
    /\ told[q][u] <= 1
    \* ...and only to a queue that registered.
    /\ told[q][u] = 1 => q \in regd[u]

\* Once a finished unit has told everyone it owed, every queue that
\* registered got its note.
\* Rules out: B registering on block 7's unit and never hearing it finished.
EveryWaiterTold ==
  \* For every unit that ended and has nobody left to tell:
  \A u \in Ids : (state[u] = "done" /\ toTell[u] = {}) =>
    \* each queue that registered got exactly one note.
    \A q \in regd[u] : told[q][u] = 1

\* A read's request sits only on its own thread's queue, so only that
\* queue's poll can ever finish it.
\* Rules out: A's read recorded on B's queue, finished by B's poll on B's
\* thread, while A never hears.
OwnQueue ==
  \* In every queue's inbox and taken notes...
  \A q \in Threads :
    \* every "read" note in the inbox is from q's own reader...
    /\ \A i \in 1..Len(inbox[q]) : inbox[q][i].kind = "read" => inbox[q][i].reader = q
    \* ...and so is every one being handled.
    /\ \A i \in 1..Len(taken[q]) : taken[q][i].kind = "read" => taken[q][i].reader = q

\* An idle owner that nobody has woken has an empty inbox.
\* Rules out: B going to sleep right as A's "done" note lands, sleeping
\* forever with the note unread.
NoLostIdleWakeup ==
  \* For every thread: asleep and not woken means nothing in the inbox.
  \A t \in Threads : (own[t] = "idle" /\ ~woken[t]) => inbox[t] = <<>>

\* Only an idle owner is ever woken.
\* Rules out: a note waking A while A is busy running its own reads.
BusyNeverWoken ==
  \* For every thread: a fired waker means the thread was asleep.
  \A t \in Threads : woken[t] => own[t] = "idle"

\* Every free unit in the table is held by some queue (registered there, or
\* on its way in a "read" note), so some poll will run it.
\* Rules out: a job started with no queue, which no poll ever runs.
NoOrphanUnit ==
  \* For every block or job:
  \A x \in Things :
    \* If the table holds a free unit for x...
    (table[x] # NoUnit /\ state[table[x]] = "free") =>
      \* ...some queue holds it.
      Held(table[x])

\* A group is visible only once its fsync ran: an Immediate commit a
\* reader saw survives a power cut.
\* Rules out: group 4 visible as soon as its leader wrote it, before the
\* fsync a member's poll will run.
VisibleAfterSync == visible \subseteq synced

\* A ticket (any wait) becomes ready only at its own thread's poll: no
\* other thread's step makes it ready.
\* Rules out: B landing group 4 and making A's ticket ready on B's thread,
\* running A's callbacks there, while A is busy.
DeliveredOnOwnPoll == offPoll = {}

\* A cleared stall leaves no unlanded unit behind, except one a writer is
\* about to land on its second look.
\* Rules out: the clearer looking before the writer installed its unit, and
\* the writer never looking again, so its write waits forever.
StallLandsWhenClear ==
  \* For every stall:
  \A s \in Stalls :
    \* If it cleared and the table still holds an unlanded unit for it...
    (s \notin stalled /\ table[s] # NoUnit /\ state[table[s]] = "free") =>
      \* ...some writer has registered and is about to look again.
      \E t \in Threads : spc[t][s] = "recheck"

\* Over a whole run: every thread's reads, jobs, commits and writes all
\* finish. With one thread this is the wasm case: it finishes everything
\* by itself.
AllDone == <>(\A t \in Threads : done[t] = Goal(t))

-----------------------------------------------------------------------------
\* THE SETUPS THE CONFIGURATIONS NAME

\* Two threads: thread 1 reads blocks 1 and 2, thread 2 reads block 1 (the
\* block both miss; block 2 is thread 1's alone).
WantPool == [t \in {1, 2} |-> IF t = 1 THEN {1, 2} ELSE {1}]
\* No jobs in that setup.
JobOfNone == [j \in {} |-> 1]
\* Two threads that both read block 1, while thread 2's call starts job 3.
WantJobs == [t \in {1, 2} |-> {1}]
\* Job 3 belongs to thread 2.
JobOfJobs == [j \in {3} |-> 2]
\* One thread reads both blocks and starts the job itself.
WantSingle == [t \in {1} |-> {1, 2}]
\* Job 3 belongs to the one thread.
JobOfSingle == [j \in {3} |-> 1]
\* No groups in a setup.
MembersNone == [g \in {} |-> {}]
\* No stalls in a setup.
StoppedNone == [s \in {} |-> {}]
\* No reads in a setup.
WantNone == [t \in {1, 2} |-> {}]
\* Group 4 has members on threads 1 and 2.
MembersBoth == [g \in {4} |-> {1, 2}]
\* Stall 5 stops writes on threads 1 and 2.
StoppedBoth == [s \in {5} |-> {1, 2}]

====
