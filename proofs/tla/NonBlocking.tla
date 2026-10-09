---- MODULE NonBlocking ----
\* R13, non-blocking calls (plan 4.10): no regolith call waits for another
\* thread. A call that would wait returns a handle instead: a CommitTicket
\* from commit_nowait, or WouldBlock::Io(IoWait) from a CacheOnly read that
\* misses the block cache. The caller's own threads do the I/O through
\* poll_io, and wait for work on io_pending.
\*
\* NO LEAN COUNTERPART. What this model checks is about interleavings:
\* wakeups, notifications and who runs the I/O. There is no law over sizes
\* to prove, so TLC is the whole check. The commits whose tickets complete
\* here are the pipeline's slots (CommitPipeline.tla; Lean Pipeline.lean).
\*
\* THE API (4.10, 3.0).
\*   Transaction::commit_nowait -> CommitTicket
\*     Decides and writes the commit and returns at once. The ticket is a
\*     Future that resolves when the commit is durable (at Immediate) and
\*     visible. on_complete(f) runs f once, on the thread that completes
\*     the ticket, or at once if it is already complete.
\*   ReadMode::CacheOnly
\*     A read that misses the block cache never touches the device: it
\*     returns WouldBlock::Io(IoWait) and queues the block read for
\*     poll_io, once per block however many readers missed it
\*     (single-flight). IoWait is a Future that resolves when the block is
\*     cached; the read is then run again.
\*   Db::poll_io(budget) -> IoProgress { completed, more_pending }
\*     Does at most budget units of pending I/O (the durability sync, queued
\*     block reads, a flush owed with no worker, the disk check) and
\*     returns at once when none is pending.
\*   Db::io_pending() -> Notified
\*     Fires whenever regolith queues I/O, including I/O it starts itself,
\*     so the caller's I/O threads wait on it instead of polling.
\*
\* HOW A FUTURE IS POLLED HERE. A task awaiting a ticket or an IoWait first
\* registers its waker on the handle, then checks whether the handle is
\* ready, and parks only if it is not. Whoever makes a handle ready takes
\* the registered wakers and wakes them in the same step. Mutant
\* LostWakeup checks first and registers after, with no recheck: a
\* completion in between finds no waker, and the task parks on a ready
\* handle for good.
\*
\* CHOICES WHERE THE PLAN IS SILENT.
\*   - Each poll_io call does one unit (budget 1), the smallest budget. A
\*     thread that sees more_pending calls again; a larger budget runs the
\*     same units with fewer returns.
\*   - io_pending is a Notify that stores one permit when nobody waits, so
\*     a notification sent while the I/O thread is busy is not lost.
\*   - on_complete registration is one CAS on the ticket's state word: it
\*     either queues the callback for the completer or, finding the ticket
\*     complete, runs it at once. Exactly one of the two runs it.
\*   - Single-threaded wasm: one thread runs every task and calls poll_io
\*     only when no task can run. It never waits on io_pending.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - Commits at Eventual durability: their ticket is ready once applied
\*     and owes no I/O, so no wakeup can be lost on it.
\*   - The blocking commit() and get(): they run the same I/O units on the
\*     calling thread.
\*   - Cache eviction between a block's arrival and the re-read: the re-read
\*     misses again and takes the same path once more.
\*   - Write stalls (WouldBlock::Stall) and lock waits (WouldBlock::Locked):
\*     the same register-then-recheck handle, woken by a flush or a release
\*     instead of by I/O.
\*   - close(), which completes every ticket and wakes every IoWait with
\*     Closed: one more completer.
\*
\* CONFIGURATIONS.
\*   MC_NonBlocking_Green_Pool        Mode = "pool": two commits (one with a
\*     callback), two reads of one block, one self-started unit, two I/O
\*     threads on io_pending. Every invariant and the liveness properties
\*     hold.
\*   MC_NonBlocking_Green_Single      Mode = "single": one thread does it
\*     all, polling I/O when idle. Every invariant and the liveness
\*     properties hold.
\*   MC_NonBlocking_Red_LostWakeup    Mutant = "LostWakeup".
\*     NoLostWakeup fails.
\*   MC_NonBlocking_Red_SilentSelfIo  Mutant = "SilentSelfIo": I/O regolith
\*     starts itself does not fire io_pending. IoPendingFires fails.

EXTENDS Naturals, FiniteSets

CONSTANTS
  CommitTasks,  \* tasks that call commit_nowait at Immediate and await the ticket
  Callbacks,    \* the commit tasks that also register an on_complete callback
  ReadTasks,    \* tasks that read one block through a CacheOnly handle
  Blocks,       \* the blocks those reads need, none cached at the start
  BlockOf,      \* [ReadTasks -> Blocks]: the block each read needs
  IoThreads,    \* the caller's threads reserved for I/O (pool mode)
  SelfJobs,     \* how many units of I/O regolith starts itself in a run
  Mode,         \* "pool" or "single"
  Mutant        \* "none", "LostWakeup" or "SilentSelfIo"

\* Every task.
Tasks == CommitTasks \cup ReadTasks

ASSUME CommitTasks \cap ReadTasks = {}
ASSUME Callbacks \subseteq CommitTasks
ASSUME BlockOf \in [ReadTasks -> Blocks]
ASSUME SelfJobs \in Nat
ASSUME Mode \in {"pool", "single"}
ASSUME Mode = "single" => IoThreads = {}
ASSUME Mutant \in {"none", "LostWakeup", "SilentSelfIo"}

VARIABLES
  tpc,       \* [Tasks -> phase]: "start", "await" (about to poll its handle),
             \* "registered" (waker registered, recheck next), "checked"
             \* (Mutant LostWakeup: checked, not registered), "parked",
             \* "retry" (a read whose block arrived, to run again), "done"
  ticket,    \* [CommitTasks -> {"none", "pending", "complete"}]
  unsynced,  \* the commits written but not yet durable: the sync owed
  synced,    \* the commits a sync made durable
  cb,        \* [CommitTasks -> {"none", "registered", "ran"}]: on_complete
  cbRuns,    \* [CommitTasks -> Nat]: how many times the callback ran
  reg,       \* the tasks whose waker is registered on the handle they await
  cached,    \* the blocks in the block cache
  queued,    \* the block reads queued for poll_io
  devReads,  \* [Blocks -> Nat]: device reads of each block
  jobs,      \* self-started units of I/O queued (a flush with no worker,
             \* the disk check)
  started,   \* self-started units so far
  permit,    \* io_pending holds a stored notification
  io         \* [IoThreads -> {"waiting", "polling"}]

\* Every variable, so a step that changes none of them is a stutter.
vars == <<tpc, ticket, unsynced, synced, cb, cbRuns, reg, cached, queued, devReads,
          jobs, started, permit, io>>

----------------------------------------------------------------------------
\* Helpers.

\* The handle task t awaits is ready: its ticket completed, or its block is
\* cached.
Ready(t) ==
  IF t \in CommitTasks THEN ticket[t] = "complete" ELSE BlockOf[t] \in cached

\* Where task t goes once its handle is ready: a commit is done; a read
\* runs again.
After(t) == IF t \in CommitTasks THEN "done" ELSE "retry"

\* Task t can take a step: it is neither parked nor done.
Runnable(t) == tpc[t] \notin {"parked", "done"}

\* Some I/O is queued: a sync owed, a block read, or a self-started unit.
PendingIo == unsynced # {} \/ queued # {} \/ jobs > 0

\* Wake the tasks in W whose wakers are registered: a parked one runs again
\* and polls its handle anew; one between registering and its recheck
\* finds the handle ready at the recheck. Either way the waker is used up.
WakeTpc(W) == [t \in Tasks |-> IF t \in W /\ t \in reg /\ tpc[t] = "parked" THEN "await" ELSE tpc[t]]

----------------------------------------------------------------------------
\* Actions of the tasks.

\* The start: no commit, nothing cached or queued, no notification, every
\* I/O thread waiting on io_pending.
Init ==
  /\ tpc      = [t \in Tasks |-> "start"]
  /\ ticket   = [c \in CommitTasks |-> "none"]
  /\ unsynced = {}
  /\ synced   = {}
  /\ cb       = [c \in CommitTasks |-> "none"]
  /\ cbRuns   = [c \in CommitTasks |-> 0]
  /\ reg      = {}
  /\ cached   = {}
  /\ queued   = {}
  /\ devReads = [b \in Blocks |-> 0]
  /\ jobs     = 0
  /\ started  = 0
  /\ permit   = FALSE
  /\ io       = [th \in IoThreads |-> "waiting"]

\* Commit task c calls commit_nowait: the commit is decided and written, a
\* sync is owed, io_pending fires, and c holds a pending ticket.
CommitNowait(c) ==
  /\ tpc[c] = "start"
  /\ tpc'      = [tpc EXCEPT ![c] = "await"]
  /\ ticket'   = [ticket EXCEPT ![c] = "pending"]
  /\ unsynced' = unsynced \cup {c}
  /\ permit'   = TRUE
  /\ UNCHANGED <<synced, cb, cbRuns, reg, cached, queued, devReads, jobs, started, io>>

\* Commit task c registers its on_complete callback with one CAS: queued
\* for the completer while the ticket is pending, run at once on c's own
\* thread when the ticket is already complete.
OnComplete(c) ==
  /\ c \in Callbacks
  /\ cb[c] = "none"
  /\ tpc[c] = "await"
  /\ IF ticket[c] = "complete"
       THEN /\ cb'     = [cb EXCEPT ![c] = "ran"]
            /\ cbRuns' = [cbRuns EXCEPT ![c] = @ + 1]
       ELSE /\ cb'     = [cb EXCEPT ![c] = "registered"]
            /\ UNCHANGED cbRuns
  /\ UNCHANGED <<tpc, ticket, unsynced, synced, reg, cached, queued, devReads, jobs, started,
                 permit, io>>

\* Read task r reads its block through a CacheOnly handle. A hit finishes
\* it. A miss returns WouldBlock::Io(IoWait) without touching the device and
\* queues the block read, unless one is already queued (single-flight);
\* queuing it fires io_pending.
Read(r) ==
  LET b == BlockOf[r]
  IN /\ tpc[r] \in {"start", "retry"}
     /\ IF b \in cached
          THEN /\ tpc' = [tpc EXCEPT ![r] = "done"]
               /\ UNCHANGED <<queued, permit>>
          ELSE /\ tpc'    = [tpc EXCEPT ![r] = "await"]
               /\ queued' = queued \cup {b}
               /\ permit' = IF b \in queued THEN permit ELSE TRUE
     /\ UNCHANGED <<ticket, unsynced, synced, cb, cbRuns, reg, cached, devReads, jobs, started,
                    io>>

\* A commit task registers its callback before it awaits, if it has one.
CallbackSettled(t) == t \in CommitTasks /\ t \in Callbacks => cb[t] # "none"

\* Polling, first half. The fix: register the waker. Mutant LostWakeup:
\* check readiness first, without registering.
PollFirst(t) ==
  /\ tpc[t] = "await"
  /\ CallbackSettled(t)
  /\ IF Mutant = "LostWakeup"
       THEN /\ tpc' = [tpc EXCEPT ![t] = IF Ready(t) THEN After(t) ELSE "checked"]
            /\ UNCHANGED reg
       ELSE /\ tpc' = [tpc EXCEPT ![t] = "registered"]
            /\ reg'  = reg \cup {t}
  /\ UNCHANGED <<ticket, unsynced, synced, cb, cbRuns, cached, queued, devReads, jobs, started,
                 permit, io>>

\* Polling, second half. The fix: recheck readiness after registering, and
\* park only if the handle is still not ready. Mutant LostWakeup: register
\* now and park, with no recheck.
PollSecond(t) ==
  \/ /\ tpc[t] = "registered"
     /\ IF Ready(t)
          THEN /\ tpc' = [tpc EXCEPT ![t] = After(t)]
               /\ reg' = reg \ {t}
          ELSE /\ tpc' = [tpc EXCEPT ![t] = "parked"]
               /\ UNCHANGED reg
     /\ UNCHANGED <<ticket, unsynced, synced, cb, cbRuns, cached, queued, devReads, jobs, started,
                    permit, io>>
  \/ /\ tpc[t] = "checked"
     /\ tpc' = [tpc EXCEPT ![t] = "parked"]
     /\ reg' = reg \cup {t}
     /\ UNCHANGED <<ticket, unsynced, synced, cb, cbRuns, cached, queued, devReads, jobs, started,
                    permit, io>>

\* Any step of task t.
TaskStep(t) ==
  \/ t \in CommitTasks /\ (CommitNowait(t) \/ OnComplete(t))
  \/ t \in ReadTasks /\ Read(t)
  \/ PollFirst(t)
  \/ PollSecond(t)

----------------------------------------------------------------------------
\* Units of I/O. poll_io runs them, one per call; nothing else does.

\* The durability sync: every written commit becomes durable and visible,
\* and its ticket completes on this thread, in this step: the registered
\* callbacks run here, once, and the registered wakers are woken.
DoSync ==
  /\ unsynced # {}
  /\ ticket'   = [c \in CommitTasks |-> IF c \in unsynced THEN "complete" ELSE ticket[c]]
  /\ synced'   = synced \cup unsynced
  /\ unsynced' = {}
  /\ cb'       = [c \in CommitTasks |-> IF c \in unsynced /\ cb[c] = "registered" THEN "ran" ELSE cb[c]]
  /\ cbRuns'   = [c \in CommitTasks |->
                    IF c \in unsynced /\ cb[c] = "registered" THEN cbRuns[c] + 1 ELSE cbRuns[c]]
  /\ tpc'      = WakeTpc(unsynced)
  /\ reg'      = reg \ unsynced
  /\ UNCHANGED <<cached, queued, devReads, jobs, started, permit, io>>

\* A queued block read: the block is read from the device once, enters the
\* cache, and every read waiting on its IoWait is woken.
DoRead(b) ==
  LET waiters == {r \in ReadTasks : BlockOf[r] = b}
  IN /\ b \in queued
     /\ cached'   = cached \cup {b}
     /\ queued'   = queued \ {b}
     /\ devReads' = [devReads EXCEPT ![b] = @ + 1]
     /\ tpc'      = WakeTpc(waiters)
     /\ reg'      = reg \ waiters
     /\ UNCHANGED <<ticket, unsynced, synced, cb, cbRuns, jobs, started, permit, io>>

\* A self-started unit: a flush owed with no compaction worker, or the
\* disk check.
DoJob ==
  /\ jobs > 0
  /\ jobs' = jobs - 1
  /\ UNCHANGED <<tpc, ticket, unsynced, synced, cb, cbRuns, reg, cached, queued, devReads,
                 started, permit, io>>

\* One unit of pending I/O, whichever is chosen.
IoUnit == DoSync \/ (\E b \in Blocks : DoRead(b)) \/ DoJob

----------------------------------------------------------------------------
\* Who runs the I/O.

\* Pool mode, I/O thread th: io_pending fired, so it consumes the stored
\* notification and starts calling poll_io.
IoWake(th) ==
  /\ io[th] = "waiting"
  /\ permit
  /\ permit' = FALSE
  /\ io'     = [io EXCEPT ![th] = "polling"]
  /\ UNCHANGED <<tpc, ticket, unsynced, synced, cb, cbRuns, reg, cached, queued, devReads,
                 jobs, started>>

\* Pool mode: poll_io does one unit; more_pending keeps th calling.
IoPoll(th) ==
  /\ io[th] = "polling"
  /\ IoUnit

\* Pool mode: poll_io found nothing pending, so th awaits io_pending again.
IoIdle(th) ==
  /\ io[th] = "polling"
  /\ ~PendingIo
  /\ io' = [io EXCEPT ![th] = "waiting"]
  /\ UNCHANGED <<tpc, ticket, unsynced, synced, cb, cbRuns, reg, cached, queued, devReads,
                 jobs, started, permit>>

\* Any step of I/O thread th.
IoStep(th) == IoWake(th) \/ IoPoll(th) \/ IoIdle(th)

\* Single mode: the one thread's event loop calls poll_io only when no
\* task can run.
LoopIo ==
  /\ Mode = "single"
  /\ \A t \in Tasks : ~Runnable(t)
  /\ IoUnit

\* regolith queues I/O of its own (a rotation with no worker queues a
\* flush; the disk check comes due) and fires io_pending. Mutant
\* SilentSelfIo does not fire it.
SelfStart ==
  /\ started < SelfJobs
  /\ jobs'    = jobs + 1
  /\ started' = started + 1
  /\ permit'  = IF Mutant = "SilentSelfIo" THEN permit ELSE TRUE
  /\ UNCHANGED <<tpc, ticket, unsynced, synced, cb, cbRuns, reg, cached, queued, devReads, io>>

\* Every step the system can take.
Next ==
  \/ \E t \in Tasks : TaskStep(t)
  \/ \E th \in IoThreads : IoStep(th)
  \/ LoopIo
  \/ SelfStart

\* Every behaviour: start in Init, take Next steps, and never stop while a
\* step is possible. No step spins or waits, so every behaviour is finite
\* and ends where no step is possible.
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ tpc \in [Tasks -> {"start", "await", "registered", "checked", "parked", "retry", "done"}]
  /\ ticket \in [CommitTasks -> {"none", "pending", "complete"}]
  /\ unsynced \subseteq CommitTasks /\ synced \subseteq CommitTasks
  /\ cb \in [CommitTasks -> {"none", "registered", "ran"}]
  /\ reg \subseteq Tasks
  /\ cached \subseteq Blocks /\ queued \subseteq Blocks
  /\ jobs \in 0..SelfJobs /\ started \in 0..SelfJobs
  /\ permit \in BOOLEAN
  /\ io \in [IoThreads -> {"waiting", "polling"}]

\* THE HEADLINE. No lost wakeup: a parked task awaits a handle that is not
\* ready, with its waker registered, so whoever makes the handle ready
\* wakes it.
NoLostWakeup == \A t \in Tasks : tpc[t] = "parked" => ~Ready(t) /\ t \in reg

\* A ticket completes when, and only when, the I/O that makes its commit
\* durable has run.
TicketCompletesWithItsIo ==
  \A c \in CommitTasks : (ticket[c] = "complete") <=> (c \in synced)

\* on_complete runs at most once, only on a complete ticket.
CallbackOnce ==
  \A c \in CommitTasks :
    /\ cbRuns[c] <= 1
    /\ (cb[c] = "ran") <=> (cbRuns[c] = 1)
    /\ (cb[c] = "ran" => ticket[c] = "complete")

\* Single-flight: the device is read only to fill the cache, once per
\* block, however many CacheOnly reads missed it; a read never touches the
\* device itself.
SingleFlight == \A b \in Blocks : devReads[b] = IF b \in cached THEN 1 ELSE 0

\* io_pending fires whenever I/O is queued: in pool mode, while any I/O is
\* queued, an I/O thread is polling or a notification is stored to wake
\* one.
IoPendingFires ==
  Mode = "pool" /\ PendingIo => permit \/ \E th \in IoThreads : io[th] = "polling"

\* Nothing is ever stuck: when no step is possible, every task is done and
\* no I/O is queued. In single mode this is "one thread completes
\* everything".
NothingStuck == (~ENABLED Next) => (\A t \in Tasks : tpc[t] = "done") /\ ~PendingIo

----------------------------------------------------------------------------
\* Liveness.

\* Every ticket completes once its I/O runs, and its I/O does run.
EveryTicketCompletes == <>(\A c \in CommitTasks : ticket[c] = "complete")

\* Every task finishes, every registered callback has run, and no I/O is
\* left queued.
AllTasksFinish ==
  <>(/\ \A t \in Tasks : tpc[t] = "done"
     /\ \A c \in Callbacks : cbRuns[c] = 1
     /\ ~PendingIo)

----------------------------------------------------------------------------
\* Workloads, chosen by the configurations.

\* Every read needs block 1, so their misses share one queued read.
OneBlock == [r \in ReadTasks |-> 1]

====
