---- MODULE SyncRwLock ----
\* ===========================================================================
\* THE STORY
\* ===========================================================================
\* A reader-writer lock lets many tasks read at once, or one task write, but
\* never both. regolith's (src/sync/rwlock.rs, src/sync/raw_rwlock.rs and
\* src/sync/reentrant_rwlock.rs) is for async code: a task that cannot enter joins a
\* queue and is woken later instead of blocking its thread.
\*
\* Like the Mutex of Sync.tla it allows "barging": a request that fits the
\* lock right now enters, even past the queue. Tiny example of why that
\* needs a limit: a writer waits; readers keep arriving so that at every
\* moment some reader is inside. Each time a reader leaves, the writer is
\* woken, finds another reader still inside, and loses. Without a limit it
\* waits for ever. So a waiter counts its lost races, and after Bound of
\* them the lock stops letting newcomers in: the readers inside drain, and
\* the lock goes straight to the writer.
\*
\* The lock also has an "upgradable read": a read guard that can later
\* become the write guard without letting go in between. Tiny example of
\* what can go wrong there: if ANY reader could upgrade, two readers could
\* both ask; each waits for the other to leave, and neither does. So only
\* one upgradable guard exists at a time, and while it waits to upgrade no
\* new plain reader is let in.
\*
\* What this model shows, over every interleaving of three tasks: a writer
\* is alone, nobody loses more than Bound races, a handoff cannot be
\* barged, an upgrade never deadlocks and never waits behind new readers,
\* an owner never queues behind itself, and no waiter sleeps beside a lock
\* it could enter. Each planted bug breaks one of these.
\*
\* The locks covered: RwLock and ReentrantRwLock after D49 (barging with
\* bounded bypass between readers and writers) and D50 (the upgradable
\* read). The code differs from the model in who raises the owed bit and in
\* whom a release wakes, exactly as Sync.tla's header describes for the
\* Mutex ("WHERE THE CODE DIFFERS"); in addition the code wakes the readers
\* at the front of the queue together (src/sync/raw_rwlock.rs), where this
\* model wakes the head and lets each entering reader wake the next.
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/Sync.lean: the
\* barging lock's laws (mutual_exclusion, bounded_bypass, owed_exclusive)
\* for an exclusive lock, which this lock's write side follows. The
\* reader-writer sharing, the upgradable read and the reentrant owner rules
\* are checked here only, for three tasks; no Lean theorem covers them.
\*
\* THE DESIGN.
\*   - D49, as for the Mutex (Sync.tla): a fast path that succeeds whenever
\*     the request fits the lock's state and no handoff is owed, even with
\*     waiters queued (readers barge past waiting writers, writers past
\*     waiting readers); every release with waiters wakes the head waiter,
\*     which competes when polled; a head that loses keeps its place and
\*     counts the loss; once it has lost Bound times the next release sets
\*     the owed bit, which shuts barging, and when the holders have drained
\*     the lock passes straight to the head.
\*   - D50, `upgradable_read()`: at most one upgradable guard at a time. It
\*     coexists with plain readers and excludes writers and other
\*     upgradable guards. `upgrade()` holds new plain readers back, waits
\*     for the plain readers to drain, then holds write. Only one upgrader
\*     can exist, and plain readers never wait on the lock while holding a
\*     guard, so an upgrade never deadlocks. Plain read guards have no
\*     upgrade method.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - The queue mechanics. Registration with the re-check, the drain token,
\*     the node CAS and the woken bit are Sync.tla's, checked there step by
\*     step for the same protocol. Here a registration with its re-check, a
\*     release with the decisions it triggers, a poll and a cancel are each
\*     one step; the wakes a step decides are separate steps, so handoff
\*     before wake is still checked.
\*   - Memory ordering is loom's (plan 7.1).
\*
\* DESIGN CHOICES WHERE THE NOTES ARE SILENT, recorded in the report.
\*   - A release wakes the head even when its request does not fit yet (a
\*     writer while readers remain): it competes and counts the loss. Only
\*     so does a writer facing readers that keep overlapping reach Bound.
\*   - A waiter that takes the lock, or is cancelled, wakes the next head
\*     if that head's request fits now (consecutive readers enter one after
\*     another; a dropped head's wake is not lost). An owed handoff passes
\*     to the next head, or clears when nobody waits.
\*   - A poll counts a loss only if its own node was notified, which is the
\*     node's woken bit set by the release that woke it; a spurious poll (a
\*     stale wake meant for a node since served or dropped) re-registers
\*     without counting. Counting every poll as a loss let one release's
\*     late wake cost a re-registered waiter a second loss with no release
\*     in between to hand it the lock, past Bound (TLC found it).
\*   - The upgradable read is on the plain RwLock. ReentrantRwLock keeps its
\*     re-entry rules (read under the owner's read or write, write under
\*     its write) and has no upgrade: a task holding only read never asks
\*     for write, and the implementation refuses it.
\*
\* CONFIGURATIONS.
\*   MC_SyncRwLock_Green_Plain       RwLock, three tasks each reading,
\*                                   writing, taking upgradable reads and
\*                                   upgrading, Bound 1: every safety
\*                                   invariant.
\*   MC_SyncRwLock_Green_WriterLive  task 1 writes and upgrades, tasks 2
\*                                   and 3 read: the writer is served and
\*                                   the upgrade completes, however the
\*                                   readers overlap.
\*   MC_SyncRwLock_Green_ReaderLive  task 1 reads, tasks 2 and 3 write: the
\*                                   reader is served.
\*     (Liveness over the all-roles configuration costs minutes on one
\*     worker; these two roles carry the starvation cases.)
\*   MC_SyncRwLock_Green_Reentrant   ReentrantRwLock, tasks 1 and 2 of one
\*                                   owner nesting up to two guards: every
\*                                   safety invariant.
\*   MC_SyncRwLock_Green_ReentrantLive  the same with one guard per task:
\*                                   if no owner holds forever, every waiter
\*                                   is served.
\*   MC_SyncRwLock_Red_UnboundedBarging  the owed bit is never set: readers
\*                                   keep barging past a writer head:
\*                                   BoundedBypass.
\*   MC_SyncRwLock_Red_AnyReaderUpgrade  plain readers may upgrade (the
\*                                   removed any-reader upgrade): two wait
\*                                   for each other, NoUpgradeDeadlock.
\*   MC_SyncRwLock_Red_UpgradeNoHoldBack  new plain readers enter while an
\*                                   upgrade waits: UpgradeHoldsBack.
\*   MC_SyncRwLock_Red_OwnerUnaware  an owner's second read queues while it
\*                                   holds read: NoSelfDeadlock.

\* Borrow the standard TLA+ books: counting numbers, lists, and sizes of finite sets.
EXTENDS Naturals, Sequences, FiniteSets

\* The fixed inputs a configuration chooses.
CONSTANTS
  \* The tasks that use the lock, named by positive numbers.
  Tasks,
  \* Which lock is modelled: "Plain" (RwLock, src/sync/rwlock.rs) or "Reentrant" (ReentrantRwLock,
  \* src/sync/reentrant_rwlock.rs).
  Kind,
  \* Each task's owner token, as a map from task to a positive number (Owner, src/sync/owner.rs).
  \* Tasks with the same token count as one owner.
  Owner,
  \* The largest number of guards one task holds at once.
  MaxDepth,
  \* After how many lost races a waiter is handed the lock directly: MAX_BYPASS in
  \* src/sync/contend.rs.
  Bound,
  \* The tasks whose "is eventually served" promise is checked: one per role is enough.
  Watched,
  \* What each task may ask for: a set drawn from "read", "write" and "upread" (the upgradable
  \* read). Either everything, or one role for a liveness check.
  Asks,
  \* "none" for the design, or the name of one planted bug.
  Mutant

\* The value "no owner holds write", and "no task".
NoOwner == 0
\* Every Owner token some task uses.
Owners == {Owner[t] : t \in Tasks}

\* The kind is one of the two.
ASSUME Kind \in {"Plain", "Reentrant"}
\* Tasks and owner tokens are positive numbers (0 means "none").
ASSUME Tasks \subseteq Nat \ {0} /\ Owners \subseteq Nat \ {0}
\* At least one guard may be held, the bound is at least 1, and only tasks are watched.
ASSUME MaxDepth \in Nat \ {0} /\ Bound \in Nat \ {0} /\ Watched \subseteq Tasks
\* On a plain RwLock a task holds one guard at a time and every task is its own owner.
ASSUME Kind = "Plain" => MaxDepth = 1 /\ \A t, u \in Tasks : t # u => Owner[t] # Owner[u]
\* The mutant is "none" or one of the four planted bugs.
ASSUME Mutant \in {"none", "UnboundedBarging", "AnyReaderUpgrade", "UpgradeNoHoldBack",
                   "OwnerUnaware"}

\* Configuration helpers, named in the MC_SyncRwLock_*.cfg files.
\* Every task is its own Owner (a plain RwLock).
OwnerEach == [t \in Tasks |-> t]
\* Tasks 1 and 2 share Owner 1, task 3 is Owner 2.
OwnerPair == [t \in Tasks |-> IF t = 3 THEN 2 ELSE 1]
\* Every task may make every request (the reentrant lock has no upgradable
\* read, so it never asks for one).
AsksAll == [t \in Tasks |-> IF Kind = "Plain" THEN {"read", "write", "upread"}
                            ELSE {"read", "write"}]
\* Task 1 writes and takes upgradable reads; tasks 2 and 3 only read: can
\* readers that keep overlapping starve a writer or an upgrade?
AsksWriterVsReaders == [t \in Tasks |-> IF t = 1 THEN {"write", "upread"} ELSE {"read"}]
\* Task 1 only reads; tasks 2 and 3 only write: can writers starve a reader?
AsksReaderVsWriters == [t \in Tasks |-> IF t = 1 THEN {"read"} ELSE {"write"}]

\* The state: everything that changes from one step to the next. Each line says what the variable
\* stands for in the real program.
VARIABLES
  \* How many plain read guards each task holds (RwLockReadGuard, ReentrantReadGuard).
  rd,
  \* How many write guards each task holds (RwLockWriteGuard, ReentrantWriteGuard).
  wr,
  \* Whether each task holds the upgradable guard: 1 or 0 (RwLockUpgradableReadGuard).
  up,
  \* The lock's count of plain read guards out, per owner. In the engine the readers are one count
  \* in the state word (above READER_SHIFT, src/sync/raw_rwlock.rs); the reentrant lock also
  \* remembers each owner's depth.
  rdepth,
  \* The owner that holds write, or NoOwner (the WRITER bit of the state word; the reentrant lock
  \* also records which owner).
  wowner,
  \* How many write guards are out.
  wdepth,
  \* The task that holds the upgradable guard, or 0 (the UPGRADABLE bit).
  uholder,
  \* TRUE while the upgradable holder waits to become the writer: new plain readers are held back
  \* (the UPGRADING bit).
  upgrading,
  \* The waiter queue, oldest first (the Waiter nodes of src/sync/waiter.rs).
  q,
  \* What each waiter asks for: "read", "write" or "upread" (the payload READ, WRITE or
  \* UPGRADABLE_READ of its node).
  want,
  \* The state of each task's waiter node: "none", "waiting" or "handed" (it was given the lock).
  node,
  \* Each node's count of lost races (Contend::bypass, src/sync/contend.rs).
  bypass,
  \* Model bookkeeping (a "ghost"): how many races each task lost during its current request. The
  \* promise BoundedBypass reads it.
  lost,
  \* Whether each waiter was woken since it last registered its waker (the NUDGED bit of a Waiter).
  woken,
  \* The handoff-owed bit: while it is set nobody may barge (the HANDOFF bit of the state word,
  \* src/sync/queue.rs).
  owed,
  \* The waiters each task has decided to wake and has not woken yet (the WakeList a pass fills,
  \* src/sync/waiter.rs).
  towake,
  \* Where a task goes on once it has delivered its wakes, per task.
  ret,
  \* Where each task is: "idle", "holding", "parked" (asleep in the queue), "upwait" (waiting to
  \* upgrade), "rupwait" (the same, for the planted bug), or "wake" (delivering wakes).
  pc,
  \* Model bookkeeping: TRUE once somebody entered by the fast path while a handoff was owed.
  bargedOwed,
  \* Model bookkeeping: TRUE once a plain reader entered while an upgrade was waiting.
  readInUpgrade

\* Every variable, so a step that changes none of them is a stutter.
vars == <<rd, wr, up, rdepth, wowner, wdepth, uholder, upgrading, q, want, node,
          bypass, lost, woken, owed, towake, ret, pc, bargedOwed, readInUpgrade>>

----------------------------------------------------------------------------
\* The lock's words as one record, so a guard drop and the decisions it
\* triggers compose as functions: L1 == Drop(L), L2 == Dispatch(L1).

\* The current lock state.
Lock == [rd |-> rd, wr |-> wr, up |-> up, rdepth |-> rdepth, wowner |-> wowner,
         wdepth |-> wdepth, uholder |-> uholder, upgrading |-> upgrading, q |-> q,
         node |-> node, bypass |-> bypass, lost |-> lost, woken |-> woken,
         owed |-> owed, wake |-> {}]

\* Make lock state L the next state.
Apply(L) ==
  \* The guards held and the readers' depth are L's;
  /\ rd' = L.rd /\ wr' = L.wr /\ up' = L.up /\ rdepth' = L.rdepth
  \* the write side and the upgradable holder are L's;
  /\ wowner' = L.wowner /\ wdepth' = L.wdepth /\ uholder' = L.uholder
  \* the upgrading flag, the queue, the nodes and their counts are L's;
  /\ upgrading' = L.upgrading /\ q' = L.q /\ node' = L.node /\ bypass' = L.bypass
  \* and so are the lost races, the woken bits and the owed bit.
  /\ lost' = L.lost /\ woken' = L.woken /\ owed' = L.owed

\* The set of elements of a sequence.
Range(s) == {s[i] : i \in 1..Len(s)}

\* The sum of f[x] over a finite set S.
RECURSIVE SumOf(_, _)
\* The sum over the empty set is 0.
SumOf(f, S) == IF S = {} THEN 0
               \* Otherwise pick any element x, and add f[x] to the sum over the rest.
               ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

\* No owner holds a plain read guard in L.
NoReaders(L) == \A o \in Owners : L.rdepth[o] = 0

\* A request of kind w fits lock state L now (ignoring the owed bit):
\* a read while no writer holds and no upgrade holds readers back (mutant
\* UpgradeNoHoldBack: whatever the upgrade); an upgradable read while no
\* writer and no other upgradable guard hold; a write while nobody holds.
Fits(L, w) ==
  \* A read: nobody holds write, and no upgrade is holding readers back (the bug UpgradeNoHoldBack
  \* ignores the upgrade).
  CASE w = "read"   -> L.wowner = NoOwner /\ (~L.upgrading \/ Mutant = "UpgradeNoHoldBack")
    \* An upgradable read: nobody holds write, and nobody holds the upgradable guard.
    [] w = "upread" -> L.wowner = NoOwner /\ L.uholder = 0
    \* A write: nobody holds write, no plain reader is in, and nobody holds the upgradable guard.
    [] OTHER        -> L.wowner = NoOwner /\ NoReaders(L) /\ L.uholder = 0

\* Task t enters lock state L with a guard of kind w.
Enter(L, t, w) ==
  \* A read:
  CASE w = "read" ->
         \* the task holds one more read guard,
         [L EXCEPT !.rd = [@ EXCEPT ![t] = @ + 1],
                   \* and its owner's read depth goes up by one.
                   !.rdepth = [@ EXCEPT ![Owner[t]] = @ + 1]]
    \* An upgradable read:
    [] w = "upread" ->
         \* the task holds the upgradable guard, and the lock names it as the holder.
         [L EXCEPT !.up = [@ EXCEPT ![t] = 1], !.uholder = t]
    \* A write:
    [] OTHER ->
         \* the task holds one more write guard, its owner holds write,
         [L EXCEPT !.wr = [@ EXCEPT ![t] = @ + 1], !.wowner = Owner[t],
                   \* and one more write guard is out.
                   !.wdepth = @ + 1]

\* The head is served by handoff: one is owed already, or it has lost
\* Bound times. (Mutant UnboundedBarging: only if owed already.)
HandoffMode(L, h) == L.owed \/ (L.bypass[h] >= Bound /\ Mutant # "UnboundedBarging")

\* Task h is woken already, or a wake for it is decided and not delivered.
Notified(L, h) == L.woken[h] \/ h \in L.wake \/ \E d \in Tasks : h \in towake[d]

\* Wake task h: its woken bit is set when the wake is delivered (by the
\* deciding task, in later steps); here it joins the wake list.
WakeIn(L, h) == [L EXCEPT !.wake = @ \cup {h}]

\* The queue step after anything that may let the head proceed. With
\* nobody queued, an owed bit clears. In handoff mode the owed bit is set
\* and, if the head's request fits, the lock passes to it: it is popped,
\* holds its guard, and is woken. Otherwise the head is woken if it is not
\* already and either `release` says a release just happened (it then
\* competes, even if it does not fit) or its request fits now.
QueueStep(L, release) ==
  \* Nobody is queued: an owed handoff has nobody left to go to, so the bit clears.
  IF L.q = <<>> THEN [L EXCEPT !.owed = FALSE]
  \* Otherwise h is the head of the queue.
  ELSE LET h == Head(L.q) IN
       \* In handoff mode:
       IF HandoffMode(L, h)
         \* if the head's request fits now,
         THEN IF Fits(L, want[h])
                \* the head enters, the owed bit is set,
                THEN WakeIn([Enter(L, h, want[h]) EXCEPT !.owed = TRUE,
                               \* its node is marked handed,
                               !.node = [@ EXCEPT ![h] = "handed"],
                               \* it leaves the queue, and it is to be woken;
                               !.q = Tail(@)], h)
                \* if it does not fit yet, only the owed bit is set: barging is shut until it does.
                ELSE [L EXCEPT !.owed = TRUE]
         \* Not in handoff mode: if nobody has woken the head or decided to, and a release just
         \* happened or its request fits,
         ELSE IF ~Notified(L, h) /\ (release \/ Fits(L, want[h]))
                \* the head is to be woken;
                THEN WakeIn(L, h)
                \* otherwise nothing changes.
                ELSE L

\* The upgrade step: an upgradable holder that waits gets write once no
\* plain reader remains (it is woken). Mutant AnyReaderUpgrade: a plain
\* reader waiting to upgrade gets write once it is the only reader.
UpgradeStep(L) ==
  \* An upgradable holder is waiting to upgrade, no plain reader is left,
  IF L.upgrading /\ L.uholder # 0 /\ pc[L.uholder] = "upwait" /\ NoReaders(L)
     \* and nobody holds write:
     /\ L.wowner = NoOwner
    \* u: that holder.
    THEN LET u == L.uholder IN
         \* It gives up the upgradable guard,
         WakeIn([L EXCEPT !.up = [@ EXCEPT ![u] = 0], !.uholder = 0,
                          \* the upgrade is no longer waiting,
                          !.upgrading = FALSE,
                          \* it holds one write guard for its owner,
                          !.wr = [@ EXCEPT ![u] = 1], !.wowner = Owner[u],
                          \* one write guard is out, and it is to be woken.
                          !.wdepth = 1], u)
  \* The bug AnyReaderUpgrade: an upgrade is waiting, nobody holds write or the upgradable guard,
  ELSE IF Mutant = "AnyReaderUpgrade" /\ L.upgrading /\ L.wowner = NoOwner /\ L.uholder = 0
       \* and some reader waiting to upgrade holds every read guard there is:
       /\ \E r \in Tasks : pc[r] = "rupwait" /\ SumOf(L.rd, Tasks) = L.rd[r]
    \* r: that reader.
    THEN LET r == CHOOSE x \in Tasks : pc[x] = "rupwait" /\ SumOf(L.rd, Tasks) = L.rd[x] IN
         \* It gives up its read guard,
         WakeIn([L EXCEPT !.rd = [@ EXCEPT ![r] = 0],
                          \* its owner's read depth drops,
                          !.rdepth = [@ EXCEPT ![Owner[r]] = @ - L.rd[r]],
                          \* the upgrade is no longer waiting,
                          !.upgrading = FALSE,
                          \* it holds one write guard for its owner,
                          !.wr = [@ EXCEPT ![r] = 1], !.wowner = Owner[r],
                          \* one write guard is out, and it is to be woken.
                          !.wdepth = 1], r)
  \* Otherwise nothing changes.
  ELSE L

\* Everything a release triggers: the upgrade step, then the queue step.
Dispatch(L) == QueueStep(UpgradeStep(L), TRUE)

\* Task t drops one plain read guard.
DropRead(L, t) ==
  \* The task holds one read guard fewer, and its owner's read depth drops by one.
  [L EXCEPT !.rd = [@ EXCEPT ![t] = @ - 1], !.rdepth = [@ EXCEPT ![Owner[t]] = @ - 1]]

\* Task t drops one write guard; the last one frees write.
DropWrite(L, t) ==
  \* The task holds one write guard fewer, one fewer is out,
  [L EXCEPT !.wr = [@ EXCEPT ![t] = @ - 1], !.wdepth = @ - 1,
            \* and when that was the last one nobody holds write.
            !.wowner = IF L.wdepth = 1 THEN NoOwner ELSE L.wowner]

\* Task t drops its upgradable guard.
DropUp(L, t) == [L EXCEPT !.up = [@ EXCEPT ![t] = 0], !.uholder = 0]

\* Task t ends its step with lock state L: it goes on to deliver L's wakes
\* (if any), then resumes at `next`. Undelivered wakes addressed to the
\* requests of the tasks in `gone`, which have just left the queue, are
\* dropped: a wake belongs to a node, and one reaching a task whose node is
\* gone finds no notified node, so the poll it causes is spurious and
\* counts no loss (design rule below).
FinishDrop(t, L, next, gone) ==
  \* The lock takes the state L.
  /\ Apply(L)
  \* Are there wakes to deliver?
  /\ IF L.wake = {}
       \* No: the task goes straight on,
       THEN /\ pc' = [pc EXCEPT ![t] = next]
            \* stale wakes for requests that just left the queue are dropped,
            /\ towake' = [d \in Tasks |-> towake[d] \ gone]
            \* and it has nowhere to come back to.
            /\ UNCHANGED ret
       \* Yes: the task goes to deliver them,
       ELSE /\ pc' = [pc EXCEPT ![t] = "wake"]
            \* its wake list is L's (others drop their stale wakes for the requests that left),
            /\ towake' = [d \in Tasks |-> IF d = t THEN L.wake ELSE towake[d] \ gone]
            \* and it remembers where to go on afterwards.
            /\ ret' = [ret EXCEPT ![t] = next]

\* Finish with no request leaving the queue.
Finish(t, L, next) == FinishDrop(t, L, next, {})

\* Task t's Owner already holds the lock in a mode that covers a read.
OwnerCoversRead(t) ==
  \* Only the reentrant lock.
  /\ Kind = "Reentrant"
  \* Its owner holds write,
  /\ \/ wowner = Owner[t]
     \* or already holds read (the bug OwnerUnaware forgets this case).
     \/ rdepth[Owner[t]] > 0 /\ Mutant # "OwnerUnaware"

\* The guards task t holds.
Guards(t) == rd[t] + wr[t] + up[t]

----------------------------------------------------------------------------
\* Actions.

\* read(), upgradable_read() or write(), first poll, or a reentrant entry.
\* A reentrant request the owner covers enters at once. Otherwise the fast
\* path enters if the request fits and no handoff is owed, barging past any
\* waiters; if not, the task registers at the tail (and its re-check, here
\* the same instant, fails as well).
Request(t, w) ==
  \* The task is idle or holds a guard.
  /\ pc[t] \in {"idle", "holding"}
  \* It may make this kind of request.
  /\ w \in Asks[t]
  \* It may hold one more guard.
  /\ Guards(t) < MaxDepth
  \* Only the plain lock has an upgradable read.
  /\ w = "upread" => Kind = "Plain"
  \* A task holding only plain read never asks for write: no upgrade method.
  \* A write is asked only by a task that holds no read guard, or whose owner already holds write.
  /\ w = "write" => (rd[t] = 0 \/ wowner = Owner[t])
  \* reenter: the request is a read its owner already covers,
  /\ LET reenter == \/ w = "read" /\ OwnerCoversRead(t)
                    \* or a write on a reentrant lock whose owner already holds write.
                    \/ w = "write" /\ Kind = "Reentrant" /\ wowner = Owner[t]
     \* Re-entering:
     IN IF reenter
          \* the task enters at once,
          THEN /\ Apply(Enter(Lock, t, w))
               \* and holds.
               /\ pc' = [pc EXCEPT ![t] = "holding"]
               \* Nothing else changes.
               /\ UNCHANGED <<want, towake, ret, bargedOwed, readInUpgrade>>
        \* Otherwise, if the request fits and no handoff is owed:
        ELSE IF Fits(Lock, w) /\ ~owed
          \* the task enters by the fast path, past any waiters,
          THEN /\ Apply(Enter(Lock, t, w))
               \* and holds.
               /\ pc' = [pc EXCEPT ![t] = "holding"]
               \* (The check is recorded for the promise HandoffExclusive; it stays false here
               \* because the owed bit was just tested.)
               /\ bargedOwed' = (bargedOwed \/ owed)
               \* If this was a plain read while an upgrade was waiting, that is recorded.
               /\ readInUpgrade' = (readInUpgrade \/ (w = "read" /\ upgrading))
               \* Nothing else changes.
               /\ UNCHANGED <<want, towake, ret>>
        \* Otherwise the task joins the tail of the queue,
        ELSE /\ q' = Append(q, t)
             \* its node is waiting,
             /\ node' = [node EXCEPT ![t] = "waiting"]
             \* it remembers what it asked for,
             /\ want' = [want EXCEPT ![t] = w]
             \* its node's count of lost races starts at 0,
             /\ bypass' = [bypass EXCEPT ![t] = 0]
             \* so do its lost races,
             /\ lost' = [lost EXCEPT ![t] = 0]
             \* it has not been woken,
             /\ woken' = [woken EXCEPT ![t] = FALSE]
             \* and it goes to sleep.
             /\ pc' = [pc EXCEPT ![t] = "parked"]
             \* The lock itself is untouched.
             /\ UNCHANGED <<rd, wr, up, rdepth, wowner, wdepth, uholder, upgrading,
                            owed, towake, ret, bargedOwed, readInUpgrade>>

\* A guard drops; everything it triggers happens with it.
Release(t) ==
  \* The task holds a guard.
  /\ pc[t] = "holding"
  \* It drops a read guard, and everything that sets off happens with it; it keeps holding if
  \* another guard is left.
  /\ \/ rd[t] > 0 /\ Finish(t, Dispatch(DropRead(Lock, t)), IF Guards(t) > 1 THEN "holding" ELSE "idle")
     \* Or it drops a write guard, likewise.
     \/ wr[t] > 0 /\ Finish(t, Dispatch(DropWrite(Lock, t)), IF Guards(t) > 1 THEN "holding" ELSE "idle")
     \* Or it drops its upgradable guard (not while its upgrade is waiting), and is idle.
     \/ up[t] > 0 /\ ~upgrading /\ Finish(t, Dispatch(DropUp(Lock, t)), "idle")
  \* Nothing else changes.
  /\ UNCHANGED <<want, bargedOwed, readInUpgrade>>

\* upgrade() on the upgradable guard: with no plain reader left, write at
\* once; otherwise hold new plain readers back and wait for them to drain.
Upgrade(t) ==
  \* The task holds a guard,
  /\ pc[t] = "holding"
  \* the upgradable one.
  /\ up[t] = 1
  \* Is any plain reader in?
  /\ IF NoReaders(Lock)
       \* No: it gives up the upgradable guard,
       THEN /\ up' = [up EXCEPT ![t] = 0]
            \* the lock names no upgradable holder,
            /\ uholder' = 0
            \* it holds one write guard,
            /\ wr' = [wr EXCEPT ![t] = 1]
            \* for its owner,
            /\ wowner' = Owner[t]
            \* and one write guard is out.
            /\ wdepth' = 1
            \* No upgrade is waiting, and the task goes on holding.
            /\ UNCHANGED <<upgrading, pc>>
       \* Yes: the upgrade waits, which holds new plain readers back,
       ELSE /\ upgrading' = TRUE
            \* and the task waits for the readers to leave.
            /\ pc' = [pc EXCEPT ![t] = "upwait"]
            \* It still holds the upgradable guard.
            /\ UNCHANGED <<up, uholder, wr, wowner, wdepth>>
  \* Nothing else changes.
  /\ UNCHANGED <<rd, rdepth, q, want, node, bypass, lost, woken, owed, towake, ret,
                 bargedOwed, readInUpgrade>>

\* Mutant AnyReaderUpgrade only: a plain reader asks to upgrade, holds new
\* readers back, and waits to be the only reader. (The upgradable guard
\* stays unused in that configuration.)
ReaderUpgrade(t) ==
  \* Only under the bug AnyReaderUpgrade.
  /\ Mutant = "AnyReaderUpgrade"
  \* The task holds a guard:
  /\ pc[t] = "holding"
  \* exactly one plain read guard, and nobody holds the upgradable guard.
  /\ rd[t] = 1 /\ wr[t] = 0 /\ up[t] = 0 /\ uholder = 0
  \* Its upgrade waits, which holds new plain readers back.
  /\ upgrading' = TRUE
  \* It waits to be the only reader.
  /\ pc' = [pc EXCEPT ![t] = "rupwait"]
  \* Nothing else changes.
  /\ UNCHANGED <<rd, wr, up, rdepth, wowner, wdepth, uholder, q, want, node, bypass,
                 lost, woken, owed, towake, ret, bargedOwed, readInUpgrade>>

\* A task delivers the wakes it decided, one per step, after the handoffs
\* they announce.
Wake(t) ==
  \* The task is delivering wakes.
  /\ pc[t] = "wake"
  \* None left?
  /\ IF towake[t] = {}
       \* Then it goes where it meant to go,
       THEN /\ pc' = [pc EXCEPT ![t] = ret[t]]
            \* and that memory is cleared.
            /\ ret' = [ret EXCEPT ![t] = "idle"]
            \* Nothing is woken.
            /\ UNCHANGED <<woken, towake>>
       \* Otherwise it picks one waiter u from its list:
       ELSE \E u \in towake[t] :
              \* u is woken,
              /\ woken' = [woken EXCEPT ![u] = TRUE]
              \* and leaves the list.
              /\ towake' = [towake EXCEPT ![t] = @ \ {u}]
              \* The task stays here for the rest.
              /\ UNCHANGED <<pc, ret>>
  \* Nothing else changes.
  /\ UNCHANGED <<rd, wr, up, rdepth, wowner, wdepth, uholder, upgrading, q, want,
                 node, bypass, lost, owed, bargedOwed, readInUpgrade>>

\* The executor polls a woken waiter. Handed: it holds its guard; the owed
\* bit clears. Otherwise it tries its fast path (only the head is ever
\* woken, and an owed handoff is its own): entering, it leaves the queue.
\* Either way the next head is woken if its request fits now. Losing: it
\* keeps its place, counts the loss, and registers its waker again.
Poll(t) ==
  \* The task is asleep in the queue.
  /\ pc[t] = "parked"
  \* It was woken.
  /\ woken[t]
  \* Its node was handed the lock:
  /\ IF node[t] = "handed"
       \* its node is gone,
       THEN FinishDrop(t, QueueStep([Lock EXCEPT !.node = [@ EXCEPT ![t] = "none"],
                                         \* its woken bit is cleared,
                                         !.woken = [@ EXCEPT ![t] = FALSE],
                                         \* the handoff is no longer owed,
                                         !.owed = FALSE,
                                         \* its node's count is forgotten,
                                         !.bypass = [@ EXCEPT ![t] = 0],
                                         \* so are its lost races; the next head is looked at, and
                                         \* the task holds.
                                         !.lost = [@ EXCEPT ![t] = 0]], FALSE), "holding", {t})
     \* Its request fits and no handoff is owed:
     ELSE IF Fits(Lock, want[t]) /\ ~owed
       \* it enters by the fast path;
       THEN FinishDrop(t, QueueStep([Enter(Lock, t, want[t]) EXCEPT
                                         \* its node is gone,
                                         !.node = [@ EXCEPT ![t] = "none"],
                                         \* its woken bit is cleared,
                                         !.woken = [@ EXCEPT ![t] = FALSE],
                                         \* it leaves the queue,
                                         !.q = SelectSeq(@, LAMBDA u : u # t),
                                         \* its node's count is forgotten,
                                         !.bypass = [@ EXCEPT ![t] = 0],
                                         \* so are its lost races; the next head is looked at, and
                                         \* the task holds.
                                         !.lost = [@ EXCEPT ![t] = 0]], FALSE), "holding", {t})
     \* It lost the race: one more lost race is counted,
     ELSE /\ lost' = [lost EXCEPT ![t] = @ + 1]
          \* its node's count goes up by one,
          /\ bypass' = [bypass EXCEPT ![t] = @ + 1]
          \* and its woken bit is cleared, so the next release wakes it again.
          /\ woken' = [woken EXCEPT ![t] = FALSE]
          \* It keeps its place; nothing else changes.
          /\ UNCHANGED <<rd, wr, up, rdepth, wowner, wdepth, uholder, upgrading, q,
                         node, owed, towake, ret, pc>>
  \* Nothing else changes.
  /\ UNCHANGED <<want, bargedOwed, readInUpgrade>>

\* The upgrader, woken after the last plain reader left, holds write.
UpPoll(t) ==
  \* The task waits to upgrade.
  /\ pc[t] \in {"upwait", "rupwait"}
  \* It was woken,
  /\ woken[t]
  \* and it holds write now (the upgrade step gave it).
  /\ wr[t] > 0
  \* Its woken bit is cleared.
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  \* It holds.
  /\ pc' = [pc EXCEPT ![t] = "holding"]
  \* Nothing else changes.
  /\ UNCHANGED <<rd, wr, up, rdepth, wowner, wdepth, uholder, upgrading, q, want, node,
                 bypass, lost, owed, towake, ret, bargedOwed, readInUpgrade>>

\* The pending future is dropped. A waiting node leaves the queue, and the
\* next head is woken if its request fits (a wake the dropped head had is
\* passed on; an owed handoff passes to it, or clears). A handed one drops
\* the guard it was handed, through the same steps as a release.
Cancel(t) ==
  \* The task is asleep in the queue.
  /\ pc[t] = "parked"
  \* L0: the lock with the task's node gone,
  /\ LET L0 == [Lock EXCEPT !.node = [@ EXCEPT ![t] = "none"],
                            \* its woken bit cleared,
                            !.woken = [@ EXCEPT ![t] = FALSE],
                            \* its node's count forgotten,
                            !.bypass = [@ EXCEPT ![t] = 0],
                            \* and its lost races forgotten.
                            !.lost = [@ EXCEPT ![t] = 0]]
     \* Its node was still waiting:
     IN IF node[t] = "waiting"
          \* it leaves the queue, the next head is looked at,
          THEN FinishDrop(t, QueueStep([L0 EXCEPT !.q = SelectSeq(@, LAMBDA u : u # t)], FALSE),
                          \* and the task is idle.
                          "idle", {t})
        \* Its node had been handed a read guard: it drops that guard, as a release would.
        ELSE IF want[t] = "read" THEN FinishDrop(t, Dispatch(DropRead(L0, t)), "idle", {t})
        \* Handed the upgradable guard: it drops that.
        ELSE IF want[t] = "upread" THEN FinishDrop(t, Dispatch(DropUp(L0, t)), "idle", {t})
        \* Handed a write guard: it drops that.
        ELSE FinishDrop(t, Dispatch(DropWrite(L0, t)), "idle", {t})
  \* Nothing else changes.
  /\ UNCHANGED <<want, bargedOwed, readInUpgrade>>

----------------------------------------------------------------------------
\* The specification.

\* The start: nobody holds, nobody waits.
Init ==
  \* Nobody holds a read guard.
  /\ rd = [t \in Tasks |-> 0]
  \* Nobody holds a write guard.
  /\ wr = [t \in Tasks |-> 0]
  \* Nobody holds the upgradable guard.
  /\ up = [t \in Tasks |-> 0]
  \* No owner has a read depth.
  /\ rdepth = [o \in Owners |-> 0]
  \* No owner holds write.
  /\ wowner = NoOwner
  \* No write guard is out.
  /\ wdepth = 0
  \* Nobody holds the upgradable guard, says the lock.
  /\ uholder = 0
  \* No upgrade is waiting.
  /\ upgrading = FALSE
  \* The queue is empty.
  /\ q = <<>>
  \* No waiter asks for anything yet (a placeholder value).
  /\ want = [t \in Tasks |-> "read"]
  \* No task has a node.
  /\ node = [t \in Tasks |-> "none"]
  \* No node has lost a race.
  /\ bypass = [t \in Tasks |-> 0]
  \* No task has lost a race.
  /\ lost = [t \in Tasks |-> 0]
  \* Nobody was woken.
  /\ woken = [t \in Tasks |-> FALSE]
  \* No handoff is owed.
  /\ owed = FALSE
  \* Nobody has wakes to deliver.
  /\ towake = [t \in Tasks |-> {}]
  \* Every task would go on to idle.
  /\ ret = [t \in Tasks |-> "idle"]
  \* Every task is idle.
  /\ pc = [t \in Tasks |-> "idle"]
  \* Nobody barged past an owed handoff.
  /\ bargedOwed = FALSE
  \* No reader entered during an upgrade.
  /\ readInUpgrade = FALSE

\* Every step the system can take.
Next ==
  \* Some task
  \E t \in Tasks :
    \* asks to read, write or take the upgradable read,
    \/ \E w \in {"read", "write", "upread"} : Request(t, w)
    \* releases a guard, upgrades, delivers a wake, is polled,
    \/ Release(t) \/ Upgrade(t) \/ ReaderUpgrade(t) \/ Wake(t) \/ Poll(t) \/ UpPoll(t)
    \* or drops its pending request.
    \/ Cancel(t)

\* Fairness: wakes are delivered, woken futures are polled, and a holder
\* eventually drops a guard. Requests, upgrades and cancels are the
\* caller's choices.
Fairness ==
  \* For every task:
  \A t \in Tasks :
    \* wakes are delivered and woken tasks are polled, sooner or later;
    /\ WF_vars(Wake(t) \/ Poll(t) \/ UpPoll(t))
    \* and a holder lets go, sooner or later.
    /\ WF_vars(Release(t))

\* Every behaviour: start in Init, take Next steps or stutter, fairly.
Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  \* Every task holds between 0 and MaxDepth read guards,
  /\ rd \in [Tasks -> 0..MaxDepth]
  \* and write guards,
  /\ wr \in [Tasks -> 0..MaxDepth]
  \* and at most one upgradable guard.
  /\ up \in [Tasks -> 0..1]
  \* Write is held by an owner or by nobody.
  /\ wowner \in Owners \cup {NoOwner}
  \* The upgradable guard is held by a task or by nobody.
  /\ uholder \in Tasks \cup {0}
  \* Every node is none, waiting or handed.
  /\ node \in [Tasks -> {"none", "waiting", "handed"}]
  \* Every task is at one of the known places.
  /\ pc \in [Tasks -> {"idle", "holding", "parked", "upwait", "rupwait", "wake"}]
  \* The queue holds tasks.
  /\ Range(q) \subseteq Tasks

\* MUTUAL EXCLUSION. While an owner holds write, no other owner holds read
\* and no upgradable guard is out; every guard is counted on the lock.
\* Lean (exclusive side): mutual_exclusion.
MutualExclusion ==
  \* While an owner holds write: nobody holds the upgradable guard, and no other owner has a read
  \* guard. Rules out a reader looking at data a writer is in the middle of changing.
  /\ wowner # NoOwner => uholder = 0 /\ \A o \in Owners \ {wowner} : rdepth[o] = 0
  \* Every task that holds a write guard belongs to the owner the lock names.
  /\ \A t \in Tasks : wr[t] > 0 => Owner[t] = wowner
  \* Every task that holds a read guard is counted in its owner's read depth.
  /\ \A t \in Tasks : rd[t] > 0 => rdepth[Owner[t]] > 0

\* AT MOST ONE UPGRADABLE GUARD, and the lock names its holder.
UpgradableExclusive ==
  \* No two tasks hold the upgradable guard.
  /\ \A t, u \in Tasks : up[t] = 1 /\ up[u] = 1 => t = u
  \* And the lock names exactly the task that holds it.
  /\ \A t \in Tasks : up[t] = 1 <=> uholder = t

\* REENTRANCY DEPTH. The lock's depths are exactly the guards out, and
\* write is held exactly when its depth is not 0.
ReentrancyDepth ==
  \* The write depth is the number of write guards out.
  /\ wdepth = SumOf(wr, Tasks)
  \* Each owner's read depth is the number of read guards its tasks hold.
  /\ \A o \in Owners : rdepth[o] = SumOf(rd, {t \in Tasks : Owner[t] = o})
  \* Nobody holds write exactly when no write guard is out.
  /\ (wowner = NoOwner <=> wdepth = 0)

\* BOUNDED BYPASS. A waiter, reader or writer, loses the race at most Bound
\* times; then a release hands it the lock. Neither side starves.
\* Lean: bounded_bypass.
\* Rules out, for example: a writer waits while readers keep arriving so that some reader is always
\* inside; every time the writer is woken it finds a reader and loses, for ever.
BoundedBypass == \A t \in Tasks : lost[t] <= Bound

\* HANDOFF EXCLUSIVE. Nobody enters through the fast path while a handoff
\* is owed. Lean: owed_blocks_barging.
\* Rules out a newcomer slipping in while the lock is being handed to a waiter that lost Bound
\* times.
HandoffExclusive == ~bargedOwed

\* UPGRADE HOLDS READERS BACK. No plain reader enters while an upgrade
\* waits.
\* Rules out, for example: an upgrade waits for the readers to leave, and new readers keep entering,
\* so it waits for ever.
UpgradeHoldsBack == ~readInUpgrade

\* NO UPGRADE DEADLOCK. Every reader an upgrader waits for is free to drop
\* its guard: it is running (holding, or delivering wakes), or it was handed
\* its guard and only awaits its own poll, which needs nothing from the
\* lock. It is never itself waiting on the lock. With one upgrader and no
\* upgrade from plain read, this holds, so every upgrade completes.
NoUpgradeDeadlock ==
  \* For every task
  \A t \in Tasks :
    \* that waits to upgrade:
    pc[t] \in {"upwait", "rupwait"} =>
      \* every other task
      \A u \in Tasks \ {t} :
        \* that holds a read guard is running, or was handed its guard and only waits to be polled.
        \* Rules out two readers each waiting to upgrade while the other still holds its read guard:
        \* neither would ever leave.
        rd[u] > 0 => (pc[u] \in {"holding", "wake"} \/ (pc[u] = "parked" /\ node[u] = "handed"))

\* NO SELF-DEADLOCK. A queued task holds no guard of the lock.
\* Rules out, for example: an owner that holds a read guard asks for another read, is queued behind
\* a waiting writer, and so waits on a lock that its own guard keeps the writer out of.
NoSelfDeadlock == \A t \in Tasks : node[t] = "waiting" => Guards(t) = 0

\* A queued head left asleep though it could proceed: its request fits,
\* nobody has woken it or decided to, and no handed waiter is still to take
\* an owed handoff (that waiter's take clears the owed bit and wakes the
\* head); or an upgrade left waiting with every plain reader gone.
Stranded ==
  \* The queue has a head,
  \/ /\ q # <<>>
     \* whose request fits and whom nobody has woken or decided to wake,
     /\ LET h == Head(q) IN Fits(Lock, want[h]) /\ ~Notified(Lock, h)
     \* and no handed waiter is about to clear an owed handoff and wake it;
     /\ ~(owed /\ \E t \in Tasks : node[t] = "handed")
  \* or an upgrade is left waiting although no plain reader is left and nobody holds write.
  \/ /\ upgrading /\ uholder # 0 /\ NoReaders(Lock) /\ wowner = NoOwner

\* NO LOST WAKEUP. A parked future handed the lock has been woken or is
\* about to be, and no head or upgrader is stranded. Lean: no_stranded_head.
NoLostWakeup ==
  \* For every task
  /\ \A t \in Tasks :
       \* that sleeps with its node marked handed: it was woken, or somebody has it on a wake list.
       pc[t] = "parked" /\ node[t] = "handed" => woken[t] \/ \E d \in Tasks : t \in towake[d]
  \* And nobody is stranded. Rules out a waiter asleep beside a lock it could take.
  /\ ~Stranded

\* CANCELLATION PASSES ON. An idle task holds no guard.
\* Rules out a waiter that was handed a guard, was dropped before it ran, and left the guard held by
\* nobody.
CancelPassesOn == \A t \in Tasks : pc[t] = "idle" => Guards(t) = 0

----------------------------------------------------------------------------
\* Liveness. Checked for the tasks in Watched: tasks with the same Owner
\* role are interchangeable, so one per role stands for all.

\* Every parked waiter stops waiting: it is served, unless it cancels.
\* Rules out a reader or writer that waits for ever although guards keep being dropped.
EveryWaiterServed == \A t \in Watched : (pc[t] = "parked") ~> (pc[t] # "parked")

\* Every upgrade completes: the upgrader comes to hold write.
\* Rules out an upgrade that never gets write.
UpgradeCompletes == \A t \in Watched : (pc[t] = "upwait") ~> (pc[t] = "holding")

\* Owner o holds the lock in some mode.
OwnerHolds(o) == rdepth[o] > 0 \/ wowner = o

\* Reentrant: no owner keeps the lock forever.
\* Each owner, again and again, holds nothing.
OwnersLetGo == \A o \in Owners : []<>(~OwnerHolds(o))

\* Reentrant: if no owner holds the lock forever, every waiter is served.
ReentrantServed == OwnersLetGo => EveryWaiterServed

====
