---- MODULE SyncRwLock ----
\* regolith::sync::RwLock and ReentrantRwLock after D49 (barging with bounded
\* bypass between readers and writers) and D50 (the upgradable read).
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

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Tasks,     \* the tasks using the lock: positive naturals
  Kind,      \* "Plain" (RwLock) or "Reentrant" (ReentrantRwLock)
  Owner,     \* [Tasks -> positive naturals]: the Owner token of each task
  MaxDepth,  \* the most guards one task holds at once
  Bound,     \* BOUND: the losses after which the next release hands off
  Watched,   \* the tasks whose liveness is checked: one per role
  Asks,      \* [Tasks -> SUBSET {"read", "write", "upread"}]: what each task
             \* may request (all of them, or a role for a liveness check)
  Mutant     \* "none" for the design, or the name of one defect

\* The value "no owner holds write", and "no task".
NoOwner == 0
\* Every Owner token some task uses.
Owners == {Owner[t] : t \in Tasks}

ASSUME Kind \in {"Plain", "Reentrant"}
ASSUME Tasks \subseteq Nat \ {0} /\ Owners \subseteq Nat \ {0}
ASSUME MaxDepth \in Nat \ {0} /\ Bound \in Nat \ {0} /\ Watched \subseteq Tasks
ASSUME Kind = "Plain" => MaxDepth = 1 /\ \A t, u \in Tasks : t # u => Owner[t] # Owner[u]
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

VARIABLES
  rd,         \* [Tasks -> Nat]: plain read guards each task holds
  wr,         \* [Tasks -> Nat]: write guards each task holds
  up,         \* [Tasks -> 0..1]: the upgradable guard, held or not
  rdepth,     \* [Owners -> Nat]: the lock's per-owner read depth
  wowner,     \* the Owner holding write, or NoOwner
  wdepth,     \* write guards out
  uholder,    \* the task holding the upgradable guard, or 0
  upgrading,  \* the upgradable holder waits to upgrade: plain readers held back
  q,          \* the waiter queue, oldest first
  want,       \* [Tasks -> {"read", "write", "upread"}]: what a waiter asks for
  node,       \* [Tasks -> {"none", "waiting", "handed"}]
  bypass,     \* [Tasks -> Nat]: the node's bypass count
  lost,       \* ghost [Tasks -> Nat]: races lost during the current request
  woken,      \* [Tasks -> BOOLEAN]: Waker::wake ran since it was registered
  owed,       \* the handoff-owed bit: barging is shut
  towake,     \* [Tasks -> SUBSET Tasks]: waiters a task has yet to wake
  ret,        \* [Tasks -> pc]: where a task resumes once its wakes are done
  pc,         \* [Tasks -> {"idle", "holding", "parked", "upwait", "rupwait", "wake"}]
  bargedOwed, \* ghost: a fast-path entry while a handoff was owed
  readInUpgrade \* ghost: a plain reader entered while an upgrade waited

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
  /\ rd' = L.rd /\ wr' = L.wr /\ up' = L.up /\ rdepth' = L.rdepth
  /\ wowner' = L.wowner /\ wdepth' = L.wdepth /\ uholder' = L.uholder
  /\ upgrading' = L.upgrading /\ q' = L.q /\ node' = L.node /\ bypass' = L.bypass
  /\ lost' = L.lost /\ woken' = L.woken /\ owed' = L.owed

\* The set of elements of a sequence.
Range(s) == {s[i] : i \in 1..Len(s)}

\* The sum of f[x] over a finite set S.
RECURSIVE SumOf(_, _)
SumOf(f, S) == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

\* No owner holds a plain read guard in L.
NoReaders(L) == \A o \in Owners : L.rdepth[o] = 0

\* A request of kind w fits lock state L now (ignoring the owed bit):
\* a read while no writer holds and no upgrade holds readers back (mutant
\* UpgradeNoHoldBack: whatever the upgrade); an upgradable read while no
\* writer and no other upgradable guard hold; a write while nobody holds.
Fits(L, w) ==
  CASE w = "read"   -> L.wowner = NoOwner /\ (~L.upgrading \/ Mutant = "UpgradeNoHoldBack")
    [] w = "upread" -> L.wowner = NoOwner /\ L.uholder = 0
    [] OTHER        -> L.wowner = NoOwner /\ NoReaders(L) /\ L.uholder = 0

\* Task t enters lock state L with a guard of kind w.
Enter(L, t, w) ==
  CASE w = "read" ->
         [L EXCEPT !.rd = [@ EXCEPT ![t] = @ + 1],
                   !.rdepth = [@ EXCEPT ![Owner[t]] = @ + 1]]
    [] w = "upread" ->
         [L EXCEPT !.up = [@ EXCEPT ![t] = 1], !.uholder = t]
    [] OTHER ->
         [L EXCEPT !.wr = [@ EXCEPT ![t] = @ + 1], !.wowner = Owner[t],
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
  IF L.q = <<>> THEN [L EXCEPT !.owed = FALSE]
  ELSE LET h == Head(L.q) IN
       IF HandoffMode(L, h)
         THEN IF Fits(L, want[h])
                THEN WakeIn([Enter(L, h, want[h]) EXCEPT !.owed = TRUE,
                               !.node = [@ EXCEPT ![h] = "handed"],
                               !.q = Tail(@)], h)
                ELSE [L EXCEPT !.owed = TRUE]
         ELSE IF ~Notified(L, h) /\ (release \/ Fits(L, want[h]))
                THEN WakeIn(L, h)
                ELSE L

\* The upgrade step: an upgradable holder that waits gets write once no
\* plain reader remains (it is woken). Mutant AnyReaderUpgrade: a plain
\* reader waiting to upgrade gets write once it is the only reader.
UpgradeStep(L) ==
  IF L.upgrading /\ L.uholder # 0 /\ pc[L.uholder] = "upwait" /\ NoReaders(L)
     /\ L.wowner = NoOwner
    THEN LET u == L.uholder IN
         WakeIn([L EXCEPT !.up = [@ EXCEPT ![u] = 0], !.uholder = 0,
                          !.upgrading = FALSE,
                          !.wr = [@ EXCEPT ![u] = 1], !.wowner = Owner[u],
                          !.wdepth = 1], u)
  ELSE IF Mutant = "AnyReaderUpgrade" /\ L.upgrading /\ L.wowner = NoOwner /\ L.uholder = 0
       /\ \E r \in Tasks : pc[r] = "rupwait" /\ SumOf(L.rd, Tasks) = L.rd[r]
    THEN LET r == CHOOSE x \in Tasks : pc[x] = "rupwait" /\ SumOf(L.rd, Tasks) = L.rd[x] IN
         WakeIn([L EXCEPT !.rd = [@ EXCEPT ![r] = 0],
                          !.rdepth = [@ EXCEPT ![Owner[r]] = @ - L.rd[r]],
                          !.upgrading = FALSE,
                          !.wr = [@ EXCEPT ![r] = 1], !.wowner = Owner[r],
                          !.wdepth = 1], r)
  ELSE L

\* Everything a release triggers: the upgrade step, then the queue step.
Dispatch(L) == QueueStep(UpgradeStep(L), TRUE)

\* Task t drops one plain read guard.
DropRead(L, t) ==
  [L EXCEPT !.rd = [@ EXCEPT ![t] = @ - 1], !.rdepth = [@ EXCEPT ![Owner[t]] = @ - 1]]

\* Task t drops one write guard; the last one frees write.
DropWrite(L, t) ==
  [L EXCEPT !.wr = [@ EXCEPT ![t] = @ - 1], !.wdepth = @ - 1,
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
  /\ Apply(L)
  /\ IF L.wake = {}
       THEN /\ pc' = [pc EXCEPT ![t] = next]
            /\ towake' = [d \in Tasks |-> towake[d] \ gone]
            /\ UNCHANGED ret
       ELSE /\ pc' = [pc EXCEPT ![t] = "wake"]
            /\ towake' = [d \in Tasks |-> IF d = t THEN L.wake ELSE towake[d] \ gone]
            /\ ret' = [ret EXCEPT ![t] = next]

\* Finish with no request leaving the queue.
Finish(t, L, next) == FinishDrop(t, L, next, {})

\* Task t's Owner already holds the lock in a mode that covers a read.
OwnerCoversRead(t) ==
  /\ Kind = "Reentrant"
  /\ \/ wowner = Owner[t]
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
  /\ pc[t] \in {"idle", "holding"}
  /\ w \in Asks[t]
  /\ Guards(t) < MaxDepth
  /\ w = "upread" => Kind = "Plain"
  \* A task holding only plain read never asks for write: no upgrade method.
  /\ w = "write" => (rd[t] = 0 \/ wowner = Owner[t])
  /\ LET reenter == \/ w = "read" /\ OwnerCoversRead(t)
                    \/ w = "write" /\ Kind = "Reentrant" /\ wowner = Owner[t]
     IN IF reenter
          THEN /\ Apply(Enter(Lock, t, w))
               /\ pc' = [pc EXCEPT ![t] = "holding"]
               /\ UNCHANGED <<want, towake, ret, bargedOwed, readInUpgrade>>
        ELSE IF Fits(Lock, w) /\ ~owed
          THEN /\ Apply(Enter(Lock, t, w))
               /\ pc' = [pc EXCEPT ![t] = "holding"]
               /\ bargedOwed' = (bargedOwed \/ owed)
               /\ readInUpgrade' = (readInUpgrade \/ (w = "read" /\ upgrading))
               /\ UNCHANGED <<want, towake, ret>>
        ELSE /\ q' = Append(q, t)
             /\ node' = [node EXCEPT ![t] = "waiting"]
             /\ want' = [want EXCEPT ![t] = w]
             /\ bypass' = [bypass EXCEPT ![t] = 0]
             /\ lost' = [lost EXCEPT ![t] = 0]
             /\ woken' = [woken EXCEPT ![t] = FALSE]
             /\ pc' = [pc EXCEPT ![t] = "parked"]
             /\ UNCHANGED <<rd, wr, up, rdepth, wowner, wdepth, uholder, upgrading,
                            owed, towake, ret, bargedOwed, readInUpgrade>>

\* A guard drops; everything it triggers happens with it.
Release(t) ==
  /\ pc[t] = "holding"
  /\ \/ rd[t] > 0 /\ Finish(t, Dispatch(DropRead(Lock, t)), IF Guards(t) > 1 THEN "holding" ELSE "idle")
     \/ wr[t] > 0 /\ Finish(t, Dispatch(DropWrite(Lock, t)), IF Guards(t) > 1 THEN "holding" ELSE "idle")
     \/ up[t] > 0 /\ ~upgrading /\ Finish(t, Dispatch(DropUp(Lock, t)), "idle")
  /\ UNCHANGED <<want, bargedOwed, readInUpgrade>>

\* upgrade() on the upgradable guard: with no plain reader left, write at
\* once; otherwise hold new plain readers back and wait for them to drain.
Upgrade(t) ==
  /\ pc[t] = "holding"
  /\ up[t] = 1
  /\ IF NoReaders(Lock)
       THEN /\ up' = [up EXCEPT ![t] = 0]
            /\ uholder' = 0
            /\ wr' = [wr EXCEPT ![t] = 1]
            /\ wowner' = Owner[t]
            /\ wdepth' = 1
            /\ UNCHANGED <<upgrading, pc>>
       ELSE /\ upgrading' = TRUE
            /\ pc' = [pc EXCEPT ![t] = "upwait"]
            /\ UNCHANGED <<up, uholder, wr, wowner, wdepth>>
  /\ UNCHANGED <<rd, rdepth, q, want, node, bypass, lost, woken, owed, towake, ret,
                 bargedOwed, readInUpgrade>>

\* Mutant AnyReaderUpgrade only: a plain reader asks to upgrade, holds new
\* readers back, and waits to be the only reader. (The upgradable guard
\* stays unused in that configuration.)
ReaderUpgrade(t) ==
  /\ Mutant = "AnyReaderUpgrade"
  /\ pc[t] = "holding"
  /\ rd[t] = 1 /\ wr[t] = 0 /\ up[t] = 0 /\ uholder = 0
  /\ upgrading' = TRUE
  /\ pc' = [pc EXCEPT ![t] = "rupwait"]
  /\ UNCHANGED <<rd, wr, up, rdepth, wowner, wdepth, uholder, q, want, node, bypass,
                 lost, woken, owed, towake, ret, bargedOwed, readInUpgrade>>

\* A task delivers the wakes it decided, one per step, after the handoffs
\* they announce.
Wake(t) ==
  /\ pc[t] = "wake"
  /\ IF towake[t] = {}
       THEN /\ pc' = [pc EXCEPT ![t] = ret[t]]
            /\ ret' = [ret EXCEPT ![t] = "idle"]
            /\ UNCHANGED <<woken, towake>>
       ELSE \E u \in towake[t] :
              /\ woken' = [woken EXCEPT ![u] = TRUE]
              /\ towake' = [towake EXCEPT ![t] = @ \ {u}]
              /\ UNCHANGED <<pc, ret>>
  /\ UNCHANGED <<rd, wr, up, rdepth, wowner, wdepth, uholder, upgrading, q, want,
                 node, bypass, lost, owed, bargedOwed, readInUpgrade>>

\* The executor polls a woken waiter. Handed: it holds its guard; the owed
\* bit clears. Otherwise it tries its fast path (only the head is ever
\* woken, and an owed handoff is its own): entering, it leaves the queue.
\* Either way the next head is woken if its request fits now. Losing: it
\* keeps its place, counts the loss, and registers its waker again.
Poll(t) ==
  /\ pc[t] = "parked"
  /\ woken[t]
  /\ IF node[t] = "handed"
       THEN FinishDrop(t, QueueStep([Lock EXCEPT !.node = [@ EXCEPT ![t] = "none"],
                                         !.woken = [@ EXCEPT ![t] = FALSE],
                                         !.owed = FALSE,
                                         !.bypass = [@ EXCEPT ![t] = 0],
                                         !.lost = [@ EXCEPT ![t] = 0]], FALSE), "holding", {t})
     ELSE IF Fits(Lock, want[t]) /\ ~owed
       THEN FinishDrop(t, QueueStep([Enter(Lock, t, want[t]) EXCEPT
                                         !.node = [@ EXCEPT ![t] = "none"],
                                         !.woken = [@ EXCEPT ![t] = FALSE],
                                         !.q = SelectSeq(@, LAMBDA u : u # t),
                                         !.bypass = [@ EXCEPT ![t] = 0],
                                         !.lost = [@ EXCEPT ![t] = 0]], FALSE), "holding", {t})
     ELSE /\ lost' = [lost EXCEPT ![t] = @ + 1]
          /\ bypass' = [bypass EXCEPT ![t] = @ + 1]
          /\ woken' = [woken EXCEPT ![t] = FALSE]
          /\ UNCHANGED <<rd, wr, up, rdepth, wowner, wdepth, uholder, upgrading, q,
                         node, owed, towake, ret, pc>>
  /\ UNCHANGED <<want, bargedOwed, readInUpgrade>>

\* The upgrader, woken after the last plain reader left, holds write.
UpPoll(t) ==
  /\ pc[t] \in {"upwait", "rupwait"}
  /\ woken[t]
  /\ wr[t] > 0
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  /\ pc' = [pc EXCEPT ![t] = "holding"]
  /\ UNCHANGED <<rd, wr, up, rdepth, wowner, wdepth, uholder, upgrading, q, want, node,
                 bypass, lost, owed, towake, ret, bargedOwed, readInUpgrade>>

\* The pending future is dropped. A waiting node leaves the queue, and the
\* next head is woken if its request fits (a wake the dropped head had is
\* passed on; an owed handoff passes to it, or clears). A handed one drops
\* the guard it was handed, through the same steps as a release.
Cancel(t) ==
  /\ pc[t] = "parked"
  /\ LET L0 == [Lock EXCEPT !.node = [@ EXCEPT ![t] = "none"],
                            !.woken = [@ EXCEPT ![t] = FALSE],
                            !.bypass = [@ EXCEPT ![t] = 0],
                            !.lost = [@ EXCEPT ![t] = 0]]
     IN IF node[t] = "waiting"
          THEN FinishDrop(t, QueueStep([L0 EXCEPT !.q = SelectSeq(@, LAMBDA u : u # t)], FALSE),
                          "idle", {t})
        ELSE IF want[t] = "read" THEN FinishDrop(t, Dispatch(DropRead(L0, t)), "idle", {t})
        ELSE IF want[t] = "upread" THEN FinishDrop(t, Dispatch(DropUp(L0, t)), "idle", {t})
        ELSE FinishDrop(t, Dispatch(DropWrite(L0, t)), "idle", {t})
  /\ UNCHANGED <<want, bargedOwed, readInUpgrade>>

----------------------------------------------------------------------------
\* The specification.

\* The start: nobody holds, nobody waits.
Init ==
  /\ rd = [t \in Tasks |-> 0]
  /\ wr = [t \in Tasks |-> 0]
  /\ up = [t \in Tasks |-> 0]
  /\ rdepth = [o \in Owners |-> 0]
  /\ wowner = NoOwner
  /\ wdepth = 0
  /\ uholder = 0
  /\ upgrading = FALSE
  /\ q = <<>>
  /\ want = [t \in Tasks |-> "read"]
  /\ node = [t \in Tasks |-> "none"]
  /\ bypass = [t \in Tasks |-> 0]
  /\ lost = [t \in Tasks |-> 0]
  /\ woken = [t \in Tasks |-> FALSE]
  /\ owed = FALSE
  /\ towake = [t \in Tasks |-> {}]
  /\ ret = [t \in Tasks |-> "idle"]
  /\ pc = [t \in Tasks |-> "idle"]
  /\ bargedOwed = FALSE
  /\ readInUpgrade = FALSE

\* Every step the system can take.
Next ==
  \E t \in Tasks :
    \/ \E w \in {"read", "write", "upread"} : Request(t, w)
    \/ Release(t) \/ Upgrade(t) \/ ReaderUpgrade(t) \/ Wake(t) \/ Poll(t) \/ UpPoll(t)
    \/ Cancel(t)

\* Fairness: wakes are delivered, woken futures are polled, and a holder
\* eventually drops a guard. Requests, upgrades and cancels are the
\* caller's choices.
Fairness ==
  \A t \in Tasks :
    /\ WF_vars(Wake(t) \/ Poll(t) \/ UpPoll(t))
    /\ WF_vars(Release(t))

\* Every behaviour: start in Init, take Next steps or stutter, fairly.
Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ rd \in [Tasks -> 0..MaxDepth]
  /\ wr \in [Tasks -> 0..MaxDepth]
  /\ up \in [Tasks -> 0..1]
  /\ wowner \in Owners \cup {NoOwner}
  /\ uholder \in Tasks \cup {0}
  /\ node \in [Tasks -> {"none", "waiting", "handed"}]
  /\ pc \in [Tasks -> {"idle", "holding", "parked", "upwait", "rupwait", "wake"}]
  /\ Range(q) \subseteq Tasks

\* MUTUAL EXCLUSION. While an owner holds write, no other owner holds read
\* and no upgradable guard is out; every guard is counted on the lock.
\* Lean (exclusive side): mutual_exclusion.
MutualExclusion ==
  /\ wowner # NoOwner => uholder = 0 /\ \A o \in Owners \ {wowner} : rdepth[o] = 0
  /\ \A t \in Tasks : wr[t] > 0 => Owner[t] = wowner
  /\ \A t \in Tasks : rd[t] > 0 => rdepth[Owner[t]] > 0

\* AT MOST ONE UPGRADABLE GUARD, and the lock names its holder.
UpgradableExclusive ==
  /\ \A t, u \in Tasks : up[t] = 1 /\ up[u] = 1 => t = u
  /\ \A t \in Tasks : up[t] = 1 <=> uholder = t

\* REENTRANCY DEPTH. The lock's depths are exactly the guards out, and
\* write is held exactly when its depth is not 0.
ReentrancyDepth ==
  /\ wdepth = SumOf(wr, Tasks)
  /\ \A o \in Owners : rdepth[o] = SumOf(rd, {t \in Tasks : Owner[t] = o})
  /\ (wowner = NoOwner <=> wdepth = 0)

\* BOUNDED BYPASS. A waiter, reader or writer, loses the race at most Bound
\* times; then a release hands it the lock. Neither side starves.
\* Lean: bounded_bypass.
BoundedBypass == \A t \in Tasks : lost[t] <= Bound

\* HANDOFF EXCLUSIVE. Nobody enters through the fast path while a handoff
\* is owed. Lean: owed_blocks_barging.
HandoffExclusive == ~bargedOwed

\* UPGRADE HOLDS READERS BACK. No plain reader enters while an upgrade
\* waits.
UpgradeHoldsBack == ~readInUpgrade

\* NO UPGRADE DEADLOCK. Every reader an upgrader waits for is free to drop
\* its guard: it is running (holding, or delivering wakes), or it was handed
\* its guard and only awaits its own poll, which needs nothing from the
\* lock. It is never itself waiting on the lock. With one upgrader and no
\* upgrade from plain read, this holds, so every upgrade completes.
NoUpgradeDeadlock ==
  \A t \in Tasks :
    pc[t] \in {"upwait", "rupwait"} =>
      \A u \in Tasks \ {t} :
        rd[u] > 0 => (pc[u] \in {"holding", "wake"} \/ (pc[u] = "parked" /\ node[u] = "handed"))

\* NO SELF-DEADLOCK. A queued task holds no guard of the lock.
NoSelfDeadlock == \A t \in Tasks : node[t] = "waiting" => Guards(t) = 0

\* A queued head left asleep though it could proceed: its request fits,
\* nobody has woken it or decided to, and no handed waiter is still to take
\* an owed handoff (that waiter's take clears the owed bit and wakes the
\* head); or an upgrade left waiting with every plain reader gone.
Stranded ==
  \/ /\ q # <<>>
     /\ LET h == Head(q) IN Fits(Lock, want[h]) /\ ~Notified(Lock, h)
     /\ ~(owed /\ \E t \in Tasks : node[t] = "handed")
  \/ /\ upgrading /\ uholder # 0 /\ NoReaders(Lock) /\ wowner = NoOwner

\* NO LOST WAKEUP. A parked future handed the lock has been woken or is
\* about to be, and no head or upgrader is stranded. Lean: no_stranded_head.
NoLostWakeup ==
  /\ \A t \in Tasks :
       pc[t] = "parked" /\ node[t] = "handed" => woken[t] \/ \E d \in Tasks : t \in towake[d]
  /\ ~Stranded

\* CANCELLATION PASSES ON. An idle task holds no guard.
CancelPassesOn == \A t \in Tasks : pc[t] = "idle" => Guards(t) = 0

----------------------------------------------------------------------------
\* Liveness. Checked for the tasks in Watched: tasks with the same Owner
\* role are interchangeable, so one per role stands for all.

\* Every parked waiter stops waiting: it is served, unless it cancels.
EveryWaiterServed == \A t \in Watched : (pc[t] = "parked") ~> (pc[t] # "parked")

\* Every upgrade completes: the upgrader comes to hold write.
UpgradeCompletes == \A t \in Watched : (pc[t] = "upwait") ~> (pc[t] = "holding")

\* Owner o holds the lock in some mode.
OwnerHolds(o) == rdepth[o] > 0 \/ wowner = o

\* Reentrant: no owner keeps the lock forever.
OwnersLetGo == \A o \in Owners : []<>(~OwnerHolds(o))

\* Reentrant: if no owner holds the lock forever, every waiter is served.
ReentrantServed == OwnersLetGo => EveryWaiterServed

====
