---- MODULE Sync ----
\* regolith::sync's lock-like primitives after D49: Mutex, Semaphore (owned
\* guards included) and ReentrantMutex, with barging and bounded fairness.
\* (Notify keeps FIFO handoff: SyncNotify.tla. RwLock: SyncRwLock.tla.)
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/Sync.lean (the Mutex,
\* one permit, every interleaving of the abstract steps):
\*   step_inv, reachable_inv      the protocol's invariant holds in every
\*                                reachable state
\*   mutual_exclusion             at most one holder, and none while free
\*                                (MutualExclusion here)
\*   bounded_bypass, lose_below_bound, bypass_counts_losses
\*                                a waiter's count of lost races never
\*                                passes Bound, a loss happens only below
\*                                it, and only a loss moves the count
\*                                (BoundedBypass here)
\*   release_hands_off_at_bound   once a waiter has lost Bound times, the
\*                                next release hands it the lock
\*   owed_exclusive,              while a handoff is owed, its waiter holds
\*   owed_blocks_barging          the lock and nobody else acquires
\*                                (HandoffExclusive here)
\*   no_stranded_head,            a free lock with waiters has woken its
\*   handed_woken                 head; a handed waiter is woken
\*                                (NoLostWakeup here)
\*   unbounded_barging_breaks_bound, release_without_wake_strands
\*                                the RED cases, as counterexamples
\*
\* THE DESIGN (D49, replacing strict FIFO handoff, which measured 15 to 350
\* times slower than std::sync::Mutex under cross-thread contention: it
\* hands the lock to a suspended task, and every acquirer waits for that
\* task to be scheduled).
\*   - The state word: permits free (`avail`; a Mutex's locked bit), a
\*     waiters-present count and a handoff-owed bit.
\*   - Acquire, fast path: one CAS taking free permits. It succeeds whenever
\*     they are free and no handoff is owed, even if waiters are queued:
\*     barging. try_lock is the same CAS. A contended acquire spins a
\*     bounded number of times on that CAS, then registers a waiter node at
\*     the tail and returns Pending.
\*   - Release with no waiters: one RMW. With waiters: if the head's bypass
\*     count is below Bound, the permits become free and the head is woken
\*     to compete again; if it has reached Bound, the permits pass straight
\*     to the head (the lock stays held), the owed bit blocks barging until
\*     the head takes them, and the head is woken.
\*   - A woken waiter, polled, tries the CAS. If it loses it keeps its place
\*     at the head, its bypass count goes up by one, and it registers its
\*     waker again, re-checking the state after registering.
\*   - Cancellation removes the waiter; a handoff it was owed passes to the
\*     next waiter, or the permits are freed if none waits; a wake it was
\*     given and did not use passes to the next head.
\*
\* THE PROTOCOL MODELLED, one atomic step per word-sized CAS or queue
\* operation, as before D49:
\*   - a release that finds waiters adds its permits to `pending` (in the
\*     state word, not takeable) and drains. The drain token: only its
\*     holder looks at and pops the queue head, decides free-and-wake or
\*     handoff, and hands permits over. Nobody waits for the token: a task
\*     that finds it taken leaves, and the holder re-checks before letting
\*     go. So the handoff decision is made before the permits ever become
\*     free, which "the lock stays held" requires;
\*   - a node is CAS'd once from "waiting" to "handed" (by the drainer),
\*     "done" (its waiter won the CAS itself) or "cancelled" (its future
\*     was dropped). Done and cancelled nodes stay queued until the drainer
\*     pops them;
\*   - a node's bypass count and its woken bit share one word: the drainer
\*     wakes a head only if the bit is clear, and a losing poll increments
\*     the count and clears the bit in one RMW.
\*
\* DESIGN CHOICES WHERE THE NOTE IS SILENT, recorded in the report.
\*   - "Bypassed" means: polled after a wake, tried the CAS, lost. Between a
\*     wake and the poll it causes, the lock may change hands any number of
\*     times; the waiter could not have taken it then (its task was not
\*     running), and those acquisitions are not counted. Nobody starves:
\*     after Bound losses the next release hands off, so a waiter is served
\*     once the waiters ahead of it are (EveryWaiterServed checks it).
\*   - Semaphore: a request for several permits at the head in handoff mode
\*     reserves: the owed bit blocks barging while released permits gather
\*     until the head's request is met. A drainer in handoff mode keeps
\*     handing spare permits to the next heads.
\*   - A waiter that acquires by its own CAS while queued, or takes a
\*     handoff, drains when others wait: it pops its own stale node and
\*     wakes the next head if permits are still free (a Semaphore's spare
\*     permits; for a Mutex this only pops).
\*   - A poll counts a loss only if its own node's woken bit is set (set by
\*     the drain that woke it). A spurious poll, such as one caused by a late
\*     wake meant for a node since served or dropped, re-registers without
\*     counting. Here polls fire only on the node's bit, so a spurious poll
\*     is a no-op; SyncRwLock.tla shows what counting it would break.
\*   - A woken waiter that is cancelled passes its wake on to the next head
\*     (the drain after a cancel wakes it). Without this a free lock and a
\*     sleeping head are left behind.
\*   - A release wakes the head whatever its request, as the note says,
\*     and a poll that cannot take its request counts a loss. Waking a
\*     Semaphore head only when the free permits meet its request starves
\*     it: one-permit bargers keep it short, it never loses, and Bound is
\*     never reached. TLC found that lasso in MC_Sync_Green_Semaphore.
\*
\* UNCONTENDED COST. The fast path is one step on the state word (Acquire's
\* take branch), and a release with no waiters is one step on it (Release's
\* free branch): one atomic RMW each. That is structural in the actions,
\* not an invariant.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - Spinning: a failed CAS try changes nothing, so a spin of up to SPIN
\*     tries is one Acquire step taken at the moment of its last try: it
\*     takes the lock then, or registers then. On single-threaded wasm the
\*     spin is skipped.
\*   - A task has one request at a time and may not register again while its
\*     previous node is still queued; two nodes of one task act as two tasks.
\*   - A cancel is one step; a drainer's pop and its `waiters` decrement are
\*     one step; letting the token go and the re-check are one step.
\*   - Memory ordering is loom's (plan 7.1).
\*
\* CONFIGURATIONS.
\*   MC_Sync_Green_Mutex          Mutex, three tasks, Bound 2: every
\*                                invariant, and every waiter is served.
\*   MC_Sync_Green_Semaphore      two permits, task 1 asks for both, owned
\*                                guards moving between tasks.
\*   MC_Sync_Green_Reentrant      ReentrantMutex, tasks 1 and 2 of one owner,
\*                                nesting two guards: every safety invariant.
\*   MC_Sync_Green_ReentrantLive  the same with one guard per task: if no
\*                                owner holds forever, every waiter is served.
\*   MC_Sync_Red_UnboundedBarging the drain never hands off: BoundedBypass.
\*   MC_Sync_Red_ReleaseNoWake    a release frees the lock and wakes nobody:
\*                                NoLostWakeup.
\*   MC_Sync_Red_LoseQueuePosition  a waiter that loses goes to the tail with
\*                                a fresh count: BoundedBypass.
\*   MC_Sync_Red_CancelNoPassOn   a waiter dropped after a handoff keeps the
\*                                lock: CancelPassesOn.
\*   MC_Sync_Red_NoRecheck        park right after the push: NoLostWakeup.
\*   MC_Sync_Red_IgnoreOwed       the fast path ignores the owed bit:
\*                                HandoffExclusive.
\*   MC_Sync_Red_NoDepth          a reentrant guard drop frees the lock at
\*                                any depth: ReentrancyDepth.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Tasks,     \* the tasks using the primitive: positive naturals
  Kind,      \* "Semaphore" (a Mutex is one permit) or "Reentrant"
  Permits,   \* the permits; a Mutex and a ReentrantMutex have 1
  Need,      \* [Tasks -> 1..Permits]: how many permits task t asks for
  Owner,     \* [Tasks -> positive naturals]: task t's Owner token (Reentrant)
  MaxDepth,  \* the most nested guards one task holds (Reentrant)
  Owned,     \* TRUE when guards may move between tasks (Semaphore)
  Bound,     \* BOUND: the losses after which a release hands off
  Watched,   \* the tasks whose liveness is checked: one per role
  Mutant     \* "none" for the design, or the name of one defect

\* The value "no task", for the drain token and a drainer's target.
NoTask == 0
\* The value "no owner holds the lock".
NoOwner == 0
\* Every Owner token some task locks with.
Owners == {Owner[t] : t \in Tasks}

ASSUME Kind \in {"Semaphore", "Reentrant"}
ASSUME Permits \in Nat \ {0} /\ MaxDepth \in Nat \ {0} /\ Bound \in Nat \ {0}
ASSUME Owned \in BOOLEAN /\ Watched \subseteq Tasks
ASSUME \A t \in Tasks : Need[t] \in 1..Permits
ASSUME Tasks \subseteq Nat \ {0} /\ Owners \subseteq Nat \ {0}
ASSUME Kind = "Reentrant" => Permits = 1
ASSUME Mutant \in {"none", "UnboundedBarging", "ReleaseNoWake", "LoseQueuePosition",
                   "CancelNoPassOn", "NoRecheck", "IgnoreOwed", "NoDepth"}

\* Configuration helpers, named in the MC_Sync_*.cfg files.
\* Every task asks for one permit.
NeedOne == [t \in Tasks |-> 1]
\* Task 1 asks for every permit, the others for one.
NeedFirstAll == [t \in Tasks |-> IF t = 1 THEN Permits ELSE 1]
\* Every task is its own Owner.
OwnerEach == [t \in Tasks |-> t]
\* Tasks 1 and 2 share Owner 1 (two tasks pinned to one thread, say); task 3
\* is Owner 2.
OwnerPair == [t \in Tasks |-> IF t = 3 THEN 2 ELSE 1]

VARIABLES
  avail,      \* free permits (a ReentrantMutex: 1 when unlocked)
  pending,    \* permits a release returned while waiters were present, not
              \* yet handed out or freed by a drain; nobody can take them
  owed,       \* the handoff-owed bit: barging is shut
  waiters,    \* registered waiters not yet popped (the waiters-present bit
              \* is waiters > 0)
  fifo,       \* the waiter queue: tasks, oldest first (each task's one node)
  node,       \* [Tasks -> state of the task's node]
  woken,      \* [Tasks -> BOOLEAN]: the node's woken bit, set by a wake and
              \* cleared when the waiter registers its waker again
  bypass,     \* [Tasks -> Nat]: the node's bypass count
  lost,       \* ghost [Tasks -> Nat]: races lost during the current acquire
  held,       \* [Tasks -> Nat]: permits held (Reentrant: guards held)
  owner,      \* Reentrant: the Owner holding the lock, or NoOwner
  depth,      \* Reentrant: guards out on the lock
  token,      \* the drain token: the task holding it, or NoTask
  hand,       \* [Tasks -> Nat]: permits a drainer debited for the head
  target,     \* [Tasks -> Tasks \cup {NoTask}]: the head a drainer serves
  ret,        \* [Tasks -> pc]: where a task resumes once its drain ends
  pc,         \* [Tasks -> pc]: where each task is in its operation
  bargedOwed  \* ghost: a fast-path take succeeded while a handoff was owed

\* Every variable, so a step that changes none of them is a stutter.
vars == <<avail, pending, owed, waiters, fifo, node, woken, bypass, lost, held,
          owner, depth, token, hand, target, ret, pc, bargedOwed>>

\* The steps of the drain, where a task may hold the token.
DrainPCs == {"dtake", "dloop", "dgrant", "dwake", "dfree"}

\* The places a task can be: "idle", "holding", "owned" (holds a guard moved
\* to it), "push" (registered, about to push its node), "recheck" (about to
\* re-check the state after registering its waker), "parked" (its future
\* returned Pending), or a drain step.
PCs == {"idle", "holding", "owned", "push", "recheck", "parked"} \cup DrainPCs

\* The states of a node. "done" and "cancelled" are stale: the drainer pops
\* them. "none": no node, or one nobody looks at any more.
NodeStates == {"none", "waiting", "handed", "done", "cancelled"}

----------------------------------------------------------------------------
\* Helpers.

\* The sum of f[x] over a finite set S.
RECURSIVE SumOf(_, _)
SumOf(f, S) == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

\* Sequence s without element x.
Remove(s, x) == SelectSeq(s, LAMBDA y : y # x)

\* Task t has a node in the queue.
InFifo(t) == \E i \in 1..Len(fifo) : fifo[i] = t

\* A node the drainer pops without serving.
Stale(t) == node[t] \in {"done", "cancelled"}

\* The fast-path CAS for task t succeeds: enough permits are free and no
\* handoff is owed. Waiters do not matter: barging. (Mutant IgnoreOwed: the
\* owed bit does not matter either.)
CanTake(t) == avail >= Need[t] /\ (~owed \/ Mutant = "IgnoreOwed")

\* The drain serves the head by handoff: one is owed already, or the head
\* has lost Bound times. (Mutant UnboundedBarging: only if owed already.)
HandoffMode(h) == owed \/ (bypass[h] >= Bound /\ Mutant # "UnboundedBarging")

\* The drain may wake a head it is not handing to. (Mutant ReleaseNoWake:
\* it never does.)
Wakes == Mutant # "ReleaseNoWake"

\* The queue head is work for a drainer: a stale node to pop; a head to hand
\* permits to; a head to wake because permits are free and its bit is clear.
HeadWork ==
  /\ fifo # <<>>
  /\ LET h == Head(fifo) IN
       \/ Stale(h)
       \/ avail >= Need[h] /\ HandoffMode(h)
       \/ avail >= Need[h] /\ ~woken[h] /\ Wakes

\* Work for a drainer: permits to distribute, an owed bit with nobody left
\* to owe it to, or work at the head.
Work == pending > 0 \/ (owed /\ fifo = <<>>) \/ HeadWork

\* Reentrant: t's Owner holds the lock, so t enters again at once.
CanReenter(t) == Kind = "Reentrant" /\ owner = Owner[t] /\ held[t] < MaxDepth

\* Task t goes on to drain (try the token), and resumes at `r` afterwards.
DrainThen(t, r) ==
  /\ pc' = [pc EXCEPT ![t] = "dtake"]
  /\ ret' = [ret EXCEPT ![t] = r]

\* Task t's drain is over: it resumes where it was going.
Resume(t) ==
  /\ pc' = [pc EXCEPT ![t] = ret[t]]
  /\ ret' = [ret EXCEPT ![t] = "idle"]

\* Task t, holding now, drains if others wait (to pop its stale node and
\* wake the next head for spare permits), else just holds.
HoldThenDrain(t) ==
  IF waiters > 0 THEN DrainThen(t, "holding")
  ELSE pc' = [pc EXCEPT ![t] = "holding"] /\ UNCHANGED ret

\* The fast-path take: the permits leave `avail` and task t holds them.
\* Records a take made while a handoff was owed (only IgnoreOwed can).
Take(t) ==
  /\ avail' = avail - Need[t]
  /\ held' = [held EXCEPT ![t] = Need[t]]
  /\ owner' = IF Kind = "Reentrant" THEN Owner[t] ELSE owner
  /\ depth' = IF Kind = "Reentrant" THEN 1 ELSE depth
  /\ bargedOwed' = (bargedOwed \/ owed)

\* Task t gives up n of its permits (Reentrant: n guards). It returns `rel`
\* permits to the state word: a Semaphore returns n; a ReentrantMutex
\* returns its one permit when the depth reaches 0 (mutant NoDepth: at
\* once). With no waiters they become free (one RMW); with waiters they go
\* to `pending` for the drain. `freed` tells whether anything was returned.
GiveUp(t, n) ==
  LET rel == IF Kind = "Semaphore" THEN n
             ELSE IF depth - n = 0 \/ Mutant = "NoDepth" THEN 1 ELSE 0
  IN /\ held' = [held EXCEPT ![t] = @ - n]
     /\ depth' = IF Kind = "Reentrant" THEN depth - n ELSE depth
     /\ owner' = IF Kind = "Reentrant" /\ rel = 1 THEN NoOwner ELSE owner
     /\ IF waiters = 0
          THEN avail' = avail + rel /\ UNCHANGED pending
          ELSE pending' = pending + rel /\ UNCHANGED avail

\* What GiveUp(t, n) returns to the state word (see GiveUp).
Returned(t, n) ==
  IF Kind = "Semaphore" THEN n
  ELSE IF depth - n = 0 \/ Mutant = "NoDepth" THEN 1 ELSE 0

----------------------------------------------------------------------------
\* Acquiring.

\* lock() / acquire(n) / lock(owner), first poll (try_lock is its first
\* branch): the fast-path CAS, barging past any waiters; if it fails,
\* register as a waiter (the waiters-present count goes up).
Acquire(t) ==
  /\ pc[t] = "idle"
  /\ ~InFifo(t)
  /\ ~CanReenter(t)
  /\ IF CanTake(t)
       THEN /\ Take(t)
            /\ pc' = [pc EXCEPT ![t] = "holding"]
            /\ UNCHANGED waiters
       ELSE /\ waiters' = waiters + 1
            /\ pc' = [pc EXCEPT ![t] = "push"]
            /\ UNCHANGED <<avail, held, owner, depth, bargedOwed>>
  /\ UNCHANGED <<pending, owed, fifo, node, woken, bypass, lost, token, hand, target, ret>>

\* Reentrant: a task whose Owner holds the lock enters again at once, idle
\* or holding. Nothing barges: the owner is already inside.
Reenter(t) ==
  /\ pc[t] \in {"idle", "holding"}
  /\ CanReenter(t)
  /\ held' = [held EXCEPT ![t] = @ + 1]
  /\ depth' = depth + 1
  /\ pc' = [pc EXCEPT ![t] = "holding"]
  /\ UNCHANGED <<avail, pending, owed, waiters, fifo, node, woken, bypass, lost,
                 owner, token, hand, target, ret, bargedOwed>>

\* The registered waiter pushes its node (bypass count 0, woken bit clear,
\* Waker inside) at the tail, then re-checks. Mutant NoRecheck: it parks.
Push(t) ==
  /\ pc[t] = "push"
  /\ fifo' = Append(fifo, t)
  /\ node' = [node EXCEPT ![t] = "waiting"]
  /\ bypass' = [bypass EXCEPT ![t] = 0]
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  /\ pc' = [pc EXCEPT ![t] = IF Mutant = "NoRecheck" THEN "parked" ELSE "recheck"]
  /\ UNCHANGED <<avail, pending, owed, waiters, lost, held, owner, depth, token,
                 hand, target, ret, bargedOwed>>

\* Task t takes a handoff: the permits are already its; the owed bit clears.
TakeHanded(t) ==
  /\ node' = [node EXCEPT ![t] = "none"]
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  /\ owed' = FALSE
  /\ lost' = [lost EXCEPT ![t] = 0]
  /\ bypass' = [bypass EXCEPT ![t] = 0]
  /\ HoldThenDrain(t)
  /\ UNCHANGED <<avail, held, owner, depth, bargedOwed>>

\* Task t wins the CAS while its node is queued: it holds, its node is
\* stale, and it drains (it popping its node and maybe waking the next).
WinQueued(t) ==
  /\ Take(t)
  /\ node' = [node EXCEPT ![t] = "done"]
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  /\ lost' = [lost EXCEPT ![t] = 0]
  /\ bypass' = [bypass EXCEPT ![t] = 0]
  /\ DrainThen(t, "holding")
  /\ UNCHANGED owed

\* The re-check after registering the waker: take a handoff that arrived,
\* or win the CAS, or park.
Recheck(t) ==
  /\ pc[t] = "recheck"
  /\ CASE node[t] = "handed" -> TakeHanded(t)
       [] CanTake(t) -> WinQueued(t)
       [] OTHER -> /\ pc' = [pc EXCEPT ![t] = "parked"]
                   /\ UNCHANGED <<node, woken, owed, lost, bypass, avail, held, owner,
                                  depth, bargedOwed, ret>>
  /\ UNCHANGED <<pending, waiters, fifo, token, hand, target>>

\* The executor polls a woken future. Handed: take it. Otherwise try the
\* CAS. Losing: keep the place at the head, count the loss, register the
\* waker again (clearing the woken bit) and re-check. Mutant
\* LoseQueuePosition: the loser goes to the tail with a fresh count.
Poll(t) ==
  /\ pc[t] = "parked"
  /\ woken[t]
  /\ CASE node[t] = "handed" ->
            /\ TakeHanded(t)
            /\ UNCHANGED <<pending, waiters, fifo, token, hand, target>>
       [] CanTake(t) ->
            /\ WinQueued(t)
            /\ UNCHANGED <<pending, waiters, fifo, token, hand, target>>
       [] OTHER ->
            /\ lost' = [lost EXCEPT ![t] = @ + 1]
            /\ woken' = [woken EXCEPT ![t] = FALSE]
            /\ IF Mutant = "LoseQueuePosition"
                 THEN /\ fifo' = Append(Remove(fifo, t), t)
                      /\ bypass' = [bypass EXCEPT ![t] = 0]
                 ELSE /\ bypass' = [bypass EXCEPT ![t] = @ + 1]
                      /\ UNCHANGED fifo
            /\ pc' = [pc EXCEPT ![t] = "recheck"]
            /\ UNCHANGED <<avail, pending, owed, waiters, node, held, owner, depth,
                           token, hand, target, ret, bargedOwed>>

\* The pending future is dropped. A waiting node is CAS'd to "cancelled"
\* and the task drains: that pops it if it is the head, passes an unused
\* wake on to the next head, and passes an owed handoff on. A handed node:
\* the permits go back to `pending` (the owed bit stays set), and the drain
\* hands them to the next waiter, or frees them if none waits. Mutant
\* CancelNoPassOn: a handed waiter keeps the lock.
Cancel(t) ==
  /\ pc[t] = "parked"
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  /\ lost' = [lost EXCEPT ![t] = 0]
  /\ bypass' = [bypass EXCEPT ![t] = 0]
  /\ IF node[t] = "waiting"
       THEN /\ node' = [node EXCEPT ![t] = "cancelled"]
            /\ DrainThen(t, "idle")
            /\ UNCHANGED <<held, owner, depth, pending, avail>>
       ELSE /\ node' = [node EXCEPT ![t] = "none"]
            /\ IF Mutant = "CancelNoPassOn"
                 THEN /\ pc' = [pc EXCEPT ![t] = "idle"]
                      /\ UNCHANGED <<held, owner, depth, pending, avail, ret>>
                 ELSE /\ held' = [held EXCEPT ![t] = 0]
                      /\ depth' = IF Kind = "Reentrant" THEN depth - held[t] ELSE depth
                      /\ owner' = IF Kind = "Reentrant" /\ depth = held[t] THEN NoOwner ELSE owner
                      /\ pending' = pending +
                           (IF Kind = "Semaphore" THEN held[t]
                            ELSE IF depth = held[t] THEN 1 ELSE 0)
                      /\ DrainThen(t, "idle")
                      /\ UNCHANGED avail
  /\ UNCHANGED <<owed, waiters, fifo, token, hand, target, bargedOwed>>

----------------------------------------------------------------------------
\* Releasing and moving owned guards.

\* A guard is dropped. A Semaphore gives back all the task's permits; a
\* ReentrantMutex one guard. Returned permits with no waiters are free at
\* once (one RMW); with waiters they are pending and the task drains.
Release(t) ==
  /\ pc[t] \in {"holding", "owned"}
  /\ LET n    == IF Kind = "Reentrant" THEN 1 ELSE held[t]
         rest == held[t] - n
         next == IF rest > 0 THEN "holding" ELSE "idle"
     IN /\ GiveUp(t, n)
        /\ IF Returned(t, n) > 0 /\ waiters > 0
             THEN DrainThen(t, next)
             ELSE pc' = [pc EXCEPT ![t] = next] /\ UNCHANGED ret
  /\ UNCHANGED <<owed, waiters, fifo, node, woken, bypass, lost, token, hand, target,
                 bargedOwed>>

\* An owned guard (`lock_owned`, `acquire_owned`) moves from task t to an
\* idle task u, which only drops it.
Give(t, u) ==
  /\ Kind = "Semaphore" /\ Owned
  /\ t # u
  /\ pc[t] = "holding"
  /\ pc[u] = "idle"
  /\ ~InFifo(u)
  /\ held' = [held EXCEPT ![t] = 0, ![u] = held[t]]
  /\ pc' = [pc EXCEPT ![t] = "idle", ![u] = "owned"]
  /\ UNCHANGED <<avail, pending, owed, waiters, fifo, node, woken, bypass, lost,
                 owner, depth, token, hand, target, ret, bargedOwed>>

----------------------------------------------------------------------------
\* The drain: the only code that pops the queue head and hands permits out.

\* Take the drain token if it is free; if another task holds it, leave: the
\* holder re-checks for work before it lets go.
DTake(t) ==
  /\ pc[t] = "dtake"
  /\ IF token = NoTask
       THEN /\ token' = t
            /\ pc' = [pc EXCEPT ![t] = "dloop"]
            /\ UNCHANGED ret
       ELSE /\ Resume(t)
            /\ UNCHANGED token
  /\ UNCHANGED <<avail, pending, owed, waiters, fifo, node, woken, bypass, lost,
                 held, owner, depth, hand, target, bargedOwed>>

\* Holding the token, serve the head.
\*   - A stale head is popped.
\*   - No waiter left: pending permits become free, and the owed bit clears.
\*   - Handoff mode (owed already, or the head lost Bound times): set the
\*     owed bit, gather pending permits, and if the head's request is met,
\*     debit it into `hand` for the handoff. Nothing ever becomes free.
\*   - Otherwise: pending permits become free, and the head is woken if its
\*     woken bit is clear and a release just returned permits or the free
\*     ones meet its request.
DLoop(t) ==
  /\ pc[t] = "dloop"
  /\ IF fifo # <<>> /\ Stale(Head(fifo))
       THEN /\ fifo' = Tail(fifo)
            /\ waiters' = waiters - 1
            /\ node' = [node EXCEPT ![Head(fifo)] = "none"]
            /\ UNCHANGED <<avail, pending, owed, hand, target, pc>>
       ELSE IF fifo = <<>>
       THEN /\ avail' = avail + pending
            /\ pending' = 0
            /\ owed' = FALSE
            /\ pc' = [pc EXCEPT ![t] = "dfree"]
            /\ UNCHANGED <<waiters, fifo, node, hand, target>>
       ELSE LET h == Head(fifo)
                a == avail + pending
            IN IF HandoffMode(h)
               THEN /\ owed' = TRUE
                    /\ pending' = 0
                    /\ IF a >= Need[h]
                         THEN /\ avail' = a - Need[h]
                              /\ hand' = [hand EXCEPT ![t] = Need[h]]
                              /\ target' = [target EXCEPT ![t] = h]
                              /\ pc' = [pc EXCEPT ![t] = "dgrant"]
                         ELSE /\ avail' = a
                              /\ pc' = [pc EXCEPT ![t] = "dfree"]
                              /\ UNCHANGED <<hand, target>>
                    /\ UNCHANGED <<waiters, fifo, node>>
               ELSE /\ avail' = a
                    /\ pending' = 0
                    \* A release wakes the head even if the free permits
                    \* fall short of its request: it competes, and a loss
                    \* counts towards Bound. Waking it only when they
                    \* suffice starves a large request that one-permit
                    \* bargers keep short (TLC found that lasso).
                    /\ IF (pending > 0 \/ a >= Need[h]) /\ ~woken[h] /\ Wakes
                         THEN /\ target' = [target EXCEPT ![t] = h]
                              /\ pc' = [pc EXCEPT ![t] = "dwake"]
                         ELSE /\ pc' = [pc EXCEPT ![t] = "dfree"]
                              /\ UNCHANGED target
                    /\ UNCHANGED <<owed, waiters, fifo, node, hand>>
  /\ UNCHANGED <<woken, bypass, lost, held, owner, depth, token, ret, bargedOwed>>

\* The handoff: CAS the head's node from "waiting" to "handed". On success
\* the debited permits are its (Reentrant: the lock is its Owner's, depth
\* 1) and its node is popped; then it is woken. If its waiter won the CAS
\* on its own or was cancelled first, the permits go back to the drain.
DGrant(t) ==
  /\ pc[t] = "dgrant"
  /\ LET h == target[t] IN
     IF node[h] = "waiting"
       THEN /\ node' = [node EXCEPT ![h] = "handed"]
            /\ held' = [held EXCEPT ![h] = hand[t]]
            /\ owner' = IF Kind = "Reentrant" THEN Owner[h] ELSE owner
            /\ depth' = IF Kind = "Reentrant" THEN 1 ELSE depth
            /\ hand' = [hand EXCEPT ![t] = 0]
            /\ fifo' = Remove(fifo, h)
            /\ waiters' = waiters - 1
            /\ pc' = [pc EXCEPT ![t] = "dwake"]
            /\ UNCHANGED <<pending, target>>
       ELSE /\ pending' = pending + hand[t]
            /\ hand' = [hand EXCEPT ![t] = 0]
            /\ target' = [target EXCEPT ![t] = NoTask]
            /\ pc' = [pc EXCEPT ![t] = "dloop"]
            /\ UNCHANGED <<node, held, owner, depth, fifo, waiters>>
  /\ UNCHANGED <<avail, owed, woken, bypass, lost, token, ret, bargedOwed>>

\* Waker::wake for the head: its woken bit is set.
DWake(t) ==
  /\ pc[t] = "dwake"
  /\ woken' = [woken EXCEPT ![target[t]] = TRUE]
  /\ target' = [target EXCEPT ![t] = NoTask]
  /\ pc' = [pc EXCEPT ![t] = "dloop"]
  /\ UNCHANGED <<avail, pending, owed, waiters, fifo, node, bypass, lost, held,
                 owner, depth, token, hand, ret, bargedOwed>>

\* Let the token go and look again: work left by a task that found the
\* token taken is picked up here.
DFree(t) ==
  /\ pc[t] = "dfree"
  /\ token' = NoTask
  /\ IF Work
       THEN pc' = [pc EXCEPT ![t] = "dtake"] /\ UNCHANGED ret
       ELSE Resume(t)
  /\ UNCHANGED <<avail, pending, owed, waiters, fifo, node, woken, bypass, lost,
                 held, owner, depth, hand, target, bargedOwed>>

----------------------------------------------------------------------------
\* The specification.

\* The start: every permit free, nobody waiting.
Init ==
  /\ avail = Permits
  /\ pending = 0
  /\ owed = FALSE
  /\ waiters = 0
  /\ fifo = <<>>
  /\ node = [t \in Tasks |-> "none"]
  /\ woken = [t \in Tasks |-> FALSE]
  /\ bypass = [t \in Tasks |-> 0]
  /\ lost = [t \in Tasks |-> 0]
  /\ held = [t \in Tasks |-> 0]
  /\ owner = NoOwner
  /\ depth = 0
  /\ token = NoTask
  /\ hand = [t \in Tasks |-> 0]
  /\ target = [t \in Tasks |-> NoTask]
  /\ ret = [t \in Tasks |-> "idle"]
  /\ pc = [t \in Tasks |-> "idle"]
  /\ bargedOwed = FALSE

\* The steps a task takes on its own once started: they must happen.
Internal(t) ==
  \/ Push(t) \/ Recheck(t) \/ Poll(t)
  \/ DTake(t) \/ DLoop(t) \/ DGrant(t) \/ DWake(t) \/ DFree(t)

\* Every step the system can take.
Next ==
  \E t \in Tasks :
    \/ Acquire(t) \/ Reenter(t) \/ Cancel(t) \/ Release(t) \/ Internal(t)
    \/ \E u \in Tasks : Give(t, u)

\* Fairness: a started operation finishes, a woken future is polled, and a
\* holder eventually drops its guard. Acquiring, re-entering, cancelling
\* and moving a guard are the caller's choices.
Fairness == \A t \in Tasks : WF_vars(Internal(t)) /\ WF_vars(Release(t))

\* Every behaviour: start in Init, take Next steps or stutter, fairly.
Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ avail \in 0..Permits
  /\ pending \in 0..Permits
  /\ owed \in BOOLEAN
  /\ waiters \in 0..Cardinality(Tasks)
  /\ \A i \in 1..Len(fifo) : fifo[i] \in Tasks
  /\ node \in [Tasks -> NodeStates]
  /\ woken \in [Tasks -> BOOLEAN]
  /\ held \in [Tasks -> 0..(Permits * MaxDepth)]
  /\ owner \in Owners \cup {NoOwner}
  /\ token \in Tasks \cup {NoTask}
  /\ hand \in [Tasks -> 0..Permits]
  /\ pc \in [Tasks -> PCs]

\* `waiters` counts exactly the registered tasks not yet pushed plus the
\* queued nodes.
WaitersCounted == waiters = Cardinality({t \in Tasks : pc[t] = "push"}) + Len(fifo)

\* Only the token holder is inside the drain, and a drainer granting a head
\* still has it at the head of the queue.
DrainExclusive ==
  /\ \A t \in Tasks : pc[t] \in {"dloop", "dgrant", "dwake", "dfree"} <=> token = t
  /\ \A t \in Tasks : pc[t] = "dgrant" => fifo # <<>> /\ Head(fifo) = target[t]

\* Every permit is somewhere: free, pending, held, or in a drainer's hand.
\* Reentrant: the one lock is free, pending, owned, or in a drainer's hand.
PermitsConserved ==
  /\ Kind = "Semaphore" =>
       avail + pending + SumOf(held, Tasks) + SumOf(hand, Tasks) = Permits
  /\ Kind = "Reentrant" =>
       avail + pending + (IF owner # NoOwner THEN 1 ELSE 0) + SumOf(hand, Tasks) = 1

\* MUTUAL EXCLUSION. A Semaphore never has more permits out than it has (a
\* Mutex: at most one holder). A ReentrantMutex's guards are all held by
\* tasks of the one Owner holding it. Lean: mutual_exclusion.
MutualExclusion ==
  /\ Kind = "Semaphore" => SumOf(held, Tasks) <= Permits
  /\ Kind = "Reentrant" => \A t \in Tasks : held[t] > 0 => Owner[t] = owner

\* REENTRANCY DEPTH. The depth is exactly the guards out, and the lock has
\* an owner exactly when the depth is not 0.
ReentrancyDepth ==
  Kind = "Reentrant" =>
    /\ depth = SumOf(held, Tasks)
    /\ (owner = NoOwner <=> depth = 0)

\* BOUNDED BYPASS. During one acquire, a waiter loses the race at most Bound
\* times: after that a release hands it the lock. Nobody starves.
\* Lean: bounded_bypass, release_hands_off_at_bound.
BoundedBypass == \A t \in Tasks : lost[t] <= Bound

\* HANDOFF EXCLUSIVE. No fast-path take ever succeeds while a handoff is
\* owed: the owed bit shuts barging until the head takes its permits.
\* Lean: owed_exclusive, owed_blocks_barging.
HandoffExclusive == ~bargedOwed

\* A parked future that was handed the lock has been woken, or its drainer
\* is about to wake it. Lean: handed_woken.
GrantedWoken ==
  \A t \in Tasks :
    pc[t] = "parked" /\ node[t] = "handed" =>
      woken[t] \/ \E d \in Tasks : pc[d] = "dwake" /\ target[d] = t

\* Every task is between operations.
Quiescent == \A t \in Tasks : pc[t] \in {"idle", "holding", "owned", "parked"}

\* Left behind with nobody to act: permits returned but never distributed;
\* or a live head (every node ahead of it stale) that a drain would serve,
\* because the permits it asks for are free and either a handoff is owed to
\* it or its woken bit is clear.
Stranded ==
  \/ pending > 0
  \/ \E i \in 1..Len(fifo) :
       /\ node[fifo[i]] = "waiting"
       /\ \A j \in 1..(i - 1) : node[fifo[j]] # "waiting"
       /\ avail >= Need[fifo[i]]
       /\ owed \/ ~woken[fifo[i]]

\* NO LOST WAKEUP. A handoff is followed by a wake; and once every task is
\* between operations, no waiter sleeps while it could proceed.
\* Lean: no_stranded_head, handed_woken.
NoLostWakeup == GrantedWoken /\ (Quiescent => ~Stranded)

\* CANCELLATION PASSES ON. An idle task holds nothing: a waiter dropped
\* after a handoff passed the lock on.
CancelPassesOn == \A t \in Tasks : pc[t] = "idle" => held[t] = 0

----------------------------------------------------------------------------
\* Liveness. Checked for the tasks in Watched: tasks with the same Need and
\* Owner role are interchangeable (renaming them maps behaviours to
\* behaviours), so one per role stands for all, at a fraction of the cost.

\* Every parked waiter stops waiting: it is served, unless it cancels.
EveryWaiterServed == \A t \in Watched : (pc[t] = "parked") ~> (pc[t] # "parked")

\* Reentrant: no Owner keeps the lock forever.
OwnersLetGo == \A o \in Owners : []<>(owner # o)

\* Reentrant: if no owner holds the lock forever, every waiter is served.
ReentrantServed == OwnersLetGo => EveryWaiterServed

====
