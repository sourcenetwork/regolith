---- MODULE Sync ----
\* ===========================================================================
\* THE STORY
\* ===========================================================================
\* A lock lets one task at a time into a piece of code. regolith has its own
\* locks for async code (src/sync/): Mutex, Semaphore (a lock with several
\* "permits") and ReentrantMutex. A task that finds the lock taken does not
\* block its thread: it joins a queue of waiters and is woken later.
\*
\* The simplest fair rule would be: when the holder lets go, hand the lock to
\* the waiter that has waited longest. That is fair but slow: the lock then
\* sits idle until that sleeping task gets scheduled, and everyone else
\* waits for it. So these locks allow "barging": whoever asks while the lock
\* is free gets it, even past the queue. A release just wakes the first
\* waiter so it can try again.
\*
\* Barging alone is unfair. Tiny example: task A waits. Each time the lock is
\* released A is woken, but before A gets to run, task B, which is already
\* running, grabs the lock again. A loses the race, and loses it again, for
\* ever. So each waiter counts the races it loses, and after Bound losses
\* the next release does not free the lock at all: it hands it straight to
\* that waiter, and nobody may barge meanwhile ("bounded bypass").
\*
\* What can go wrong, each a RED configuration below: a waiter starves; a
\* release frees the lock and wakes nobody; somebody barges past a handoff;
\* a waiter that gave up (its future was dropped) keeps the lock it had just
\* been handed; a reentrant lock is freed while a guard still exists.
\*
\* What this model shows: over every interleaving of a few tasks acquiring,
\* releasing, cancelling and passing guards around, there is never more
\* than one holder (never more permits out than exist), nobody loses more
\* than Bound races, a handoff cannot be barged, no waiter sleeps beside a
\* lock it could take, and every waiter is served.
\*
\* The primitives covered: Mutex, Semaphore (owned guards included) and
\* ReentrantMutex after D49, with barging and bounded fairness. (Notify
\* keeps FIFO handoff: SyncNotify.tla. RwLock: SyncRwLock.tla.)
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
\*     barging. try_lock is the same CAS. A contended acquire registers a
\*     waiter node at the tail and returns Pending (the code does not spin
\*     first: src/sync/contend.rs says why).
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
\* WHERE THE CODE DIFFERS FROM THIS MODEL (found while checking this file
\* against src/sync on this branch; the promises checked are the same, the
\* mechanism is not step for step what is modelled here).
\*   - Who raises the owed bit. Here the draining release decides: it hands
\*     off when the head's count has reached Bound. In the code the waiter
\*     decides: the retry that would be its MAX_BYPASS-th loss either takes
\*     the lock or raises the HANDOFF bit in the same compare-and-swap
\*     (Lock::take_or_owe, src/sync/contend.rs), and the next drain pass
\*     hands the permits out in queue order.
\*   - Where the count lives. Here in the node (`bypass`); in the code in the
\*     waiting future (Contend::bypass), and a loss in the poll that first
\*     queues is not counted.
\*   - `pending`. The code has no such field: a release adds its permits to
\*     the state word at once, and while the HANDOFF bit is up every barging
\*     acquire is refused, which keeps them for the drain.
\*   - Whom a release wakes. Here only the head; the code also nudges the
\*     waiters behind it that the free permits could serve
\*     (RawSemaphore::pass, src/sync/raw_semaphore.rs).
\*   - The drain role. Here a task that finds the token taken just leaves;
\*     in the code it also sets a DIRTY bit that makes the holder pass again
\*     (src/sync/queue.rs). Same effect as the re-check modelled in DFree.
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
\*   - Spinning: the code does not spin before queueing. If it did, a
\*     failed CAS try changes nothing, so a spin would be one Acquire step
\*     taken at the moment of its last try.
\*   - A task has one request at a time and may not register again while its
\*     previous node is still queued; two nodes of one task act as two tasks.
\*   - A cancel is one step; a drainer's pop and its `waiters` decrement are
\*     one step; letting the token go and the re-check are one step.
\*   - Memory ordering is loom's (plan 7.1).
\*
\* CONFIGURATIONS.
\*   MC_Sync_Green_Mutex          Mutex, three tasks, Bound 2: every
\*                                safety invariant.
\*   MC_Sync_Green_MutexLive      the same with two tasks: every waiter is
\*                                served.
\*   MC_Sync_Green_Semaphore      two permits, task 1 asks for both, owned
\*                                guards moving between three tasks: every
\*                                safety invariant.
\*   MC_Sync_Green_SemaphoreLive  the same with two tasks: every waiter is
\*                                served.
\*   MC_Sync_Green_Reentrant      ReentrantMutex, tasks 1 and 2 of one owner,
\*                                nesting two guards: every safety invariant.
\*   MC_Sync_Green_ReentrantLive  one task of each owner, one guard each: if
\*                                no owner holds forever, every waiter is
\*                                served.
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

\* Borrow the standard TLA+ books: counting numbers, lists, and sizes of finite sets.
EXTENDS Naturals, Sequences, FiniteSets

\* The fixed inputs a configuration chooses.
CONSTANTS
  \* The tasks that use the lock, named by positive numbers.
  Tasks,
  \* Which primitive is modelled: "Semaphore" (a Mutex is a semaphore with one permit) or
  \* "Reentrant" (ReentrantMutex, src/sync/reentrant_mutex.rs).
  Kind,
  \* How many permits there are. A Mutex and a ReentrantMutex have 1.
  Permits,
  \* How many permits each task asks for, as a map from task to number.
  Need,
  \* Each task's owner token, as a map from task to a positive number (ReentrantMutex only; Owner,
  \* src/sync/owner.rs). Tasks with the same token count as one owner.
  Owner,
  \* The largest number of nested guards one task holds (ReentrantMutex only).
  MaxDepth,
  \* TRUE when a guard may move from one task to another (the owned guards of lock_owned and
  \* acquire_owned).
  Owned,
  \* After how many lost races a waiter is handed the lock directly: MAX_BYPASS in
  \* src/sync/contend.rs (16 in the engine, 2 under loom).
  Bound,
  \* The tasks whose "is eventually served" promise is checked: one per role is enough.
  Watched,
  \* "none" for the design, or the name of one planted bug.
  Mutant

\* The value "no task", for the drain token and a drainer's target.
NoTask == 0
\* The value "no owner holds the lock".
NoOwner == 0
\* Every Owner token some task locks with.
Owners == {Owner[t] : t \in Tasks}

\* The kind is one of the two.
ASSUME Kind \in {"Semaphore", "Reentrant"}
\* There is at least one permit, at least one level of nesting, and the bound is at least 1.
ASSUME Permits \in Nat \ {0} /\ MaxDepth \in Nat \ {0} /\ Bound \in Nat \ {0}
\* Owned is a yes or a no, and only tasks are watched.
ASSUME Owned \in BOOLEAN /\ Watched \subseteq Tasks
\* Every task asks for at least one permit and no more than exist.
ASSUME \A t \in Tasks : Need[t] \in 1..Permits
\* Tasks and owner tokens are positive numbers (0 means "none").
ASSUME Tasks \subseteq Nat \ {0} /\ Owners \subseteq Nat \ {0}
\* A reentrant lock has one permit.
ASSUME Kind = "Reentrant" => Permits = 1
\* The mutant is "none" or one of the seven planted bugs.
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

\* The state: everything that changes from one step to the next. Each line says what the variable
\* stands for in the real program.
VARIABLES
  \* The permits that are free to take: the count kept in the state word above the queue's bits
  \* (WaitQueue::state in src/sync/queue.rs, read by RawSemaphore::available in
  \* src/sync/raw_semaphore.rs).
  \* For a ReentrantMutex: 1 when unlocked.
  avail,
  \* Permits a release gave back while waiters were present, not yet handed to a waiter or made
  \* free. Nobody can take them. In the model this is how "the lock stays held during a handoff" is
  \* expressed.
  pending,
  \* The handoff-owed bit: while it is set, nobody may barge (the HANDOFF bit of the state word,
  \* src/sync/queue.rs).
  owed,
  \* How many waiters are registered and not yet removed from the queue. The engine keeps only "is
  \* anybody queued", the QUEUED bit.
  waiters,
  \* The waiter queue: the waiting tasks, oldest first. Each task has at most one node in it (the
  \* Waiter nodes of src/sync/waiter.rs, pushed by WaitQueue::push).
  fifo,
  \* The state of each task's waiter node: see NodeStates below (a Waiter's phase: WAITING, GRANTED
  \* or CANCELLED).
  node,
  \* Each node's "woken" bit: set when the waiter is woken to try again, cleared when it registers
  \* its waker again (the NUDGED bit of a Waiter).
  woken,
  \* Each node's count of lost races since it was queued (Contend::bypass, src/sync/contend.rs).
  bypass,
  \* Model bookkeeping (a "ghost"): how many races each task lost during its current acquire. The
  \* promise BoundedBypass reads it.
  lost,
  \* How many permits each task holds; for a ReentrantMutex, how many guards.
  held,
  \* ReentrantMutex only: the owner token that holds the lock, or NoOwner (ReentrantMutex::holder).
  owner,
  \* ReentrantMutex only: how many guards are out on the lock (ReentrantMutex::depth).
  depth,
  \* The drain token: which task is the one allowed to look at the queue right now, or NoTask (the
  \* DRAINING bit of the state word, src/sync/queue.rs).
  token,
  \* The permits a draining task has set aside for the head of the queue, per draining task.
  hand,
  \* Which waiter a draining task is serving, per draining task.
  target,
  \* Where a task goes on once its drain is over, per task.
  ret,
  \* Where each task is in its operation: its "program counter" (see PCs below).
  pc,
  \* Model bookkeeping: TRUE once somebody took permits by the fast path while a handoff was owed.
  \* The promise HandoffExclusive reads it.
  bargedOwed

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
\* The sum over the empty set is 0.
SumOf(f, S) == IF S = {} THEN 0
               \* Otherwise pick any element x, and add f[x] to the sum over the rest.
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
  \* The queue is not empty,
  /\ fifo # <<>>
  \* and its head h
  /\ LET h == Head(fifo) IN
       \* is stale,
       \/ Stale(h)
       \* or can be handed the permits it asks for (they are free and the drain is in handoff mode),
       \/ avail >= Need[h] /\ HandoffMode(h)
       \* or should be woken (the permits it asks for are free, it has not been woken, and wakes are
       \* on).
       \/ avail >= Need[h] /\ ~woken[h] /\ Wakes

\* Work for a drainer: permits to distribute, an owed bit with nobody left
\* to owe it to, or work at the head.
Work == pending > 0 \/ (owed /\ fifo = <<>>) \/ HeadWork

\* Reentrant: t's Owner holds the lock, so t enters again at once.
CanReenter(t) == Kind = "Reentrant" /\ owner = Owner[t] /\ held[t] < MaxDepth

\* Task t goes on to drain (try the token), and resumes at `r` afterwards.
DrainThen(t, r) ==
  \* It goes to the first step of the drain,
  /\ pc' = [pc EXCEPT ![t] = "dtake"]
  \* and remembers where to go on afterwards.
  /\ ret' = [ret EXCEPT ![t] = r]

\* Task t's drain is over: it resumes where it was going.
Resume(t) ==
  \* It goes where it meant to go,
  /\ pc' = [pc EXCEPT ![t] = ret[t]]
  \* and that memory is cleared.
  /\ ret' = [ret EXCEPT ![t] = "idle"]

\* Task t, holding now, drains if others wait (to pop its stale node and
\* wake the next head for spare permits), else just holds.
HoldThenDrain(t) ==
  \* Others wait: drain, then hold.
  IF waiters > 0 THEN DrainThen(t, "holding")
  \* Nobody waits: just hold.
  ELSE pc' = [pc EXCEPT ![t] = "holding"] /\ UNCHANGED ret

\* The fast-path take: the permits leave `avail` and task t holds them.
\* Records a take made while a handoff was owed (only IgnoreOwed can).
Take(t) ==
  \* The permits it asks for leave the free ones.
  /\ avail' = avail - Need[t]
  \* It holds them.
  /\ held' = [held EXCEPT ![t] = Need[t]]
  \* A reentrant lock notes whose it is now,
  /\ owner' = IF Kind = "Reentrant" THEN Owner[t] ELSE owner
  \* with one guard out.
  /\ depth' = IF Kind = "Reentrant" THEN 1 ELSE depth
  \* If a handoff was owed at this moment, that is recorded.
  /\ bargedOwed' = (bargedOwed \/ owed)

\* Task t gives up n of its permits (Reentrant: n guards). It returns `rel`
\* permits to the state word: a Semaphore returns n; a ReentrantMutex
\* returns its one permit when the depth reaches 0 (mutant NoDepth: at
\* once). With no waiters they become free (one RMW); with waiters they go
\* to `pending` for the drain. `freed` tells whether anything was returned.
GiveUp(t, n) ==
  \* rel: what goes back to the state word. A semaphore: all n.
  LET rel == IF Kind = "Semaphore" THEN n
             \* A reentrant lock: its one permit, once no guard is left (the bug NoDepth: at any
             \* depth); otherwise nothing.
             ELSE IF depth - n = 0 \/ Mutant = "NoDepth" THEN 1 ELSE 0
  \* The task holds n fewer.
  IN /\ held' = [held EXCEPT ![t] = @ - n]
     \* A reentrant lock has n fewer guards out.
     /\ depth' = IF Kind = "Reentrant" THEN depth - n ELSE depth
     \* A reentrant lock that returned its permit has no owner.
     /\ owner' = IF Kind = "Reentrant" /\ rel = 1 THEN NoOwner ELSE owner
     \* Nobody waits:
     /\ IF waiters = 0
          \* the returned permits are free at once.
          THEN avail' = avail + rel /\ UNCHANGED pending
          \* Somebody waits: they are pending, for the drain to distribute.
          ELSE pending' = pending + rel /\ UNCHANGED avail

\* What GiveUp(t, n) returns to the state word (see GiveUp).
Returned(t, n) ==
  \* A semaphore returns all n.
  IF Kind = "Semaphore" THEN n
  \* A reentrant lock returns its one permit once no guard is left (or at once under the bug
  \* NoDepth), else nothing.
  ELSE IF depth - n = 0 \/ Mutant = "NoDepth" THEN 1 ELSE 0

----------------------------------------------------------------------------
\* Acquiring.

\* lock() / acquire(n) / lock(owner), first poll (try_lock is its first
\* branch): the fast-path CAS, barging past any waiters; if it fails,
\* register as a waiter (the waiters-present count goes up).
Acquire(t) ==
  \* The task is idle.
  /\ pc[t] = "idle"
  \* It has no node in the queue.
  /\ ~InFifo(t)
  \* It is not simply entering a reentrant lock its owner already holds.
  /\ ~CanReenter(t)
  \* Are the permits it asks for free, with no handoff owed?
  /\ IF CanTake(t)
       \* Yes: it takes them,
       THEN /\ Take(t)
            \* and holds.
            /\ pc' = [pc EXCEPT ![t] = "holding"]
            \* The waiter count does not change.
            /\ UNCHANGED waiters
       \* No: it registers as a waiter,
       ELSE /\ waiters' = waiters + 1
            \* and goes on to push its node.
            /\ pc' = [pc EXCEPT ![t] = "push"]
            \* Nothing is taken.
            /\ UNCHANGED <<avail, held, owner, depth, bargedOwed>>
  \* Nothing else changes.
  /\ UNCHANGED <<pending, owed, fifo, node, woken, bypass, lost, token, hand, target, ret>>

\* Reentrant: a task whose Owner holds the lock enters again at once, idle
\* or holding. Nothing barges: the owner is already inside.
Reenter(t) ==
  \* The task is idle or holding.
  /\ pc[t] \in {"idle", "holding"}
  \* Its owner holds the lock, and it may nest one more guard.
  /\ CanReenter(t)
  \* It holds one more guard.
  /\ held' = [held EXCEPT ![t] = @ + 1]
  \* One more guard is out.
  /\ depth' = depth + 1
  \* It holds.
  /\ pc' = [pc EXCEPT ![t] = "holding"]
  \* Nothing else changes.
  /\ UNCHANGED <<avail, pending, owed, waiters, fifo, node, woken, bypass, lost,
                 owner, token, hand, target, ret, bargedOwed>>

\* The registered waiter pushes its node (bypass count 0, woken bit clear,
\* Waker inside) at the tail, then re-checks. Mutant NoRecheck: it parks.
Push(t) ==
  \* The task registered and has not pushed yet.
  /\ pc[t] = "push"
  \* Its node joins the tail of the queue.
  /\ fifo' = Append(fifo, t)
  \* The node is waiting.
  /\ node' = [node EXCEPT ![t] = "waiting"]
  \* Its count of lost races starts at 0.
  /\ bypass' = [bypass EXCEPT ![t] = 0]
  \* It has not been woken.
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  \* It goes on to look at the state once more (under the bug NoRecheck it goes straight to sleep).
  /\ pc' = [pc EXCEPT ![t] = IF Mutant = "NoRecheck" THEN "parked" ELSE "recheck"]
  \* Nothing else changes.
  /\ UNCHANGED <<avail, pending, owed, waiters, lost, held, owner, depth, token,
                 hand, target, ret, bargedOwed>>

\* Task t takes a handoff: the permits are already its; the owed bit clears.
TakeHanded(t) ==
  \* Its node is gone.
  /\ node' = [node EXCEPT ![t] = "none"]
  \* Its woken bit is cleared.
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  \* The handoff is no longer owed.
  /\ owed' = FALSE
  \* Its lost races are forgotten: this acquire is over.
  /\ lost' = [lost EXCEPT ![t] = 0]
  \* So is its node's count.
  /\ bypass' = [bypass EXCEPT ![t] = 0]
  \* It holds, and drains first if others wait.
  /\ HoldThenDrain(t)
  \* The permits were already moved to it by the drainer.
  /\ UNCHANGED <<avail, held, owner, depth, bargedOwed>>

\* Task t wins the CAS while its node is queued: it holds, its node is
\* stale, and it drains (it popping its node and maybe waking the next).
WinQueued(t) ==
  \* It takes the permits by the fast path.
  /\ Take(t)
  \* Its node is stale now ("done"): the drainer will pop it.
  /\ node' = [node EXCEPT ![t] = "done"]
  \* Its woken bit is cleared.
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  \* Its lost races are forgotten.
  /\ lost' = [lost EXCEPT ![t] = 0]
  \* So is its node's count.
  /\ bypass' = [bypass EXCEPT ![t] = 0]
  \* It drains (to pop its own node), then holds.
  /\ DrainThen(t, "holding")
  \* The owed bit is untouched.
  /\ UNCHANGED owed

\* The re-check after registering the waker: take a handoff that arrived,
\* or win the CAS, or park.
Recheck(t) ==
  \* The task is at its second look.
  /\ pc[t] = "recheck"
  \* It was handed the permits meanwhile: take the handoff.
  /\ CASE node[t] = "handed" -> TakeHanded(t)
       \* The permits are free and no handoff is owed: take them.
       [] CanTake(t) -> WinQueued(t)
       \* Otherwise: go to sleep.
       [] OTHER -> /\ pc' = [pc EXCEPT ![t] = "parked"]
                   \* Nothing else of the task changes.
                   /\ UNCHANGED <<node, woken, owed, lost, bypass, avail, held, owner,
                                  depth, bargedOwed, ret>>
  \* The queue and the drain are untouched.
  /\ UNCHANGED <<pending, waiters, fifo, token, hand, target>>

\* The executor polls a woken future. Handed: take it. Otherwise try the
\* CAS. Losing: keep the place at the head, count the loss, register the
\* waker again (clearing the woken bit) and re-check. Mutant
\* LoseQueuePosition: the loser goes to the tail with a fresh count.
Poll(t) ==
  \* The task is asleep.
  /\ pc[t] = "parked"
  \* It was woken.
  /\ woken[t]
  \* It was handed the permits:
  /\ CASE node[t] = "handed" ->
            \* take the handoff.
            /\ TakeHanded(t)
            \* The queue and the drain are untouched.
            /\ UNCHANGED <<pending, waiters, fifo, token, hand, target>>
       \* The permits are free and no handoff is owed:
       [] CanTake(t) ->
            \* take them.
            /\ WinQueued(t)
            \* The queue and the drain are untouched.
            /\ UNCHANGED <<pending, waiters, fifo, token, hand, target>>
       \* It lost the race:
       [] OTHER ->
            \* one more lost race is counted,
            /\ lost' = [lost EXCEPT ![t] = @ + 1]
            \* and its woken bit is cleared, so the next release wakes it again.
            /\ woken' = [woken EXCEPT ![t] = FALSE]
            \* Under the bug LoseQueuePosition
            /\ IF Mutant = "LoseQueuePosition"
                 \* it goes to the tail of the queue
                 THEN /\ fifo' = Append(Remove(fifo, t), t)
                      \* with a fresh count.
                      /\ bypass' = [bypass EXCEPT ![t] = 0]
                 \* In the design its node's count goes up by one,
                 ELSE /\ bypass' = [bypass EXCEPT ![t] = @ + 1]
                      \* and it keeps its place.
                      /\ UNCHANGED fifo
            \* It looks at the state once more before sleeping.
            /\ pc' = [pc EXCEPT ![t] = "recheck"]
            \* Nothing else changes.
            /\ UNCHANGED <<avail, pending, owed, waiters, node, held, owner, depth,
                           token, hand, target, ret, bargedOwed>>

\* The pending future is dropped. A waiting node is CAS'd to "cancelled"
\* and the task drains: that pops it if it is the head, passes an unused
\* wake on to the next head, and passes an owed handoff on. A handed node:
\* the permits go back to `pending` (the owed bit stays set), and the drain
\* hands them to the next waiter, or frees them if none waits. Mutant
\* CancelNoPassOn: a handed waiter keeps the lock.
Cancel(t) ==
  \* The task is asleep.
  /\ pc[t] = "parked"
  \* Its woken bit is cleared.
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  \* Its lost races are forgotten.
  /\ lost' = [lost EXCEPT ![t] = 0]
  \* So is its node's count.
  /\ bypass' = [bypass EXCEPT ![t] = 0]
  \* Its node was still waiting:
  /\ IF node[t] = "waiting"
       \* the node is marked cancelled, for the drainer to pop,
       THEN /\ node' = [node EXCEPT ![t] = "cancelled"]
            \* and the task drains, then is idle.
            /\ DrainThen(t, "idle")
            \* It held nothing, so nothing is given back.
            /\ UNCHANGED <<held, owner, depth, pending, avail>>
       \* Its node had been handed the permits: the node is gone.
       ELSE /\ node' = [node EXCEPT ![t] = "none"]
            \* Under the bug CancelNoPassOn
            /\ IF Mutant = "CancelNoPassOn"
                 \* the task simply goes idle,
                 THEN /\ pc' = [pc EXCEPT ![t] = "idle"]
                      \* keeping the permits.
                      /\ UNCHANGED <<held, owner, depth, pending, avail, ret>>
                 \* In the design it gives the permits up:
                 ELSE /\ held' = [held EXCEPT ![t] = 0]
                      \* a reentrant lock has that many fewer guards out,
                      /\ depth' = IF Kind = "Reentrant" THEN depth - held[t] ELSE depth
                      \* and no owner once none is left;
                      /\ owner' = IF Kind = "Reentrant" /\ depth = held[t] THEN NoOwner ELSE owner
                      \* the permits go to pending
                      /\ pending' = pending +
                           \* (a semaphore's permits,
                           (IF Kind = "Semaphore" THEN held[t]
                            \* or a reentrant lock's one permit once no guard is left),
                            ELSE IF depth = held[t] THEN 1 ELSE 0)
                      \* and the task drains, to pass them on, then is idle.
                      /\ DrainThen(t, "idle")
                      \* Nothing becomes free directly.
                      /\ UNCHANGED avail
  \* Nothing else changes.
  /\ UNCHANGED <<owed, waiters, fifo, token, hand, target, bargedOwed>>

----------------------------------------------------------------------------
\* Releasing and moving owned guards.

\* A guard is dropped. A Semaphore gives back all the task's permits; a
\* ReentrantMutex one guard. Returned permits with no waiters are free at
\* once (one RMW); with waiters they are pending and the task drains.
Release(t) ==
  \* The task holds a guard.
  /\ pc[t] \in {"holding", "owned"}
  \* n: what it gives up: one guard of a reentrant lock, everything it holds otherwise.
  /\ LET n    == IF Kind = "Reentrant" THEN 1 ELSE held[t]
         \* rest: what it still holds afterwards.
         rest == held[t] - n
         \* next: it keeps holding if something is left, else it is idle.
         next == IF rest > 0 THEN "holding" ELSE "idle"
     \* It gives the permits up.
     IN /\ GiveUp(t, n)
        \* If something went back to the state word while others wait,
        /\ IF Returned(t, n) > 0 /\ waiters > 0
             \* it drains, then goes on;
             THEN DrainThen(t, next)
             \* otherwise it just goes on.
             ELSE pc' = [pc EXCEPT ![t] = next] /\ UNCHANGED ret
  \* Nothing else changes.
  /\ UNCHANGED <<owed, waiters, fifo, node, woken, bypass, lost, token, hand, target,
                 bargedOwed>>

\* An owned guard (`lock_owned`, `acquire_owned`) moves from task t to an
\* idle task u, which only drops it.
Give(t, u) ==
  \* Only a semaphore with owned guards.
  /\ Kind = "Semaphore" /\ Owned
  \* Two different tasks.
  /\ t # u
  \* The giver holds.
  /\ pc[t] = "holding"
  \* The receiver is idle,
  /\ pc[u] = "idle"
  \* and has no node in the queue.
  /\ ~InFifo(u)
  \* The permits move from the giver to the receiver.
  /\ held' = [held EXCEPT ![t] = 0, ![u] = held[t]]
  \* The giver is idle; the receiver holds an owned guard.
  /\ pc' = [pc EXCEPT ![t] = "idle", ![u] = "owned"]
  \* Nothing else changes.
  /\ UNCHANGED <<avail, pending, owed, waiters, fifo, node, woken, bypass, lost,
                 owner, depth, token, hand, target, ret, bargedOwed>>

----------------------------------------------------------------------------
\* The drain: the only code that pops the queue head and hands permits out.

\* Take the drain token if it is free; if another task holds it, leave: the
\* holder re-checks for work before it lets go.
DTake(t) ==
  \* The task is about to try the token.
  /\ pc[t] = "dtake"
  \* Is the token free?
  /\ IF token = NoTask
       \* Yes: it takes it,
       THEN /\ token' = t
            \* and starts serving the queue.
            /\ pc' = [pc EXCEPT ![t] = "dloop"]
            \* It still remembers where to go on afterwards.
            /\ UNCHANGED ret
       \* No: it leaves and goes where it meant to go.
       ELSE /\ Resume(t)
            \* The token stays with its holder.
            /\ UNCHANGED token
  \* Nothing else changes.
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
  \* The task holds the token and looks at the queue.
  /\ pc[t] = "dloop"
  \* A stale node is at the head:
  /\ IF fifo # <<>> /\ Stale(Head(fifo))
       \* it is popped,
       THEN /\ fifo' = Tail(fifo)
            \* one waiter fewer is counted,
            /\ waiters' = waiters - 1
            \* and the node is gone.
            /\ node' = [node EXCEPT ![Head(fifo)] = "none"]
            \* Nothing else changes; the task looks again.
            /\ UNCHANGED <<avail, pending, owed, hand, target, pc>>
       \* The queue is empty:
       ELSE IF fifo = <<>>
       \* pending permits become free,
       THEN /\ avail' = avail + pending
            \* none is pending,
            /\ pending' = 0
            \* no handoff is owed,
            /\ owed' = FALSE
            \* and the task goes on to let the token go.
            /\ pc' = [pc EXCEPT ![t] = "dfree"]
            \* Nothing else changes.
            /\ UNCHANGED <<waiters, fifo, node, hand, target>>
       \* Otherwise h is the head,
       ELSE LET h == Head(fifo)
                \* and a is every permit that could serve it: the free ones and the pending ones.
                a == avail + pending
            \* Handoff mode:
            IN IF HandoffMode(h)
               \* the owed bit is set, shutting barging,
               THEN /\ owed' = TRUE
                    \* and the pending permits are gathered.
                    /\ pending' = 0
                    \* The head's request can be met:
                    /\ IF a >= Need[h]
                         \* its permits leave the free ones,
                         THEN /\ avail' = a - Need[h]
                              \* are set aside in the drainer's hand,
                              /\ hand' = [hand EXCEPT ![t] = Need[h]]
                              \* for this head,
                              /\ target' = [target EXCEPT ![t] = h]
                              \* and the drainer goes on to grant them.
                              /\ pc' = [pc EXCEPT ![t] = "dgrant"]
                         \* It cannot be met yet: everything gathered stays in the state word (the
                         \* owed bit keeps bargers off),
                         ELSE /\ avail' = a
                              \* and the drainer goes on to let the token go.
                              /\ pc' = [pc EXCEPT ![t] = "dfree"]
                              \* Nothing is set aside.
                              /\ UNCHANGED <<hand, target>>
                    \* The queue is untouched.
                    /\ UNCHANGED <<waiters, fifo, node>>
               \* Not handoff mode: every gathered permit is free,
               ELSE /\ avail' = a
                    \* and none is pending.
                    /\ pending' = 0
                    \* A release wakes the head even if the free permits
                    \* fall short of its request: it competes, and a loss
                    \* counts towards Bound. Waking it only when they
                    \* suffice starves a large request that one-permit
                    \* bargers keep short (TLC found that lasso).
                    \* The head has not been woken, wakes are on, and a release just returned
                    \* permits or the free ones meet its request:
                    /\ IF (pending > 0 \/ a >= Need[h]) /\ ~woken[h] /\ Wakes
                         \* the drainer will wake this head,
                         THEN /\ target' = [target EXCEPT ![t] = h]
                              \* next.
                              /\ pc' = [pc EXCEPT ![t] = "dwake"]
                         \* Otherwise the drainer goes on to let the token go,
                         ELSE /\ pc' = [pc EXCEPT ![t] = "dfree"]
                              \* with no head to serve.
                              /\ UNCHANGED target
                    \* Nothing else changes.
                    /\ UNCHANGED <<owed, waiters, fifo, node, hand>>
  \* The tasks' holdings, the token and the ghosts are untouched.
  /\ UNCHANGED <<woken, bypass, lost, held, owner, depth, token, ret, bargedOwed>>

\* The handoff: CAS the head's node from "waiting" to "handed". On success
\* the debited permits are its (Reentrant: the lock is its Owner's, depth
\* 1) and its node is popped; then it is woken. If its waiter won the CAS
\* on its own or was cancelled first, the permits go back to the drain.
DGrant(t) ==
  \* The drainer is about to grant.
  /\ pc[t] = "dgrant"
  \* h: the head it serves.
  /\ LET h == target[t] IN
     \* Is the head's node still waiting?
     IF node[h] = "waiting"
       \* Yes: the node is marked handed.
       THEN /\ node' = [node EXCEPT ![h] = "handed"]
            \* The permits set aside are the head's now.
            /\ held' = [held EXCEPT ![h] = hand[t]]
            \* A reentrant lock notes whose it is,
            /\ owner' = IF Kind = "Reentrant" THEN Owner[h] ELSE owner
            \* with one guard out.
            /\ depth' = IF Kind = "Reentrant" THEN 1 ELSE depth
            \* The drainer's hand is empty.
            /\ hand' = [hand EXCEPT ![t] = 0]
            \* The head's node leaves the queue.
            /\ fifo' = Remove(fifo, h)
            \* One waiter fewer is counted.
            /\ waiters' = waiters - 1
            \* The drainer goes on to wake the head.
            /\ pc' = [pc EXCEPT ![t] = "dwake"]
            \* Nothing else changes.
            /\ UNCHANGED <<pending, target>>
       \* No (the waiter took the lock itself, or was cancelled): the permits go back to pending,
       ELSE /\ pending' = pending + hand[t]
            \* the drainer's hand is empty,
            /\ hand' = [hand EXCEPT ![t] = 0]
            \* it serves nobody,
            /\ target' = [target EXCEPT ![t] = NoTask]
            \* and it looks at the queue again.
            /\ pc' = [pc EXCEPT ![t] = "dloop"]
            \* Nothing else changes.
            /\ UNCHANGED <<node, held, owner, depth, fifo, waiters>>
  \* The free permits, the owed bit, the woken bits and the ghosts are untouched.
  /\ UNCHANGED <<avail, owed, woken, bypass, lost, token, ret, bargedOwed>>

\* Waker::wake for the head: its woken bit is set.
DWake(t) ==
  \* The drainer is about to wake.
  /\ pc[t] = "dwake"
  \* The waiter it serves is woken.
  /\ woken' = [woken EXCEPT ![target[t]] = TRUE]
  \* It serves nobody any more.
  /\ target' = [target EXCEPT ![t] = NoTask]
  \* It looks at the queue again.
  /\ pc' = [pc EXCEPT ![t] = "dloop"]
  \* Nothing else changes.
  /\ UNCHANGED <<avail, pending, owed, waiters, fifo, node, bypass, lost, held,
                 owner, depth, token, hand, ret, bargedOwed>>

\* Let the token go and look again: work left by a task that found the
\* token taken is picked up here.
DFree(t) ==
  \* The drainer is about to let the token go.
  /\ pc[t] = "dfree"
  \* The token is free.
  /\ token' = NoTask
  \* Is there work left (something a task that found the token taken left behind)?
  /\ IF Work
       \* Yes: try the token again.
       THEN pc' = [pc EXCEPT ![t] = "dtake"] /\ UNCHANGED ret
       \* No: go where the task meant to go.
       ELSE Resume(t)
  \* Nothing else changes.
  /\ UNCHANGED <<avail, pending, owed, waiters, fifo, node, woken, bypass, lost,
                 held, owner, depth, hand, target, bargedOwed>>

----------------------------------------------------------------------------
\* The specification.

\* The start: every permit free, nobody waiting.
Init ==
  \* Every permit is free.
  /\ avail = Permits
  \* None is pending.
  /\ pending = 0
  \* No handoff is owed.
  /\ owed = FALSE
  \* Nobody waits.
  /\ waiters = 0
  \* The queue is empty.
  /\ fifo = <<>>
  \* No task has a node.
  /\ node = [t \in Tasks |-> "none"]
  \* Nobody was woken.
  /\ woken = [t \in Tasks |-> FALSE]
  \* No node has lost a race.
  /\ bypass = [t \in Tasks |-> 0]
  \* No task has lost a race.
  /\ lost = [t \in Tasks |-> 0]
  \* Nobody holds anything.
  /\ held = [t \in Tasks |-> 0]
  \* A reentrant lock has no owner,
  /\ owner = NoOwner
  \* and no guard out.
  /\ depth = 0
  \* The drain token is free.
  /\ token = NoTask
  \* No drainer has set permits aside.
  /\ hand = [t \in Tasks |-> 0]
  \* No drainer serves anybody.
  /\ target = [t \in Tasks |-> NoTask]
  \* Every task would go on to idle.
  /\ ret = [t \in Tasks |-> "idle"]
  \* Every task is idle.
  /\ pc = [t \in Tasks |-> "idle"]
  \* Nobody barged past an owed handoff.
  /\ bargedOwed = FALSE

\* The steps a task takes on its own once started: they must happen.
Internal(t) ==
  \* The waiter's own steps: push, second look, poll.
  \/ Push(t) \/ Recheck(t) \/ Poll(t)
  \* The drain's steps.
  \/ DTake(t) \/ DLoop(t) \/ DGrant(t) \/ DWake(t) \/ DFree(t)

\* Every step the system can take.
Next ==
  \* Some task
  \E t \in Tasks :
    \* acquires, re-enters, cancels, releases, or takes one of its own steps,
    \/ Acquire(t) \/ Reenter(t) \/ Cancel(t) \/ Release(t) \/ Internal(t)
    \* or gives its owned guard to another task.
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
  \* The free permits never exceed the permits.
  /\ avail \in 0..Permits
  \* Nor do the pending ones.
  /\ pending \in 0..Permits
  \* The owed bit is a yes or a no.
  /\ owed \in BOOLEAN
  \* No more waiters than tasks.
  /\ waiters \in 0..Cardinality(Tasks)
  \* The queue holds tasks.
  /\ \A i \in 1..Len(fifo) : fifo[i] \in Tasks
  \* Every node is in one of the node states.
  /\ node \in [Tasks -> NodeStates]
  \* Every woken bit is a yes or a no.
  /\ woken \in [Tasks -> BOOLEAN]
  \* Nobody holds more than the permits times the nesting depth.
  /\ held \in [Tasks -> 0..(Permits * MaxDepth)]
  \* The owner is an owner token or none.
  /\ owner \in Owners \cup {NoOwner}
  \* The token is with a task or free.
  /\ token \in Tasks \cup {NoTask}
  \* A drainer's hand holds at most the permits.
  /\ hand \in [Tasks -> 0..Permits]
  \* Every task is at one of the known places.
  /\ pc \in [Tasks -> PCs]

\* `waiters` counts exactly the registered tasks not yet pushed plus the
\* queued nodes.
\* Rules out a waiter that is queued but not counted: a release would then believe nobody waits,
\* free the lock in one step, and wake nobody.
WaitersCounted == waiters = Cardinality({t \in Tasks : pc[t] = "push"}) + Len(fifo)

\* Only the token holder is inside the drain, and a drainer granting a head
\* still has it at the head of the queue.
DrainExclusive ==
  \* A task is inside the drain exactly when it holds the token.
  /\ \A t \in Tasks : pc[t] \in {"dloop", "dgrant", "dwake", "dfree"} <=> token = t
  \* A drainer about to grant still has its head at the front of the queue.
  /\ \A t \in Tasks : pc[t] = "dgrant" => fifo # <<>> /\ Head(fifo) = target[t]

\* Every permit is somewhere: free, pending, held, or in a drainer's hand.
\* Reentrant: the one lock is free, pending, owned, or in a drainer's hand.
PermitsConserved ==
  \* For a semaphore:
  /\ Kind = "Semaphore" =>
       \* the free, pending, held and set-aside permits add up to the permits there are. Rules out a
       \* permit that vanishes (the lock is lost for ever) or appears from nowhere (two holders).
       avail + pending + SumOf(held, Tasks) + SumOf(hand, Tasks) = Permits
  \* For a reentrant lock:
  /\ Kind = "Reentrant" =>
       \* its one permit is free, pending, with an owner, or set aside: exactly one of these.
       avail + pending + (IF owner # NoOwner THEN 1 ELSE 0) + SumOf(hand, Tasks) = 1

\* MUTUAL EXCLUSION. A Semaphore never has more permits out than it has (a
\* Mutex: at most one holder). A ReentrantMutex's guards are all held by
\* tasks of the one Owner holding it. Lean: mutual_exclusion.
MutualExclusion ==
  \* For a semaphore: no more permits are held than exist. Rules out, for a Mutex, two tasks inside
  \* the critical section at once.
  /\ Kind = "Semaphore" => SumOf(held, Tasks) <= Permits
  \* For a reentrant lock: every task holding a guard belongs to the owner that holds the lock.
  \* Rules out a second owner getting in.
  /\ Kind = "Reentrant" => \A t \in Tasks : held[t] > 0 => Owner[t] = owner

\* REENTRANCY DEPTH. The depth is exactly the guards out, and the lock has
\* an owner exactly when the depth is not 0.
ReentrancyDepth ==
  \* For a reentrant lock:
  Kind = "Reentrant" =>
    \* the depth equals the number of guards out,
    /\ depth = SumOf(held, Tasks)
    \* and the lock has no owner exactly when no guard is out. Rules out a lock that is free while a
    \* guard still exists (the bug NoDepth), and one that stays owned with no guard left.
    /\ (owner = NoOwner <=> depth = 0)

\* BOUNDED BYPASS. During one acquire, a waiter loses the race at most Bound
\* times: after that a release hands it the lock. Nobody starves.
\* Lean: bounded_bypass, release_hands_off_at_bound.
\* Rules out, for example: a waiter that is woken again and again and every time finds a faster
\* thread already took the lock, for ever. After Bound lost races it is handed the lock directly.
BoundedBypass == \A t \in Tasks : lost[t] <= Bound

\* HANDOFF EXCLUSIVE. No fast-path take ever succeeds while a handoff is
\* owed: the owed bit shuts barging until the head takes its permits.
\* Lean: owed_exclusive, owed_blocks_barging.
\* Rules out, for example: the lock is being handed to a waiter that lost Bound times, and a
\* newcomer grabs it first through the fast path.
HandoffExclusive == ~bargedOwed

\* A parked future that was handed the lock has been woken, or its drainer
\* is about to wake it. Lean: handed_woken.
GrantedWoken ==
  \* For every task
  \A t \in Tasks :
    \* that sleeps with its node marked handed:
    pc[t] = "parked" /\ node[t] = "handed" =>
      \* its woken bit is set, or some drainer is just about to wake it.
      woken[t] \/ \E d \in Tasks : pc[d] = "dwake" /\ target[d] = t

\* Every task is between operations.
Quiescent == \A t \in Tasks : pc[t] \in {"idle", "holding", "owned", "parked"}

\* Left behind with nobody to act: permits returned but never distributed;
\* or a live head (every node ahead of it stale) that a drain would serve,
\* because the permits it asks for are free and either a handoff is owed to
\* it or its woken bit is clear.
Stranded ==
  \* Permits were returned and nobody distributes them,
  \/ pending > 0
  \* or some queued node
  \/ \E i \in 1..Len(fifo) :
       \* is still waiting,
       /\ node[fifo[i]] = "waiting"
       \* is the first waiting one (everything ahead of it is stale),
       /\ \A j \in 1..(i - 1) : node[fifo[j]] # "waiting"
       \* could get the permits it asks for,
       /\ avail >= Need[fifo[i]]
       \* and either a handoff is owed to it or it was never woken.
       /\ owed \/ ~woken[fifo[i]]

\* NO LOST WAKEUP. A handoff is followed by a wake; and once every task is
\* between operations, no waiter sleeps while it could proceed.
\* Lean: no_stranded_head, handed_woken.
\* Rules out, for example: a release makes the lock free and wakes nobody; the waiter sleeps for
\* ever beside a free lock.
NoLostWakeup == GrantedWoken /\ (Quiescent => ~Stranded)

\* CANCELLATION PASSES ON. An idle task holds nothing: a waiter dropped
\* after a handoff passed the lock on.
\* Rules out, for example: a waiter is handed the lock, its future is dropped before it runs, and
\* the lock stays held by nobody: everyone after it waits for ever.
CancelPassesOn == \A t \in Tasks : pc[t] = "idle" => held[t] = 0

----------------------------------------------------------------------------
\* Liveness. Checked for the tasks in Watched: tasks with the same Need and
\* Owner role are interchangeable (renaming them maps behaviours to
\* behaviours), so one per role stands for all, at a fraction of the cost.

\* Every parked waiter stops waiting: it is served, unless it cancels.
\* Rules out a waiter that waits for ever although the lock keeps being released.
EveryWaiterServed == \A t \in Watched : (pc[t] = "parked") ~> (pc[t] # "parked")

\* Reentrant: no Owner keeps the lock forever.
OwnersLetGo == \A o \in Owners : []<>(owner # o)

\* Reentrant: if no owner holds the lock forever, every waiter is served.
ReentrantServed == OwnersLetGo => EveryWaiterServed

====
