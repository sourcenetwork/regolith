---- MODULE Sync ----
\* regolith::sync, the waiter queue every waiting primitive is built on
\* (plan 4.11, D25, D26, D46): Mutex, Semaphore (owned permits included),
\* ReentrantMutex and Notify.
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/Sync.lean:
\*   step_inv, reachable_inv      the queue's invariant holds in every state
\*                                every sequence of acquires, try_acquires,
\*                                releases, polls and cancels reaches
\*   at_most_one_owner            one permit: at most one owner at any time
\*                                (MutualExclusion here)
\*   permits_bounded              n permits: at most n holders
\*   fifo_served, served_in_order no request is served ahead of one that
\*                                entered the line before it and still
\*                                waits; cancelled ones are skipped
\*                                (FifoHandoff here)
\*   no_stranded_waiter           a waiter never waits while a permit is free
\*                                (NoLostWakeup's Stranded here)
\*   handed_holds,                a waiter is woken only once it owns the
\*   no_lost_handoff              permit it waits for, and one handed a
\*                                permit is woken or owed a wake
\*                                (GrantedWoken here)
\*   release_serves_head          a release hands the oldest waiter the permit
\*   position_never_grows,        a waiter's place in the queue only moves
\*   handoff_advances             forward, one place per handoff, so every
\*                                waiter is served after finitely many
\*   barging_breaks_fifo,         the RED cases, as counterexamples
\*   wake_before_handoff_strands,
\*   cancel_without_pass_on_strands
\* TLC checks the concurrent protocol here, step by atomic step, for three
\* tasks; Lean proves the queue's laws for every number of tasks.
\*
\* THE DESIGN (plan 4.11). Nothing blocks a thread. A contended acquire
\* returns Pending with its Waker registered; a release hands what it frees
\* to the next waiter in FIFO order and only then wakes it. Every wait is a
\* Future, every primitive has a try_ form that never waits, and a try_ form
\* fails while others wait, so it never jumps the queue (D25). Dropping a
\* pending acquire removes its waiter, and if ownership reached it first,
\* passes it on. Reentrancy is keyed by an Owner token, not a thread (D26).
\*
\* THE PROTOCOL MODELLED, one atomic step per word-sized CAS or queue
\* operation:
\*   - one state word holds `avail` (free permits) and `waiters` (waiters
\*     registered and not yet popped from the queue). The fast path takes
\*     permits only when `waiters` is 0, so it never passes a waiter;
\*   - a contended acquire registers (waiters + 1), pushes its node onto the
\*     lock-free FIFO with its Waker, then drains (below). The drain after
\*     the push is the re-check: a release that ran between the failed fast
\*     path and the push found no node to hand to, and left its permits in
\*     `avail` for this drain to find;
\*   - a node's state is one word, CAS'd from "waiting" to exactly one of
\*     "granted" (by the drainer), "cancelled" (by the dropped future) or
\*     "broadcast" (Notify's notify_waiters). One CAS wins;
\*   - the drain token. Only the task holding it pops the queue and hands
\*     out permits, so the head it inspects is the head it pops. A task that
\*     finds the token taken does not wait for it: it leaves, and the holder
\*     re-checks for work as it lets the token go. Nothing ever waits on the
\*     token, so no task's progress depends on a token it cannot take;
\*   - the drainer debits `avail` for the head (into `hand`), CASes the
\*     node to "granted" (handing the permits over), and only then wakes
\*     it. If a cancel won the node's CAS, the drainer returns the permits
\*     and drops the stale node.
\*
\* PRIMITIVES (Kind).
\*   "Semaphore"  Permits permits; task t's acquire asks for Need[t] of
\*                them, strictly FIFO (a large request at the head is not
\*                passed by a small one behind it). A Mutex is Permits = 1.
\*                Owned permits (`lock_owned`, `acquire_owned`): a guard is
\*                not tied to its task, so it may move to another task,
\*                which drops it (action Give).
\*   "Reentrant"  ReentrantMutex: Permits = 1, plus `owner` and `depth`. A
\*                task whose Owner already holds the lock enters again at
\*                once (depth + 1), whichever task of that owner it is; the
\*                lock is released when the last guard drops (depth 0).
\*   "Notify"     notify_one stores one permit (at most one: notify_one
\*                calls with nobody waiting coalesce), notified() consumes
\*                one, with the same queue, handoff and pass-on.
\*                notify_waiters notifies every waiter registered before it
\*                and stores nothing: it bumps a generation `bgen` in the
\*                state word and CASes every waiting node to "broadcast"
\*                (one step here); a waiter that registered under an older
\*                generation but pushed its node after the broadcast
\*                notifies itself at the push.
\*
\* DESIGN CHOICES WHERE THE PLAN IS SILENT, recorded in the final report.
\*   - The drain token above. The plan asks for kovan's lock-free FIFO and
\*     a handoff; a FIFO pop and a permit debit are separate words, and two
\*     drainers could each debit for one head and pop two. One drainer at a
\*     time, with no one waiting for it, closes that.
\*   - A cancelled or broadcast node stays in the FIFO until the drainer
\*     pops it, and `waiters` counts it until then: the fast path stays shut
\*     a little longer, which is safe, and the canceller drains so a stale
\*     head never strands the waiter behind it.
\*   - A broadcast notifies the nodes in the queue at that step, and a node
\*     registered under an older generation notifies itself; so exactly the
\*     waiters registered before notify_waiters are notified.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - A task has one request at a time, and may not register again while
\*     its previous (cancelled or broadcast) node is still in the queue.
\*     Nodes are independent objects; two nodes of one task behave as two
\*     tasks with one node each, which the three tasks here cover.
\*   - A cancel is one step: the node CAS and, when the node was granted,
\*     returning what it was handed. The canceller is the only party that
\*     touches those permits after the CAS, so splitting the step changes
\*     no other task's view.
\*   - A drainer's pop and its `waiters` decrement are one step; between
\*     them `waiters` over-counts, which only keeps the fast path shut.
\*   - Letting the token go and the re-check are one step. A task that
\*     frees permits between them would find the token free and drain
\*     itself, so the split only adds a second, redundant attempt.
\*   - Per-task bookkeeping nobody reads any more (a finished node's state,
\*     a finished drain's target) is reset at once, so states that differ
\*     only in stale fields are one state.
\*   - Memory ordering. TLC explores sequentially consistent interleavings;
\*     the weak-memory orderings are loom's to check (plan 7.1).
\*
\* CONFIGURATIONS.
\*   MC_Sync_Green_Mutex          Mutex, three tasks: every invariant, and
\*                                every waiter is eventually served.
\*   MC_Sync_Green_Semaphore      two permits, one task asking for both,
\*                                owned guards moving between tasks.
\*   MC_Sync_Green_Reentrant      ReentrantMutex, two tasks of one owner.
\*   MC_Sync_Green_Notify         Notify with notify_one and notify_waiters.
\*   MC_Sync_Red_Barging          try_acquire ignores waiters: FifoHandoff.
\*   MC_Sync_Red_WakeBeforeHandoff  wake, then hand over: NoLostWakeup.
\*   MC_Sync_Red_CancelNoPassOn   a granted, cancelled waiter keeps what it
\*                                was handed: CancelPassesOn.
\*   MC_Sync_Red_NoRecheck        park right after the push: NoLostWakeup.
\*   MC_Sync_Red_DrainNoRecheck   let the token go without re-checking:
\*                                NoLostWakeup.
\*   MC_Sync_Red_CancelNoDrain    a cancelled head is left for someone else:
\*                                NoLostWakeup.
\*   MC_Sync_Red_NoDepth          a reentrant guard drop frees the lock at
\*                                any depth: ReentrancyDepth.
\*   MC_Sync_Red_NoGenCheck       a waiter that pushed after a broadcast
\*                                misses it: NoLostWakeup.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Tasks,     \* the tasks using the primitive: positive naturals
  Kind,      \* "Semaphore", "Reentrant" or "Notify"
  Permits,   \* the permits: a Mutex and a ReentrantMutex have 1; Notify
             \* stores at most 1
  Need,      \* [Tasks -> 1..Permits]: how many permits task t asks for
  Owner,     \* [Tasks -> positive naturals]: the Owner token task t locks
             \* with (Reentrant only; ignored otherwise)
  MaxDepth,  \* the most nested guards one task holds (Reentrant)
  Owned,     \* TRUE when guards may move between tasks (Semaphore)
  MaxBcast,  \* the most notify_waiters calls in one behaviour (Notify)
  Notifiers, \* Notify: the tasks that notify; the others wait on notified()
  Watched,   \* the tasks whose liveness is checked: one per role (below)
  Mutant     \* "none" for the design, or the name of one defect

\* The value "no task", for the drain token and a drainer's target.
NoTask == 0
\* The value "no owner holds the lock".
NoOwner == 0
\* Every Owner token some task locks with.
Owners == {Owner[t] : t \in Tasks}

ASSUME Kind \in {"Semaphore", "Reentrant", "Notify"}
ASSUME Permits \in Nat \ {0} /\ MaxDepth \in Nat \ {0} /\ MaxBcast \in Nat
ASSUME Owned \in BOOLEAN /\ Notifiers \subseteq Tasks /\ Watched \subseteq Tasks
ASSUME \A t \in Tasks : Need[t] \in 1..Permits
ASSUME Tasks \subseteq Nat \ {0} /\ Owners \subseteq Nat \ {0}
ASSUME Kind # "Semaphore" => Permits = 1
ASSUME Mutant \in {"none", "Barging", "WakeBeforeHandoff", "CancelNoPassOn",
                   "NoRecheck", "DrainNoRecheck", "CancelNoDrain", "NoDepth",
                   "NoGenCheck"}

\* Configuration helpers, named in the MC_Sync_*.cfg files.
\* Every task asks for one permit.
NeedOne == [t \in Tasks |-> 1]
\* Task 1 asks for every permit, the others for one: a large request that
\* the small ones behind it must not pass.
NeedFirstAll == [t \in Tasks |-> IF t = 1 THEN Permits ELSE 1]
\* Every task is its own Owner.
OwnerEach == [t \in Tasks |-> t]
\* Tasks 1 and 2 share Owner 1 (two tasks pinned to one thread, say); task 3
\* is Owner 2.
OwnerPair == [t \in Tasks |-> IF t = 3 THEN 2 ELSE 1]

VARIABLES
  avail,    \* free permits. Notify: 1 when a permit is stored
  waiters,  \* registered waiters not yet popped, in the same word as avail
  fifo,     \* the waiter queue: tasks, oldest first (each task's one node)
  node,     \* [Tasks -> state of the task's node]
  woken,    \* [Tasks -> BOOLEAN]: Waker::wake ran since the waker was registered
  held,     \* [Tasks -> Nat]: permits held (Reentrant: guards held)
  owner,    \* Reentrant: the Owner holding the lock, or NoOwner
  depth,    \* Reentrant: guards out on the lock, over every task of the owner
  token,    \* the drain token: the task holding it, or NoTask
  hand,     \* [Tasks -> Nat]: permits a drainer debited for the head it grants
  target,   \* [Tasks -> Tasks \cup {NoTask}]: the head a drainer grants or wakes
  ret,      \* [Tasks -> pc]: where a task resumes once its drain ends
  pc,       \* [Tasks -> pc]: where each task is in its operation
  line,     \* ghost: tasks with a live request, in the order they entered
            \* (pushed a node, or took permits on the fast path)
  bgen,     \* Notify: the broadcast generation, in the state word
  gen,      \* [Tasks -> Nat]: the generation a waiter registered under
  bwake     \* [Tasks -> SUBSET Tasks]: waiters a broadcaster has yet to wake

\* Every variable, so a step that changes none of them is a stutter.
vars == <<avail, waiters, fifo, node, woken, held, owner, depth, token, hand,
          target, ret, pc, line, bgen, gen, bwake>>

\* The steps of the drain, where a task may hold the token.
DrainPCs == {"dtake", "dloop", "dgrant", "dwake", "dfree"}

\* The places a task can be. A task is "idle" (not using the primitive),
\* "holding" (owns permits or guards), "owned" (holds a guard another task
\* moved to it), "push" (registered, about to push its node), "parked" (its
\* future returned Pending), "bwake" (a broadcaster waking waiters), or in
\* one of the drain steps.
PCs == {"idle", "holding", "owned", "push", "parked", "bwake"} \cup DrainPCs

\* The states of a node. "none": no node, or one nobody looks at any more.
NodeStates == {"none", "waiting", "granted", "cancelled", "broadcast"}

----------------------------------------------------------------------------
\* Helpers.

\* The sum of f[x] over a finite set S.
RECURSIVE SumOf(_, _)
SumOf(f, S) == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

\* Sequence s without element x.
Remove(s, x) == SelectSeq(s, LAMBDA y : y # x)

\* The smaller of two naturals.
Min(a, b) == IF a <= b THEN a ELSE b

\* Task t has a node in the queue (live or stale).
InFifo(t) == \E i \in 1..Len(fifo) : fifo[i] = t

\* Task t's future still waits on its node: parked, or running the drain
\* that re-checks right after its push.
Waits(t) == pc[t] = "parked" \/ (pc[t] \in DrainPCs /\ ret[t] = "parked")

\* The head of the queue is work for a drainer: a stale node to drop, or a
\* waiting node the free permits satisfy.
Work == fifo # <<>> /\ (node[Head(fifo)] # "waiting" \/ avail >= Need[Head(fifo)])

\* Reentrant: t's Owner already holds the lock, so t enters without
\* queueing (bounded by MaxDepth nested guards per task).
CanReenter(t) == Kind = "Reentrant" /\ owner = Owner[t] /\ held[t] < MaxDepth

\* What giving up n permits (Reentrant: n guards) does to the primitive's
\* words. A Semaphore returns them to `avail`. A ReentrantMutex lowers the
\* depth and frees the lock when it reaches 0 (mutant NoDepth: at once).
\* Notify stores the permit again, still at most one.
GiveUp(t, n) ==
  /\ held' = [held EXCEPT ![t] = @ - n]
  /\ IF Kind = "Reentrant"
       THEN /\ depth' = depth - n
            /\ IF depth - n = 0 \/ Mutant = "NoDepth"
                 THEN owner' = NoOwner /\ avail' = 1
                 ELSE UNCHANGED <<owner, avail>>
       ELSE /\ avail' = IF Kind = "Notify" THEN Min(1, avail + n) ELSE avail + n
            /\ UNCHANGED <<owner, depth>>

\* Task t goes on to drain (try the token), and resumes at `r` afterwards.
DrainThen(t, r) ==
  /\ pc' = [pc EXCEPT ![t] = "dtake"]
  /\ ret' = [ret EXCEPT ![t] = r]

\* Task t's drain is over: it resumes where it was going.
Resume(t) ==
  /\ pc' = [pc EXCEPT ![t] = ret[t]]
  /\ ret' = [ret EXCEPT ![t] = "idle"]

----------------------------------------------------------------------------
\* Acquiring.

\* The fast path's take: the permits leave `avail` and the task holds them.
\* Notify consumes the stored permit at once and is done.
Take(t) ==
  /\ avail' = avail - Need[t]
  /\ IF Kind = "Notify"
       THEN /\ pc' = [pc EXCEPT ![t] = "idle"]
            /\ UNCHANGED <<held, owner, depth, line>>
       ELSE /\ held' = [held EXCEPT ![t] = Need[t]]
            /\ owner' = IF Kind = "Reentrant" THEN Owner[t] ELSE owner
            /\ depth' = IF Kind = "Reentrant" THEN 1 ELSE depth
            /\ line' = Append(line, t)
            /\ pc' = [pc EXCEPT ![t] = "holding"]

\* lock() / acquire(n) / lock(owner) / notified(), first poll. One CAS on the
\* state word: take the permits if nobody is registered and enough are free;
\* otherwise register as a waiter, recording the broadcast generation.
Acquire(t) ==
  /\ pc[t] = "idle"
  /\ t \notin Notifiers
  /\ ~InFifo(t)
  /\ ~CanReenter(t)
  /\ IF waiters = 0 /\ avail >= Need[t]
       THEN /\ Take(t)
            /\ UNCHANGED <<waiters, gen>>
       ELSE /\ waiters' = waiters + 1
            /\ gen' = [gen EXCEPT ![t] = bgen]
            /\ pc' = [pc EXCEPT ![t] = "push"]
            /\ UNCHANGED <<avail, held, owner, depth, line>>
  /\ UNCHANGED <<fifo, node, woken, token, hand, target, ret, bgen, bwake>>

\* try_lock() / try_acquire(n): the same CAS, never waiting. It succeeds
\* only when nobody is registered (D25: it never jumps the queue). A failed
\* try changes nothing, so only the success is a step. Mutant Barging:
\* it ignores the registered waiters.
TryAcquire(t) ==
  /\ pc[t] = "idle"
  /\ t \notin Notifiers
  /\ ~CanReenter(t)
  /\ waiters = 0 \/ Mutant = "Barging"
  /\ avail >= Need[t]
  /\ Take(t)
  /\ UNCHANGED <<waiters, fifo, node, woken, token, hand, target, ret, bgen, gen, bwake>>

\* Reentrant: a task whose Owner holds the lock enters again at once, idle
\* or already holding. Not an arrival: the owner is already inside, so it
\* passes no one (and is not recorded in `line`).
Reenter(t) ==
  /\ pc[t] \in {"idle", "holding"}
  /\ CanReenter(t)
  /\ held' = [held EXCEPT ![t] = @ + 1]
  /\ depth' = depth + 1
  /\ pc' = [pc EXCEPT ![t] = "holding"]
  /\ UNCHANGED <<avail, waiters, fifo, node, woken, owner, token, hand, target,
                 ret, line, bgen, gen, bwake>>

\* The registered waiter pushes its node, Waker inside, onto the FIFO, then
\* drains: the re-check that finds permits a release left in `avail`
\* between the failed fast path and this push. Notify: a broadcast that ran
\* since registration could not see this node, so the waiter notifies itself.
\* Mutant NoRecheck: it parks at once. Mutant NoGenCheck: it skips the
\* generation check.
Push(t) ==
  /\ pc[t] = "push"
  /\ fifo' = Append(fifo, t)
  /\ line' = Append(line, t)
  /\ IF Kind = "Notify" /\ gen[t] < bgen /\ Mutant # "NoGenCheck"
       THEN /\ node' = [node EXCEPT ![t] = "broadcast"]
            /\ woken' = [woken EXCEPT ![t] = TRUE]
            /\ DrainThen(t, "parked")
       ELSE /\ node' = [node EXCEPT ![t] = "waiting"]
            /\ woken' = [woken EXCEPT ![t] = FALSE]
            /\ IF Mutant = "NoRecheck"
                 THEN pc' = [pc EXCEPT ![t] = "parked"] /\ UNCHANGED ret
                 ELSE DrainThen(t, "parked")
  /\ UNCHANGED <<avail, waiters, held, owner, depth, token, hand, target, bgen, gen, bwake>>

\* The executor polls a woken future. If its node was granted (or
\* broadcast), the acquire completes: it holds what it was handed (Notify:
\* it consumes the permit, or holds nothing after a broadcast). Otherwise it
\* registers its waker again and stays Pending.
Poll(t) ==
  /\ pc[t] = "parked"
  /\ woken[t]
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  /\ IF node[t] \in {"granted", "broadcast"}
       THEN \* A broadcast node still in the queue stays marked stale for the
            \* drainer; any other finished node is forgotten.
            /\ node' = [node EXCEPT ![t] = IF InFifo(t) THEN node[t] ELSE "none"]
            /\ gen' = [gen EXCEPT ![t] = 0]
            /\ IF Kind = "Notify"
                 THEN /\ pc' = [pc EXCEPT ![t] = "idle"]
                      /\ held' = [held EXCEPT ![t] = 0]
                      /\ line' = Remove(line, t)
                 ELSE /\ pc' = [pc EXCEPT ![t] = "holding"]
                      /\ UNCHANGED <<held, line>>
       ELSE UNCHANGED <<node, gen, pc, held, line>>
  /\ UNCHANGED <<avail, waiters, fifo, owner, depth, token, hand, target, ret,
                 bgen, bwake>>

\* The pending future is dropped. Its node is CAS'd from "waiting" to
\* "cancelled". If ownership reached it first ("granted"), it passes it on:
\* it gives up what it was handed and drains, so the next waiter gets it.
\* Either way it drains, so a cancelled head does not strand the waiter
\* behind it. Mutant CancelNoPassOn: a granted waiter keeps its permits.
\* Mutant CancelNoDrain: a waiting node is cancelled and nobody drains.
Cancel(t) ==
  /\ pc[t] = "parked"
  /\ line' = Remove(line, t)
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  /\ gen' = [gen EXCEPT ![t] = 0]
  /\ CASE node[t] = "waiting" ->
            /\ node' = [node EXCEPT ![t] = "cancelled"]
            /\ IF Mutant = "CancelNoDrain"
                 THEN pc' = [pc EXCEPT ![t] = "idle"] /\ UNCHANGED ret
                 ELSE DrainThen(t, "idle")
            /\ UNCHANGED <<avail, held, owner, depth>>
       [] node[t] = "granted" ->
            /\ node' = [node EXCEPT ![t] = "none"]
            /\ IF Mutant = "CancelNoPassOn"
                 THEN /\ pc' = [pc EXCEPT ![t] = "idle"]
                      /\ UNCHANGED <<avail, held, owner, depth, ret>>
                 ELSE /\ GiveUp(t, held[t])
                      /\ DrainThen(t, "idle")
       [] OTHER ->
            \* "broadcast": notified with no permit, so nothing to pass on.
            /\ node' = [node EXCEPT ![t] = IF InFifo(t) THEN "broadcast" ELSE "none"]
            /\ DrainThen(t, "idle")
            /\ UNCHANGED <<avail, held, owner, depth>>
  /\ UNCHANGED <<waiters, fifo, token, hand, target, bgen, bwake>>

----------------------------------------------------------------------------
\* Releasing, moving owned guards, notifying.

\* A guard is dropped. A Semaphore returns all the task's permits; a
\* ReentrantMutex drops one guard and frees the lock at depth 0. Whatever
\* frees permits drains, so the next waiter is handed them.
Release(t) ==
  /\ pc[t] \in {"holding", "owned"}
  /\ Kind # "Notify"
  /\ LET n     == IF Kind = "Reentrant" THEN 1 ELSE held[t]
         rest  == held[t] - n
         freed == Kind = "Semaphore" \/ depth - n = 0 \/ Mutant = "NoDepth"
     IN /\ GiveUp(t, n)
        /\ line' = IF rest = 0 THEN Remove(line, t) ELSE line
        /\ IF freed
             THEN DrainThen(t, IF rest > 0 THEN "holding" ELSE "idle")
             ELSE /\ pc' = [pc EXCEPT ![t] = IF rest > 0 THEN "holding" ELSE "idle"]
                  /\ UNCHANGED ret
  /\ UNCHANGED <<waiters, fifo, node, woken, token, hand, target, bgen, gen, bwake>>

\* An owned guard (`lock_owned`, `acquire_owned`) moves from task t to an
\* idle task u, which will drop it. The permits go with the guard. The
\* receiving task only drops it ("owned"), so a guard cannot circle forever
\* without a release.
Give(t, u) ==
  /\ Kind = "Semaphore" /\ Owned
  /\ t # u
  /\ pc[t] = "holding"
  /\ pc[u] = "idle"
  /\ held' = [held EXCEPT ![t] = 0, ![u] = held[t]]
  /\ pc' = [pc EXCEPT ![t] = "idle", ![u] = "owned"]
  /\ line' = [i \in DOMAIN line |-> IF line[i] = t THEN u ELSE line[i]]
  /\ UNCHANGED <<avail, waiters, fifo, node, woken, owner, depth, token, hand,
                 target, ret, bgen, gen, bwake>>

\* Notify::notify_one: store the permit, then drain, so a waiting task is
\* handed it. A notify_one that finds a permit already stored changes no
\* word and returns at once (notifications coalesce): the call that stored
\* that permit drains for it, so this one is not a step.
NotifyOne(t) ==
  /\ Kind = "Notify"
  /\ t \in Notifiers
  /\ pc[t] = "idle"
  /\ avail = 0
  /\ avail' = 1
  /\ DrainThen(t, "idle")
  /\ UNCHANGED <<waiters, fifo, node, woken, held, owner, depth, token, hand,
                 target, line, bgen, gen, bwake>>

\* Notify::notify_waiters: bump the generation, and CAS every node waiting
\* in the queue to "broadcast". It stores no permit. The broadcaster then
\* wakes each of them, then drains to drop the stale nodes.
NotifyWaiters(t) ==
  /\ Kind = "Notify"
  /\ t \in Notifiers
  /\ pc[t] = "idle"
  /\ bgen < MaxBcast
  /\ LET live == {u \in Tasks : InFifo(u) /\ node[u] = "waiting"}
     IN /\ bgen' = bgen + 1
        /\ node' = [u \in Tasks |-> IF u \in live THEN "broadcast" ELSE node[u]]
        /\ bwake' = [bwake EXCEPT ![t] = live]
        /\ line' = SelectSeq(line, LAMBDA u : u \notin live)
  /\ pc' = [pc EXCEPT ![t] = "bwake"]
  /\ UNCHANGED <<avail, waiters, fifo, woken, held, owner, depth, token, hand,
                 target, ret, gen>>

\* The broadcaster wakes the waiters it notified, one per step; then it
\* drains.
BWake(t) ==
  /\ pc[t] = "bwake"
  /\ IF bwake[t] = {}
       THEN /\ DrainThen(t, "idle")
            /\ UNCHANGED <<woken, bwake>>
       ELSE \E u \in bwake[t] :
              /\ woken' = [woken EXCEPT ![u] = TRUE]
              /\ bwake' = [bwake EXCEPT ![t] = @ \ {u}]
              /\ UNCHANGED <<pc, ret>>
  /\ UNCHANGED <<avail, waiters, fifo, node, held, owner, depth, token, hand,
                 target, line, bgen, gen>>

----------------------------------------------------------------------------
\* The drain: the only code that pops the queue and hands permits over.

\* Take the drain token if it is free. If another task holds it, leave:
\* that task re-checks for work as it lets the token go.
DTake(t) ==
  /\ pc[t] = "dtake"
  /\ IF token = NoTask
       THEN /\ token' = t
            /\ pc' = [pc EXCEPT ![t] = "dloop"]
            /\ UNCHANGED ret
       ELSE /\ Resume(t)
            /\ UNCHANGED token
  /\ UNCHANGED <<avail, waiters, fifo, node, woken, held, owner, depth, hand,
                 target, line, bgen, gen, bwake>>

\* Holding the token, look at the head. A stale node (cancelled, broadcast,
\* or already finished) is popped. A waiting node the free permits satisfy
\* has its permits debited into `hand`. Otherwise there is nothing to do.
\* Mutant WakeBeforeHandoff: it goes to wake the head before handing over.
DLoop(t) ==
  /\ pc[t] = "dloop"
  /\ IF fifo = <<>>
       THEN /\ pc' = [pc EXCEPT ![t] = "dfree"]
            /\ UNCHANGED <<avail, waiters, fifo, node, hand, target>>
       ELSE LET h == Head(fifo) IN
            IF node[h] # "waiting"
              THEN \* A stale node: pop it. A broadcast node its future still
                   \* waits on keeps its mark; otherwise it is forgotten.
                   /\ fifo' = Tail(fifo)
                   /\ waiters' = waiters - 1
                   /\ node' = [node EXCEPT ![h] =
                                 IF node[h] = "broadcast" /\ Waits(h) THEN "broadcast" ELSE "none"]
                   /\ UNCHANGED <<pc, avail, hand, target>>
              ELSE IF avail >= Need[h]
                THEN /\ avail' = avail - Need[h]
                     /\ hand' = [hand EXCEPT ![t] = Need[h]]
                     /\ target' = [target EXCEPT ![t] = h]
                     /\ pc' = [pc EXCEPT ![t] =
                                 IF Mutant = "WakeBeforeHandoff" THEN "dwake" ELSE "dgrant"]
                     /\ UNCHANGED <<waiters, fifo, node>>
                ELSE /\ pc' = [pc EXCEPT ![t] = "dfree"]
                     /\ UNCHANGED <<avail, waiters, fifo, node, hand, target>>
  /\ UNCHANGED <<woken, held, owner, depth, token, ret, line, bgen, gen, bwake>>

\* The handoff: CAS the target's node from "waiting" to "granted". On
\* success the debited permits become the waiter's (Reentrant: the lock
\* becomes its Owner's, depth 1) and its node is popped. The waiter owns
\* them before anyone wakes it. If a cancel or a broadcast won the CAS, the
\* permits go back to `avail` and the loop drops the stale node.
DGrant(t) ==
  /\ pc[t] = "dgrant"
  /\ LET h == target[t] IN
     IF node[h] = "waiting"
       THEN /\ node' = [node EXCEPT ![h] = "granted"]
            /\ held' = [held EXCEPT ![h] = hand[t]]
            /\ owner' = IF Kind = "Reentrant" THEN Owner[h] ELSE owner
            /\ depth' = IF Kind = "Reentrant" THEN 1 ELSE depth
            /\ hand' = [hand EXCEPT ![t] = 0]
            /\ fifo' = Tail(fifo)
            /\ waiters' = waiters - 1
            /\ IF Mutant = "WakeBeforeHandoff"
                 THEN /\ pc' = [pc EXCEPT ![t] = "dloop"]
                      /\ target' = [target EXCEPT ![t] = NoTask]
                 ELSE /\ pc' = [pc EXCEPT ![t] = "dwake"]
                      /\ UNCHANGED target
            /\ UNCHANGED avail
       ELSE /\ avail' = IF Kind = "Notify" THEN Min(1, avail + hand[t]) ELSE avail + hand[t]
            /\ hand' = [hand EXCEPT ![t] = 0]
            /\ target' = [target EXCEPT ![t] = NoTask]
            /\ pc' = [pc EXCEPT ![t] = "dloop"]
            /\ UNCHANGED <<node, held, owner, depth, fifo, waiters>>
  /\ UNCHANGED <<woken, token, ret, line, bgen, gen, bwake>>

\* Waker::wake for the waiter just handed ownership.
DWake(t) ==
  /\ pc[t] = "dwake"
  /\ woken' = [woken EXCEPT ![target[t]] = TRUE]
  /\ IF Mutant = "WakeBeforeHandoff"
       THEN pc' = [pc EXCEPT ![t] = "dgrant"] /\ UNCHANGED target
       ELSE /\ pc' = [pc EXCEPT ![t] = "dloop"]
            /\ target' = [target EXCEPT ![t] = NoTask]
  /\ UNCHANGED <<avail, waiters, fifo, node, held, owner, depth, token, hand,
                 ret, line, bgen, gen, bwake>>

\* Let the token go and look again: work that arrived while this task held
\* the token, from a task that found the token taken and left, is picked up
\* here. Mutant DrainNoRecheck: leave without looking.
DFree(t) ==
  /\ pc[t] = "dfree"
  /\ token' = NoTask
  /\ IF Work /\ Mutant # "DrainNoRecheck"
       THEN pc' = [pc EXCEPT ![t] = "dtake"] /\ UNCHANGED ret
       ELSE Resume(t)
  /\ UNCHANGED <<avail, waiters, fifo, node, woken, held, owner, depth, hand,
                 target, line, bgen, gen, bwake>>

----------------------------------------------------------------------------
\* The specification.

\* The start: every permit free (Notify: none stored), nobody waiting.
Init ==
  /\ avail   = IF Kind = "Notify" THEN 0 ELSE Permits
  /\ waiters = 0
  /\ fifo    = <<>>
  /\ node    = [t \in Tasks |-> "none"]
  /\ woken   = [t \in Tasks |-> FALSE]
  /\ held    = [t \in Tasks |-> 0]
  /\ owner   = NoOwner
  /\ depth   = 0
  /\ token   = NoTask
  /\ hand    = [t \in Tasks |-> 0]
  /\ target  = [t \in Tasks |-> NoTask]
  /\ ret     = [t \in Tasks |-> "idle"]
  /\ pc      = [t \in Tasks |-> "idle"]
  /\ line    = <<>>
  /\ bgen    = 0
  /\ gen     = [t \in Tasks |-> 0]
  /\ bwake   = [t \in Tasks |-> {}]

\* The steps a task takes on its own once started: they must happen.
Internal(t) ==
  \/ Push(t) \/ Poll(t) \/ BWake(t)
  \/ DTake(t) \/ DLoop(t) \/ DGrant(t) \/ DWake(t) \/ DFree(t)

\* Every step the system can take.
Next ==
  \E t \in Tasks :
    \/ Acquire(t) \/ TryAcquire(t) \/ Reenter(t) \/ Cancel(t) \/ Release(t)
    \/ NotifyOne(t) \/ NotifyWaiters(t) \/ Internal(t)
    \/ \E u \in Tasks : Give(t, u)

\* Fairness: a task in the middle of an operation finishes it, a woken
\* future is polled, and a holder eventually drops its guard. Starting an
\* acquire, cancelling, re-entering, moving a guard and notifying are the
\* caller's choices, so they need not happen.
Fairness == \A t \in Tasks : WF_vars(Internal(t)) /\ WF_vars(Release(t))

\* Every behaviour: start in Init, take Next steps or stutter, fairly.
Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ avail \in 0..Permits
  /\ waiters \in 0..Cardinality(Tasks)
  /\ \A i \in 1..Len(fifo) : fifo[i] \in Tasks
  /\ node \in [Tasks -> NodeStates]
  /\ woken \in [Tasks -> BOOLEAN]
  /\ held \in [Tasks -> 0..(Permits * MaxDepth)]
  /\ owner \in Owners \cup {NoOwner}
  /\ token \in Tasks \cup {NoTask}
  /\ hand \in [Tasks -> 0..Permits]
  /\ target \in [Tasks -> Tasks \cup {NoTask}]
  /\ pc \in [Tasks -> PCs]
  /\ bgen \in 0..MaxBcast

\* `waiters` counts exactly the registered tasks not yet pushed plus the
\* nodes in the queue, so the fast path is shut whenever anyone waits.
WaitersCounted == waiters = Cardinality({t \in Tasks : pc[t] = "push"}) + Len(fifo)

\* Only the token holder is inside the drain, and a drainer granting a head
\* still has it at the head of the queue.
DrainExclusive ==
  /\ \A t \in Tasks : pc[t] \in {"dloop", "dgrant", "dwake", "dfree"} <=> token = t
  /\ \A t \in Tasks : pc[t] = "dgrant" => fifo # <<>> /\ Head(fifo) = target[t]

\* Every permit is somewhere: free, held by a task, or in a drainer's hand.
\* Reentrant: the one lock is free, owned, or in a drainer's hand. (Notify
\* creates and consumes permits, so it has no such sum.)
PermitsConserved ==
  /\ Kind = "Semaphore" =>
       avail + SumOf(held, Tasks) + SumOf(hand, Tasks) = Permits
  /\ Kind = "Reentrant" =>
       avail + (IF owner # NoOwner THEN 1 ELSE 0) + SumOf(hand, Tasks) = 1

\* MUTUAL EXCLUSION. A Semaphore never has more permits out than it has (a
\* Mutex: at most one holder). A ReentrantMutex's guards are all held by
\* tasks of the one Owner holding it. Lean: at_most_one_owner, permits_bounded.
MutualExclusion ==
  /\ Kind = "Semaphore" => SumOf(held, Tasks) <= Permits
  /\ Kind = "Reentrant" => \A t \in Tasks : held[t] > 0 => Owner[t] = owner

\* REENTRANCY DEPTH. The depth is exactly the guards out, and the lock has
\* an owner exactly when the depth is not 0: it returns to 0 exactly when
\* the last guard drops, and only then is the lock free.
ReentrancyDepth ==
  Kind = "Reentrant" =>
    /\ depth = SumOf(held, Tasks)
    /\ (owner = NoOwner <=> depth = 0)

\* FIFO HANDOFF, no barging. No task holds permits that it got after a task
\* still waiting got in line: whoever got in line first is served first.
\* Lean: fifo_served.
FifoHandoff ==
  \A i, j \in 1..Len(line) :
    i < j /\ node[line[i]] = "waiting" => held[line[j]] = 0

\* A parked future that owns what it waits for has been woken, or the task
\* that handed it over is about to wake it. Handoff comes before the wake,
\* so the wake always finds ownership. Lean: handed_holds.
GrantedWoken ==
  \A t \in Tasks :
    pc[t] = "parked" /\ node[t] \in {"granted", "broadcast"} =>
      \/ woken[t]
      \/ \E d \in Tasks : (pc[d] = "dwake" /\ target[d] = t) \/ (pc[d] = "bwake" /\ t \in bwake[d])

\* Every task is between operations: nobody is inside a step sequence that
\* would still hand something over.
Quiescent == \A t \in Tasks : pc[t] \in {"idle", "holding", "owned", "parked"}

\* A live waiter is stuck: every node ahead of it is stale and the free
\* permits satisfy it, so a drain would serve it, yet nobody is draining.
Stranded ==
  \E i \in 1..Len(fifo) :
    /\ node[fifo[i]] = "waiting"
    /\ \A j \in 1..(i - 1) : node[fifo[j]] # "waiting"
    /\ avail >= Need[fifo[i]]

\* Notify: a waiting node registered before a broadcast was not notified.
MissedBroadcast == \E t \in Tasks : node[t] = "waiting" /\ gen[t] < bgen

\* NO LOST WAKEUP. Ownership handed over is followed by a wake; no waiter
\* misses a broadcast; and once every task is between operations, no
\* waiter waits for permits that are free. Lean: no_stranded_waiter,
\* handed_holds.
NoLostWakeup == GrantedWoken /\ ~MissedBroadcast /\ (Quiescent => ~Stranded)

\* CANCELLATION PASSES ON. A task that is idle holds nothing: a waiter
\* dropped after ownership reached it gave that ownership up.
CancelPassesOn == \A t \in Tasks : pc[t] = "idle" => held[t] = 0

----------------------------------------------------------------------------
\* Liveness.

\* The liveness properties are checked for the tasks in Watched only. Tasks
\* with the same Need, Owner role and notifier role are interchangeable:
\* renaming them maps every behaviour to a behaviour, a starving one to a
\* starving one. So one task of each role (the cfg's Watched) covers all,
\* at a fraction of TLC's liveness cost, which grows with each property
\* branch.

\* Every parked waiter stops waiting: it is served, unless it cancels.
EveryWaiterServed == \A t \in Watched : (pc[t] = "parked") ~> (pc[t] # "parked")

\* Reentrant: no Owner keeps the lock forever. A task of the owning Owner
\* may re-enter while another drops its guard, so an owner can hold the lock
\* as long as it likes; liveness is promised for owners that let go.
OwnersLetGo == \A o \in Owners : []<>(owner # o)

\* Reentrant: if no owner holds the lock forever, every waiter is served.
ReentrantServed == OwnersLetGo => EveryWaiterServed

\* Notify: a waiter can wait forever if nobody notifies; one that was
\* handed a notification completes.
NotifiedCompletes ==
  \A t \in Watched :
    (pc[t] = "parked" /\ node[t] \in {"granted", "broadcast"}) ~> (pc[t] # "parked")

====
