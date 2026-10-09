---- MODULE SyncNotify ----
\* regolith::sync::Notify (plan 4.11): notify_one stores one permit,
\* notified() consumes one, notify_waiters wakes every waiter registered
\* before it. The waiter queue hands a notification to the oldest waiter
\* before waking it.
\*
\* WHY NOTIFY KEEPS FIFO HANDOFF. D49 replaced strict handoff with barging
\* for the lock-like primitives (Sync.tla): handing a lock to a suspended
\* task stalls every other acquirer until that task runs. A notification is
\* addressed to a waiter, holds nothing other tasks need, and the D49 note
\* keeps Notify's semantics; so its queue stays FIFO with handoff. This model
\* is the one that checked Notify before D49, with the lock-only parts
\* (Semaphore, ReentrantMutex, owned guards) moved to the barging Sync.tla.
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/SyncFifo.lean (the
\* FIFO waiter queue with handoff before wake, one permit per request):
\*   step_inv, reachable_inv      the queue's invariant holds in every state
\*   fifo_served, served_in_order no request is served ahead of one that
\*                                entered before it and still waits
\*                                (FifoHandoff here)
\*   no_stranded_waiter           a waiter never waits beside a stored permit
\*                                (NoLostWakeup's Stranded here)
\*   handed_holds,                a waiter is woken only once it holds its
\*   no_lost_handoff              notification (GrantedWoken here)
\*   position_never_grows,        a waiter's place only moves forward, one
\*   handoff_advances             place per handoff
\*   wake_before_handoff_strands, cancel_without_pass_on_strands
\*                                the RED cases, as counterexamples
\* TLC checks the concurrent protocol here, step by atomic step.
\*
\* THE PROTOCOL MODELLED, one atomic step per word-sized CAS or queue
\* operation:
\*   - one state word holds `avail` (the stored permit, 0 or 1), `waiters`
\*     (registered waiters not yet popped) and `bgen` (the broadcast
\*     generation). notified() consumes a stored permit at once only when
\*     nobody is registered;
\*   - a waiter registers (waiters + 1, recording bgen), pushes its node with
\*     its Waker, then drains: the re-check after the push;
\*   - a node's state is CAS'd from "waiting" to exactly one of "granted"
\*     (handed the permit), "cancelled" or "broadcast";
\*   - the drain token: only its holder pops the queue and hands permits on.
\*     Nobody waits for it: a task that finds it taken leaves, and the holder
\*     re-checks as it lets go;
\*   - notify_waiters bumps bgen and CASes every waiting node to "broadcast"
\*     (one step here); a waiter registered under an older generation that
\*     pushes afterwards notifies itself at the push.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - A task has one request at a time and may not register again while its
\*     previous node is still queued: two nodes of one task behave as two
\*     tasks.
\*   - A cancel is one step; a drainer's pop and its `waiters` decrement are
\*     one step; letting the token go and the re-check are one step. Each
\*     split only adds redundant or conservative interleavings.
\*   - Memory ordering is loom's (plan 7.1).
\*
\* CONFIGURATIONS.
\*   MC_SyncNotify_Green              task 3 notifies (notify_one and two
\*                                    notify_waiters), tasks 1 and 2 wait and
\*                                    cancel: every invariant, and a notified
\*                                    waiter completes.
\*   MC_SyncNotify_Red_WakeBeforeHandoff  wake, then hand: NoLostWakeup.
\*   MC_SyncNotify_Red_CancelNoPassOn a dropped waiter keeps the notification
\*                                    handed to it: CancelPassesOn.
\*   MC_SyncNotify_Red_NoRecheck      park right after the push: NoLostWakeup.
\*   MC_SyncNotify_Red_NoGenCheck     a waiter that pushed after a broadcast
\*                                    misses it: NoLostWakeup.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Tasks,     \* the tasks using the Notify: positive naturals
  Notifiers, \* the tasks that notify; the others wait on notified()
  Watched,   \* the tasks whose liveness is checked: one per role
  MaxBcast,  \* the most notify_waiters calls in one behaviour
  Mutant     \* "none" for the design, or the name of one defect

\* The value "no task", for the drain token and a drainer's target.
NoTask == 0

ASSUME Tasks \subseteq Nat \ {0} /\ Notifiers \subseteq Tasks /\ Watched \subseteq Tasks
ASSUME MaxBcast \in Nat
ASSUME Mutant \in {"none", "WakeBeforeHandoff", "CancelNoPassOn", "NoRecheck", "NoGenCheck"}

VARIABLES
  avail,    \* 1 when a permit is stored, else 0
  waiters,  \* registered waiters not yet popped, in the same word as avail
  fifo,     \* the waiter queue: tasks, oldest first (each task's one node)
  node,     \* [Tasks -> state of the task's node]
  woken,    \* [Tasks -> BOOLEAN]: Waker::wake ran since it was registered
  held,     \* [Tasks -> 0..1]: a notification handed to the task, not consumed
  token,    \* the drain token: the task holding it, or NoTask
  hand,     \* [Tasks -> 0..1]: the permit a drainer debited for the head
  target,   \* [Tasks -> Tasks \cup {NoTask}]: the head a drainer grants or wakes
  ret,      \* [Tasks -> pc]: where a task resumes once its drain ends
  pc,       \* [Tasks -> pc]: where each task is in its operation
  line,     \* ghost: tasks with a live request, in the order they entered
  bgen,     \* the broadcast generation, in the state word
  gen,      \* [Tasks -> Nat]: the generation a waiter registered under
  bwake     \* [Tasks -> SUBSET Tasks]: waiters a broadcaster has yet to wake

\* Every variable, so a step that changes none of them is a stutter.
vars == <<avail, waiters, fifo, node, woken, held, token, hand, target, ret, pc,
          line, bgen, gen, bwake>>

\* The steps of the drain, where a task may hold the token.
DrainPCs == {"dtake", "dloop", "dgrant", "dwake", "dfree"}

\* The places a task can be: "idle", "push" (registered, about to push its
\* node), "parked" (its future returned Pending), "bwake" (a broadcaster
\* waking waiters), or one of the drain steps.
PCs == {"idle", "push", "parked", "bwake"} \cup DrainPCs

\* The states of a node. "none": no node, or one nobody looks at any more.
NodeStates == {"none", "waiting", "granted", "cancelled", "broadcast"}

----------------------------------------------------------------------------
\* Helpers.

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
\* waiting node and a stored permit.
Work == fifo # <<>> /\ (node[Head(fifo)] # "waiting" \/ avail >= 1)

\* Task t goes on to drain (try the token), and resumes at `r` afterwards.
DrainThen(t, r) ==
  /\ pc' = [pc EXCEPT ![t] = "dtake"]
  /\ ret' = [ret EXCEPT ![t] = r]

\* Task t's drain is over: it resumes where it was going.
Resume(t) ==
  /\ pc' = [pc EXCEPT ![t] = ret[t]]
  /\ ret' = [ret EXCEPT ![t] = "idle"]

----------------------------------------------------------------------------
\* Waiting.

\* notified(), first poll. One CAS on the state word: consume a stored
\* permit if nobody is registered; otherwise register, recording bgen.
Acquire(t) ==
  /\ pc[t] = "idle"
  /\ t \notin Notifiers
  /\ ~InFifo(t)
  /\ IF waiters = 0 /\ avail >= 1
       THEN /\ avail' = avail - 1
            /\ UNCHANGED <<waiters, gen, pc>>
       ELSE /\ waiters' = waiters + 1
            /\ gen' = [gen EXCEPT ![t] = bgen]
            /\ pc' = [pc EXCEPT ![t] = "push"]
            /\ UNCHANGED avail
  /\ UNCHANGED <<fifo, node, woken, held, token, hand, target, ret, line, bgen, bwake>>

\* The registered waiter pushes its node, Waker inside, then drains (the
\* re-check). A broadcast that ran since registration could not see this
\* node, so the waiter notifies itself. Mutant NoRecheck: it parks at once.
\* Mutant NoGenCheck: it skips the generation check.
Push(t) ==
  /\ pc[t] = "push"
  /\ fifo' = Append(fifo, t)
  /\ line' = Append(line, t)
  /\ IF gen[t] < bgen /\ Mutant # "NoGenCheck"
       THEN /\ node' = [node EXCEPT ![t] = "broadcast"]
            /\ woken' = [woken EXCEPT ![t] = TRUE]
            /\ DrainThen(t, "parked")
       ELSE /\ node' = [node EXCEPT ![t] = "waiting"]
            /\ woken' = [woken EXCEPT ![t] = FALSE]
            /\ IF Mutant = "NoRecheck"
                 THEN pc' = [pc EXCEPT ![t] = "parked"] /\ UNCHANGED ret
                 ELSE DrainThen(t, "parked")
  /\ UNCHANGED <<avail, waiters, held, token, hand, target, bgen, gen, bwake>>

\* The executor polls a woken future. Granted or broadcast: notified()
\* completes, consuming the handed permit if any. Otherwise it registers its
\* waker again.
Poll(t) ==
  /\ pc[t] = "parked"
  /\ woken[t]
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  /\ IF node[t] \in {"granted", "broadcast"}
       THEN \* A broadcast node still queued stays marked stale for the
            \* drainer; any other finished node is forgotten.
            /\ node' = [node EXCEPT ![t] = IF InFifo(t) THEN node[t] ELSE "none"]
            /\ gen' = [gen EXCEPT ![t] = 0]
            /\ pc' = [pc EXCEPT ![t] = "idle"]
            /\ held' = [held EXCEPT ![t] = 0]
            /\ line' = Remove(line, t)
       ELSE UNCHANGED <<node, gen, pc, held, line>>
  /\ UNCHANGED <<avail, waiters, fifo, token, hand, target, ret, bgen, bwake>>

\* The pending future is dropped. A waiting node is CAS'd to "cancelled". A
\* granted one passes the permit on: stored again, then a drain hands it to
\* the next waiter. Either way it drains. Mutant CancelNoPassOn: a granted
\* waiter keeps the permit.
Cancel(t) ==
  /\ pc[t] = "parked"
  /\ line' = Remove(line, t)
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  /\ gen' = [gen EXCEPT ![t] = 0]
  /\ CASE node[t] = "waiting" ->
            /\ node' = [node EXCEPT ![t] = "cancelled"]
            /\ DrainThen(t, "idle")
            /\ UNCHANGED <<avail, held>>
       [] node[t] = "granted" ->
            /\ node' = [node EXCEPT ![t] = "none"]
            /\ IF Mutant = "CancelNoPassOn"
                 THEN /\ pc' = [pc EXCEPT ![t] = "idle"]
                      /\ UNCHANGED <<avail, held, ret>>
                 ELSE /\ avail' = Min(1, avail + held[t])
                      /\ held' = [held EXCEPT ![t] = 0]
                      /\ DrainThen(t, "idle")
       [] OTHER ->
            \* "broadcast": notified with no permit, so nothing to pass on.
            /\ node' = [node EXCEPT ![t] = IF InFifo(t) THEN "broadcast" ELSE "none"]
            /\ DrainThen(t, "idle")
            /\ UNCHANGED <<avail, held>>
  /\ UNCHANGED <<waiters, fifo, token, hand, target, bgen, bwake>>

----------------------------------------------------------------------------
\* Notifying.

\* notify_one: store the permit, then drain, so a waiting task is handed
\* it. One that finds a permit stored changes no word (notifications
\* coalesce); the call that stored it drains for it, so it is not a step.
NotifyOne(t) ==
  /\ t \in Notifiers
  /\ pc[t] = "idle"
  /\ avail = 0
  /\ avail' = 1
  /\ DrainThen(t, "idle")
  /\ UNCHANGED <<waiters, fifo, node, woken, held, token, hand, target, line, bgen, gen, bwake>>

\* notify_waiters: bump the generation and CAS every waiting node to
\* "broadcast", storing nothing; then wake each of them and drain.
NotifyWaiters(t) ==
  /\ t \in Notifiers
  /\ pc[t] = "idle"
  /\ bgen < MaxBcast
  /\ LET live == {u \in Tasks : InFifo(u) /\ node[u] = "waiting"}
     IN /\ bgen' = bgen + 1
        /\ node' = [u \in Tasks |-> IF u \in live THEN "broadcast" ELSE node[u]]
        /\ bwake' = [bwake EXCEPT ![t] = live]
        /\ line' = SelectSeq(line, LAMBDA u : u \notin live)
  /\ pc' = [pc EXCEPT ![t] = "bwake"]
  /\ UNCHANGED <<avail, waiters, fifo, woken, held, token, hand, target, ret, gen>>

\* The broadcaster wakes the waiters it notified, one per step; then drains.
BWake(t) ==
  /\ pc[t] = "bwake"
  /\ IF bwake[t] = {}
       THEN /\ DrainThen(t, "idle")
            /\ UNCHANGED <<woken, bwake>>
       ELSE \E u \in bwake[t] :
              /\ woken' = [woken EXCEPT ![u] = TRUE]
              /\ bwake' = [bwake EXCEPT ![t] = @ \ {u}]
              /\ UNCHANGED <<pc, ret>>
  /\ UNCHANGED <<avail, waiters, fifo, node, held, token, hand, target, line, bgen, gen>>

----------------------------------------------------------------------------
\* The drain: the only code that pops the queue and hands permits over.

\* Take the drain token if it is free; if another task holds it, leave.
DTake(t) ==
  /\ pc[t] = "dtake"
  /\ IF token = NoTask
       THEN /\ token' = t
            /\ pc' = [pc EXCEPT ![t] = "dloop"]
            /\ UNCHANGED ret
       ELSE /\ Resume(t)
            /\ UNCHANGED token
  /\ UNCHANGED <<avail, waiters, fifo, node, woken, held, hand, target, line, bgen, gen, bwake>>

\* Holding the token, look at the head: pop a stale node; debit the stored
\* permit for a waiting head; otherwise stop. Mutant WakeBeforeHandoff: wake
\* the head before handing it anything.
DLoop(t) ==
  /\ pc[t] = "dloop"
  /\ IF fifo = <<>>
       THEN /\ pc' = [pc EXCEPT ![t] = "dfree"]
            /\ UNCHANGED <<avail, waiters, fifo, node, hand, target>>
       ELSE LET h == Head(fifo) IN
            IF node[h] # "waiting"
              THEN /\ fifo' = Tail(fifo)
                   /\ waiters' = waiters - 1
                   /\ node' = [node EXCEPT ![h] =
                                 IF node[h] = "broadcast" /\ Waits(h) THEN "broadcast" ELSE "none"]
                   /\ UNCHANGED <<pc, avail, hand, target>>
              ELSE IF avail >= 1
                THEN /\ avail' = avail - 1
                     /\ hand' = [hand EXCEPT ![t] = 1]
                     /\ target' = [target EXCEPT ![t] = h]
                     /\ pc' = [pc EXCEPT ![t] =
                                 IF Mutant = "WakeBeforeHandoff" THEN "dwake" ELSE "dgrant"]
                     /\ UNCHANGED <<waiters, fifo, node>>
                ELSE /\ pc' = [pc EXCEPT ![t] = "dfree"]
                     /\ UNCHANGED <<avail, waiters, fifo, node, hand, target>>
  /\ UNCHANGED <<woken, held, token, ret, line, bgen, gen, bwake>>

\* The handoff: CAS the target's node from "waiting" to "granted"; on
\* success it holds the permit and is popped, before anyone wakes it. If a
\* cancel or a broadcast won the CAS, the permit goes back.
DGrant(t) ==
  /\ pc[t] = "dgrant"
  /\ LET h == target[t] IN
     IF node[h] = "waiting"
       THEN /\ node' = [node EXCEPT ![h] = "granted"]
            /\ held' = [held EXCEPT ![h] = hand[t]]
            /\ hand' = [hand EXCEPT ![t] = 0]
            /\ fifo' = Tail(fifo)
            /\ waiters' = waiters - 1
            /\ IF Mutant = "WakeBeforeHandoff"
                 THEN /\ pc' = [pc EXCEPT ![t] = "dloop"]
                      /\ target' = [target EXCEPT ![t] = NoTask]
                 ELSE /\ pc' = [pc EXCEPT ![t] = "dwake"]
                      /\ UNCHANGED target
            /\ UNCHANGED avail
       ELSE /\ avail' = Min(1, avail + hand[t])
            /\ hand' = [hand EXCEPT ![t] = 0]
            /\ target' = [target EXCEPT ![t] = NoTask]
            /\ pc' = [pc EXCEPT ![t] = "dloop"]
            /\ UNCHANGED <<node, held, fifo, waiters>>
  /\ UNCHANGED <<woken, token, ret, line, bgen, gen, bwake>>

\* Waker::wake for the waiter just handed the permit.
DWake(t) ==
  /\ pc[t] = "dwake"
  /\ woken' = [woken EXCEPT ![target[t]] = TRUE]
  /\ IF Mutant = "WakeBeforeHandoff"
       THEN pc' = [pc EXCEPT ![t] = "dgrant"] /\ UNCHANGED target
       ELSE /\ pc' = [pc EXCEPT ![t] = "dloop"]
            /\ target' = [target EXCEPT ![t] = NoTask]
  /\ UNCHANGED <<avail, waiters, fifo, node, held, token, hand, ret, line, bgen, gen, bwake>>

\* Let the token go and look again: work left behind by a task that found
\* the token taken is picked up here.
DFree(t) ==
  /\ pc[t] = "dfree"
  /\ token' = NoTask
  /\ IF Work
       THEN pc' = [pc EXCEPT ![t] = "dtake"] /\ UNCHANGED ret
       ELSE Resume(t)
  /\ UNCHANGED <<avail, waiters, fifo, node, woken, held, hand, target, line, bgen, gen, bwake>>

----------------------------------------------------------------------------
\* The specification.

\* The start: no permit stored, nobody waiting.
Init ==
  /\ avail   = 0
  /\ waiters = 0
  /\ fifo    = <<>>
  /\ node    = [t \in Tasks |-> "none"]
  /\ woken   = [t \in Tasks |-> FALSE]
  /\ held    = [t \in Tasks |-> 0]
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
    Acquire(t) \/ Cancel(t) \/ NotifyOne(t) \/ NotifyWaiters(t) \/ Internal(t)

\* Fairness: a started operation finishes and a woken future is polled.
\* Waiting, cancelling and notifying are the caller's choices.
Fairness == \A t \in Tasks : WF_vars(Internal(t))

\* Every behaviour: start in Init, take Next steps or stutter, fairly.
Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ avail \in 0..1
  /\ waiters \in 0..Cardinality(Tasks)
  /\ \A i \in 1..Len(fifo) : fifo[i] \in Tasks
  /\ node \in [Tasks -> NodeStates]
  /\ woken \in [Tasks -> BOOLEAN]
  /\ held \in [Tasks -> 0..1]
  /\ token \in Tasks \cup {NoTask}
  /\ hand \in [Tasks -> 0..1]
  /\ pc \in [Tasks -> PCs]
  /\ bgen \in 0..MaxBcast

\* `waiters` counts the registered tasks not yet pushed plus the queued
\* nodes, so the fast path is shut whenever anyone waits.
WaitersCounted == waiters = Cardinality({t \in Tasks : pc[t] = "push"}) + Len(fifo)

\* Only the token holder is inside the drain, and a drainer granting a head
\* still has it at the head of the queue.
DrainExclusive ==
  /\ \A t \in Tasks : pc[t] \in {"dloop", "dgrant", "dwake", "dfree"} <=> token = t
  /\ \A t \in Tasks : pc[t] = "dgrant" => fifo # <<>> /\ Head(fifo) = target[t]

\* FIFO HANDOFF. No task holds a notification it got after a task still
\* waiting got in line. Lean: SyncFifo.fifo_served.
FifoHandoff ==
  \A i, j \in 1..Len(line) :
    i < j /\ node[line[i]] = "waiting" => held[line[j]] = 0

\* A parked future handed a notification has been woken, or is about to be.
\* Lean: SyncFifo.handed_holds.
GrantedWoken ==
  \A t \in Tasks :
    pc[t] = "parked" /\ node[t] \in {"granted", "broadcast"} =>
      \/ woken[t]
      \/ \E d \in Tasks : (pc[d] = "dwake" /\ target[d] = t) \/ (pc[d] = "bwake" /\ t \in bwake[d])

\* Every task is between operations.
Quiescent == \A t \in Tasks : pc[t] \in {"idle", "parked"}

\* A live waiter that a drain would serve (every node ahead of it stale, a
\* permit stored), with nobody draining.
Stranded ==
  \E i \in 1..Len(fifo) :
    /\ node[fifo[i]] = "waiting"
    /\ \A j \in 1..(i - 1) : node[fifo[j]] # "waiting"
    /\ avail >= 1

\* A waiting node registered before a broadcast was not notified.
MissedBroadcast == \E t \in Tasks : node[t] = "waiting" /\ gen[t] < bgen

\* NO LOST WAKEUP. A handed notification is followed by a wake, no waiter
\* misses a broadcast, and between operations nobody waits beside a stored
\* permit. Lean: SyncFifo.no_stranded_waiter.
NoLostWakeup == GrantedWoken /\ ~MissedBroadcast /\ (Quiescent => ~Stranded)

\* CANCELLATION PASSES ON. An idle task holds no notification.
CancelPassesOn == \A t \in Tasks : pc[t] = "idle" => held[t] = 0

----------------------------------------------------------------------------
\* Liveness.

\* A waiter handed a notification completes. (A waiter nobody notifies may
\* wait forever.) Checked for the tasks in Watched: waiters are
\* interchangeable, so one stands for all.
NotifiedCompletes ==
  \A t \in Watched :
    (pc[t] = "parked" /\ node[t] \in {"granted", "broadcast"}) ~> (pc[t] # "parked")

====
