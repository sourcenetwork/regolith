---- MODULE SyncLatch ----
\* regolith::sync::Event, Latch and Barrier (plan 4.11): one-shot and
\* reusable gates whose waiters all pass together.
\*
\* PROVED FOR EVERY SIZE in Lean: nothing specific to these gates. Their
\* waiter list is the registration-then-re-check pattern of SyncNotify.tla,
\* whose queue laws proofs/lean/Regolith/SyncFifo.lean proves (handed_holds,
\* no_stranded_waiter); the gate conditions are checked here only, for
\* three tasks. D49 changes nothing here: a gate releases every waiter at
\* once, so there is no handoff to replace with barging.
\*
\* THE DESIGN (plan 4.11).
\*   Event   `set`, `wait()`, `is_set`: a one-shot event. It is a Latch of
\*           count 1, with `set` its count_down; setting a set Event changes
\*           nothing.
\*   Latch   `count_down`, `wait()`, `is_set`: wait() completes once the
\*           count reaches 0, and stays complete.
\*   Barrier `wait()`: a fixed number of parties. The party whose arrival
\*           completes the generation releases every waiter of that
\*           generation, and the barrier is reused for the next one.
\*
\* THE PROTOCOL MODELLED. The count (Barrier: arrivals and the generation)
\* is one atomic word; waiters register in a lock-free list, here a set,
\* since a release wakes all of them. A waiter that finds the gate shut
\* pushes its node with its Waker, then re-checks the gate: a release that
\* ran between the first check and the push found no node to wake. The
\* release takes the whole list in one swap, then wakes each waiter in it.
\* A Barrier waiter checks its generation, never the arrival count, since
\* the count of the next generation starts while the woken waiters of the
\* last one have yet to be polled.
\*
\* DESIGN CHOICE WHERE THE PLAN IS SILENT, recorded in the final report.
\*   A Barrier arrival stays counted when its wait() future is dropped:
\*   withdrawing it would race with the arrival that completes the
\*   generation. The generation still completes once enough parties arrive;
\*   the dropped waiter is simply not woken.
\*
\* WHAT THE MODEL LEAVES OUT. Memory ordering (loom's, plan 7.1).
\*
\* CONFIGURATIONS.
\*   MC_SyncLatch_Green_Event        an Event set by any task.
\*   MC_SyncLatch_Green_Latch        a Latch of count 2.
\*   MC_SyncLatch_Green_Barrier      a Barrier of 2 parties, three tasks,
\*                                   two rounds each.
\*   MC_SyncLatch_Red_NoRecheck      an Event waiter parks without the
\*                                   re-check: NoLostWakeup.
\*   MC_SyncLatch_Red_CountCheck     a Barrier waiter checks the arrival
\*                                   count, not its generation: NoLostWakeup.

EXTENDS Naturals, FiniteSets

CONSTANTS
  Tasks,   \* the tasks using the gate: positive naturals
  Kind,    \* "Latch" (an Event is a Latch of count 1) or "Barrier"
  Count,   \* Latch: the initial count; Barrier: the parties per generation
  Rounds,  \* Barrier: the most times each task waits
  Mutant   \* "none", "NoRecheck" or "CountCheck"

ASSUME Kind \in {"Latch", "Barrier"}
ASSUME Count \in Nat \ {0} /\ Rounds \in Nat
ASSUME Mutant \in {"none", "NoRecheck", "CountCheck"}

VARIABLES
  count,    \* Latch: the count left
  arrived,  \* Barrier: parties arrived in the current generation
  bgen,     \* Barrier: the current generation
  mygen,    \* [Tasks -> Nat]: Barrier: the generation a task arrived in
  rounds,   \* [Tasks -> Nat]: Barrier: the waits a task has made
  q,        \* the registered waiters (their nodes in the waiter list)
  woken,    \* [Tasks -> BOOLEAN]: Waker::wake ran since it was registered
  towake,   \* [Tasks -> SUBSET Tasks]: waiters a releaser has yet to wake
  ret,      \* [Tasks -> pc]: where a releaser resumes once its wakes are done
  pc        \* [Tasks -> pc]

\* Every variable, so a step that changes none of them is a stutter.
vars == <<count, arrived, bgen, mygen, rounds, q, woken, towake, ret, pc>>

\* The places a task can be: "idle", "push" (found the gate shut, about to
\* push its node), "recheck" (pushed, about to look again), "parked" (its
\* future returned Pending), "wake" (a releaser waking waiters), "passed"
\* (its wait completed).
PCs == {"idle", "push", "recheck", "parked", "wake", "passed"}

\* Task t's gate is open. Latch: the count is 0. Barrier: its generation
\* was released (mutant CountCheck: the arrival count reads 0).
Open(t) ==
  IF Kind = "Latch" THEN count = 0
  ELSE IF Mutant = "CountCheck" THEN arrived = 0
  ELSE bgen # mygen[t]

\* Task t's gate really is open: the Latch count is 0, or t's Barrier
\* generation was released. (Open(t) is what a waiter checks, which a
\* mutant may get wrong; this is the truth it is judged against.)
Released(t) == IF Kind = "Latch" THEN count = 0 ELSE bgen > mygen[t]

\* Task t takes the whole waiter list and goes on to wake it, then resumes
\* at `next`.
ReleaseAll(t, next) ==
  /\ towake' = [towake EXCEPT ![t] = q]
  /\ q' = {}
  /\ pc' = [pc EXCEPT ![t] = "wake"]
  /\ ret' = [ret EXCEPT ![t] = next]

----------------------------------------------------------------------------
\* Actions.

\* Latch::count_down / Event::set. The count drops; the step that takes it
\* to 0 releases every waiter. On a count already at 0 it changes nothing,
\* so it is not a step.
CountDown(t) ==
  /\ Kind = "Latch"
  /\ pc[t] = "idle"
  /\ count > 0
  /\ count' = count - 1
  /\ IF count = 1
       THEN ReleaseAll(t, "idle")
       ELSE UNCHANGED <<q, towake, pc, ret>>
  /\ UNCHANGED <<arrived, bgen, mygen, rounds, woken>>

\* Latch::wait / Event::wait, first poll: complete at once if the count is
\* 0, otherwise go on to register.
LatchWait(t) ==
  /\ Kind = "Latch"
  /\ pc[t] = "idle"
  /\ pc' = [pc EXCEPT ![t] = IF count = 0 THEN "passed" ELSE "push"]
  /\ UNCHANGED <<count, arrived, bgen, mygen, rounds, q, woken, towake, ret>>

\* Barrier::wait, first poll: one atomic step on the arrival word. The
\* arrival that completes the generation starts the next one and releases
\* every waiter; any other goes on to register.
Arrive(t) ==
  /\ Kind = "Barrier"
  /\ pc[t] = "idle"
  /\ rounds[t] < Rounds
  /\ rounds' = [rounds EXCEPT ![t] = @ + 1]
  /\ mygen' = [mygen EXCEPT ![t] = bgen]
  /\ IF arrived + 1 = Count
       THEN /\ arrived' = 0
            /\ bgen' = bgen + 1
            /\ ReleaseAll(t, "passed")
       ELSE /\ arrived' = arrived + 1
            /\ pc' = [pc EXCEPT ![t] = "push"]
            /\ UNCHANGED <<bgen, q, towake, ret>>
  /\ UNCHANGED <<count, woken>>

\* The waiter pushes its node, Waker inside. Mutant NoRecheck: it parks at
\* once, without looking at the gate again.
Push(t) ==
  /\ pc[t] = "push"
  /\ q' = q \cup {t}
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  /\ pc' = [pc EXCEPT ![t] = IF Mutant = "NoRecheck" THEN "parked" ELSE "recheck"]
  /\ UNCHANGED <<count, arrived, bgen, mygen, rounds, towake, ret>>

\* The re-check after the push: if the gate opened meanwhile, complete
\* (taking the node back out); otherwise park.
Recheck(t) ==
  /\ pc[t] = "recheck"
  /\ IF Open(t)
       THEN pc' = [pc EXCEPT ![t] = "passed"] /\ q' = q \ {t}
       ELSE pc' = [pc EXCEPT ![t] = "parked"] /\ UNCHANGED q
  /\ UNCHANGED <<count, arrived, bgen, mygen, rounds, woken, towake, ret>>

\* The executor polls a woken future: if the gate is open it completes,
\* otherwise it registers its waker again (its node is gone with the swap,
\* so a wrong answer here strands it).
Poll(t) ==
  /\ pc[t] = "parked"
  /\ woken[t]
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  /\ pc' = [pc EXCEPT ![t] = IF Open(t) THEN "passed" ELSE "parked"]
  /\ UNCHANGED <<count, arrived, bgen, mygen, rounds, q, towake, ret>>

\* The pending wait is dropped: its node leaves the list. A Barrier
\* arrival stays counted.
Cancel(t) ==
  /\ pc[t] = "parked"
  /\ q' = q \ {t}
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  /\ pc' = [pc EXCEPT ![t] = "idle"]
  /\ UNCHANGED <<count, arrived, bgen, mygen, rounds, towake, ret>>

\* A releaser wakes the waiters it took, one per step.
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
  /\ UNCHANGED <<count, arrived, bgen, mygen, rounds, q>>

\* Barrier: a task that passed goes on to its next round.
Leave(t) ==
  /\ Kind = "Barrier"
  /\ pc[t] = "passed"
  /\ pc' = [pc EXCEPT ![t] = "idle"]
  /\ UNCHANGED <<count, arrived, bgen, mygen, rounds, q, woken, towake, ret>>

----------------------------------------------------------------------------
\* The specification.

\* The start: the full count, no arrival, nobody waiting.
Init ==
  /\ count = IF Kind = "Latch" THEN Count ELSE 0
  /\ arrived = 0
  /\ bgen = 0
  /\ mygen = [t \in Tasks |-> 0]
  /\ rounds = [t \in Tasks |-> 0]
  /\ q = {}
  /\ woken = [t \in Tasks |-> FALSE]
  /\ towake = [t \in Tasks |-> {}]
  /\ ret = [t \in Tasks |-> "idle"]
  /\ pc = [t \in Tasks |-> "idle"]

\* The steps a task takes on its own once started.
Internal(t) == Push(t) \/ Recheck(t) \/ Poll(t) \/ Wake(t)

\* Every step the system can take.
Next ==
  \E t \in Tasks :
    CountDown(t) \/ LatchWait(t) \/ Arrive(t) \/ Cancel(t) \/ Leave(t) \/ Internal(t)

\* Fairness: a started operation finishes and a woken future is polled.
\* Counting down, arriving, waiting and cancelling are the caller's choices.
Fairness == \A t \in Tasks : WF_vars(Internal(t))

\* Every behaviour: start in Init, take Next steps or stutter, fairly.
Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ count \in 0..Count
  /\ arrived \in 0..(Count - 1)
  /\ q \subseteq Tasks
  /\ pc \in [Tasks -> PCs]
  /\ woken \in [Tasks -> BOOLEAN]

\* THE GATE HOLDS. Latch: no wait completes while the count is above 0.
\* Barrier: no task passes a generation before that generation is
\* released, which only the arrival of its last party does.
GateHolds == \A t \in Tasks : pc[t] = "passed" => Released(t)

\* NO LOST WAKEUP. A parked waiter whose gate is open has been woken, or
\* its releaser is about to wake it.
NoLostWakeup ==
  \A t \in Tasks :
    (pc[t] = "parked" /\ Released(t)) => (woken[t] \/ \E d \in Tasks : t \in towake[d])

----------------------------------------------------------------------------
\* Liveness.

\* A parked waiter whose gate opened stops waiting.
ReleasedWaitersPass ==
  \A t \in Tasks : (pc[t] = "parked" /\ Released(t)) ~> (pc[t] # "parked")

====
