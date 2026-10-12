---- MODULE SyncOnce ----
\* ===========================================================================
\* THE STORY
\* ===========================================================================
\* A OnceCell is a box that is filled at most once and never changes after
\* that (src/sync/once_cell.rs; Lazy, src/sync/lazy.rs, is a OnceCell that
\* knows how to fill itself). Many tasks may try to fill it at the same
\* time. Whatever happens, they must all end up reading the same value.
\*
\* There are three ways to fill it: `set(v)` (here is the value), a racing
\* build (everybody who finds it empty builds a value, one wins), and an
\* async initializer (one task runs a future that produces the value while
\* the others wait for it).
\*
\* Tiny example of what can go wrong. Task 1 runs the async initializer and
\* task 2 waits for it. Task 1's future is dropped half way. If the cell
\* stays marked "being initialized", task 2 waits for ever for a value that
\* nobody is producing. So a dropped or failed initializer must put the
\* cell back to empty and wake the waiters, one of whom takes over.
\*
\* Second example: task 1 publishes value 1 and task 3 reads it. If task 2's
\* `set` could then simply store value 2, task 3 holds a value the cell no
\* longer has. So publishing is a compare-and-swap that succeeds only on a
\* cell that holds no value yet.
\*
\* What this model shows, for three tasks in every interleaving: at most one
\* value is ever published, everybody who got a value got that one, and no
\* waiter is left asleep.
\*
\* WHERE THE CODE DIFFERS FROM THIS MODEL (found while checking this file
\* against src/sync/once_cell.rs on this branch). The model keeps one state
\* word ("empty", "init", "ready") and its own waiter list. The code keeps
\* the value behind one atomic pointer (published by a single
\* compare-and-swap) and makes the async initializers take turns through a
\* one-permit semaphore (RawSemaphore, checked in Sync.tla): the waiters of
\* this model are tasks queued for that permit; a dropped or failed
\* initializer gives the permit back, which wakes the next one; and whoever
\* publishes adds a large number of permits, which lets every queued task
\* through to find the value. The promises checked here (published once,
\* readers agree, no lost wakeup) are the ones the code must keep; the
\* register, re-check and re-park steps below are the model's, not the
\* code's.
\*
\* The primitives covered: OnceCell and Lazy (plan 4.11): exactly one value
\* is published, whatever the initializers race, fail or get dropped.
\*
\* PROVED FOR EVERY SIZE in Lean: nothing specific to OnceCell. Its waiter
\* list is the registration-then-re-check pattern of SyncNotify.tla, whose
\* queue laws proofs/lean/Regolith/SyncFifo.lean proves; the publish-once
\* property is checked here only, for three tasks.
\*
\* D49. The waiters already follow the barging rule: a reset wakes every
\* waiter and each competes for the initializer role with a CAS, with no
\* handoff; once a value is published every waiter gets it. So the D49
\* note's "make that consistent" changes nothing in this model. (No bypass
\* bound is needed: a value, once published, serves every waiter.)
\*
\* THE DESIGN (plan 4.11). `OnceCell<T>`: `get`, `get_or_init(future)`,
\* `get_or_try_init`; synchronous `const fn new`, `set(v)` (one CAS,
\* wait-free) and `get_or_init_racy(f)` (every racer builds, one CAS
\* publishes, the losers drop theirs). `Lazy<T>`: `force` and `Deref`, built
\* on `get_or_init_racy`. Exactly one value is published.
\*
\* THE PROTOCOL MODELLED. One state word: "empty", "init" (an async
\* initializer, named in the word, is running its future) or "ready" (a
\* value is published).
\*   - get_or_init / get_or_try_init: on "ready" return the value; on
\*     "empty" CAS to "init" and run the future; on "init" register a
\*     waiter, push its node, and re-check (the initializer may have
\*     finished in between). A woken waiter returns the value if "ready",
\*     and tries to initialize itself if "empty".
\*   - The initializer publishes with a CAS from its own "init" to "ready".
\*     If the future fails, or is dropped, it CASes "init" back to "empty".
\*     Either way it wakes every waiter, so on failure or drop one of them
\*     takes over.
\*   - set(v) and get_or_init_racy publish with one CAS from "empty" or
\*     "init" to "ready". A racer that loses drops its value and returns
\*     the published one.
\*
\* DESIGN CHOICES WHERE THE PLAN IS SILENT, recorded in the final report.
\*   - The synchronous publishers (set, get_or_init_racy, Lazy::force) may
\*     publish over an async initializer that is still running: they
\*     cannot wait for it without blocking. That initializer's own publish
\*     CAS then fails; it drops its value and returns the published one.
\*     Its waiters are woken by whoever published.
\*   - A dropped initializer resets the cell to "empty" and wakes all
\*     waiters, so one of them initializes; nothing is lost but the
\*     dropped future's work.
\*
\* FOUND BY THIS MODEL. A woken waiter can find the cell back in "init":
\* the reset that woke it took its node with the whole list, and a new
\* initializer started before the waiter was polled. Re-storing its waker
\* then strands it, since no node of it is listed for the new initializer
\* to wake. The waiter must push a new node (Poll, Recheck). An earlier
\* draft of this model re-stored the waker, and TLC found the lost wakeup;
\* mutant ReparkStale keeps that draft as a RED.
\*
\* WHAT THE MODEL LEAVES OUT. Each task runs one operation; task t's
\* value is t, so values are told apart by who built them. Memory ordering
\* is loom's (plan 7.1).
\*
\* CONFIGURATIONS.
\*   MC_SyncOnce_Green              three tasks, each one of get_or_init,
\*                                  get_or_try_init, set or
\*                                  get_or_init_racy, with failures and
\*                                  drops: one value, every reader agrees,
\*                                  every waiter finishes.
\*   MC_SyncOnce_Red_CancelNoReset  a dropped initializer leaves "init":
\*                                  NoLostWakeup.
\*   MC_SyncOnce_Red_PlainStore     publish with a store, not a CAS:
\*                                  PublishedOnce.
\*   MC_SyncOnce_Red_NoRecheck      a waiter parks without the re-check:
\*                                  NoLostWakeup.
\*   MC_SyncOnce_Red_ReparkStale    a woken waiter that finds "init" again
\*                                  re-stores its waker without a node:
\*                                  NoLostWakeup.

\* Borrow the standard TLA+ books: counting numbers, lists, and sizes of finite sets.
EXTENDS Naturals, Sequences, FiniteSets

\* The fixed inputs a configuration chooses.
CONSTANTS
  \* The tasks that use the cell, named by positive numbers. The value task t would publish is the
  \* number t, so values tell who built them.
  Tasks,
  \* "none" for the design, or the planted bug: "CancelNoReset", "PlainStore", "NoRecheck" or
  \* "ReparkStale".
  Mutant

\* Tasks are positive numbers (0 means "no task").
ASSUME Tasks \subseteq Nat \ {0}
\* The mutant is "none" or one of the four planted bugs.
ASSUME Mutant \in {"none", "CancelNoReset", "PlainStore", "NoRecheck", "ReparkStale"}

\* The value "no task", and "no value".
None == 0

\* The state: everything that changes from one step to the next. Each line says what the variable
\* stands for in the real program.
VARIABLES
  \* The cell's state: "empty", "init" (an initializer is running) or "ready" (a value is
  \* published). In the engine (src/sync/once_cell.rs) this is not one word: "ready" is the value
  \* pointer being set, and "init" is the one-permit semaphore being held by an initializer.
  st,
  \* Which task is the running initializer while the state is "init", else None (in the engine: the
  \* task holding the semaphore's permit).
  by,
  \* The published value while the state is "ready", else None (the atomic pointer OnceCell reads
  \* with one load).
  val,
  \* The waiters registered right now (in the engine: the tasks queued on the semaphore).
  q,
  \* Whether each waiter was woken since it registered its waker.
  woken,
  \* The waiters a task has taken from the list and has not woken yet, per task.
  towake,
  \* The value each finished task returned to its caller, or None.
  result,
  \* Where each task is: its "program counter" (see PCs below).
  pc,
  \* Model bookkeeping (a "ghost"): every value ever published, in order. The promise PublishedOnce
  \* reads it.
  published

\* Every variable, so a step that changes none of them is a stutter.
vars == <<st, by, val, q, woken, towake, result, pc, published>>

\* Task t parks again on "init": with its node still listed, or (mutant
\* ReparkStale) whether or not it is, by re-storing its waker only.
Repark(t) == t \in q \/ Mutant = "ReparkStale"

\* The places a task can be: "idle" (has not started), "running" (its
\* async init future runs), "building" (a racy builder building its
\* value), "push", "recheck", "parked" (waiting for the initializer),
\* "wake" (waking waiters), "done".
PCs == {"idle", "running", "building", "push", "recheck", "parked", "wake", "done"}

\* Publish task t's value: the state word becomes "ready" with it, and t
\* takes every waiter to wake them.
Publish(t) ==
  \* The cell is ready.
  /\ st' = "ready"
  \* No initializer is running.
  /\ by' = None
  \* The value is this task's.
  /\ val' = t
  \* One more publication is recorded.
  /\ published' = Append(published, t)
  \* The task takes every registered waiter onto its wake list.
  /\ towake' = [towake EXCEPT ![t] = q]
  \* The waiter list is empty.
  /\ q' = {}
  \* The task returns its own value.
  /\ result' = [result EXCEPT ![t] = t]
  \* It goes on to wake the waiters.
  /\ pc' = [pc EXCEPT ![t] = "wake"]

\* Task t looks at the state word on behalf of get_or_init: return the
\* value if "ready", become the initializer if "empty", else register.
TryInit(t) ==
  \* A value is published:
  CASE st = "ready" ->
         \* the task returns it
         /\ result' = [result EXCEPT ![t] = val]
         \* and is done.
         /\ pc' = [pc EXCEPT ![t] = "done"]
         \* The cell is untouched.
         /\ UNCHANGED <<st, by>>
    \* The cell is empty:
    [] st = "empty" ->
         \* the task marks it "init",
         /\ st' = "init"
         \* names itself the initializer,
         /\ by' = t
         \* and runs its future.
         /\ pc' = [pc EXCEPT ![t] = "running"]
         \* It has returned nothing yet.
         /\ UNCHANGED result
    \* An initializer is running:
    [] OTHER ->
         \* the task goes on to register as a waiter.
         /\ pc' = [pc EXCEPT ![t] = "push"]
         \* The cell is untouched.
         /\ UNCHANGED <<st, by, result>>

----------------------------------------------------------------------------
\* Actions.

\* get_or_init(future) / get_or_try_init(future), first poll.
GetOrInit(t) ==
  \* The task has not started.
  /\ pc[t] = "idle"
  \* It looks at the cell and acts on what it finds.
  /\ TryInit(t)
  \* Nothing else changes.
  /\ UNCHANGED <<val, q, woken, towake, published>>

\* The waiter pushes its node with its Waker. Mutant NoRecheck: it parks
\* at once.
Push(t) ==
  \* The task found an initializer running and has not registered yet.
  /\ pc[t] = "push"
  \* Its node joins the waiter list.
  /\ q' = q \cup {t}
  \* It has not been woken.
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  \* It goes on to look at the cell once more (under the bug NoRecheck it goes straight to sleep).
  /\ pc' = [pc EXCEPT ![t] = IF Mutant = "NoRecheck" THEN "parked" ELSE "recheck"]
  \* Nothing else changes.
  /\ UNCHANGED <<st, by, val, towake, result, published>>

\* The re-check after the push. Still "init" with the node still listed:
\* park. Still "init" but the node gone: a dropped initializer's reset took
\* it and a new initializer started since, so push a new one (parking now
\* would leave nobody to wake this waiter). Otherwise take the node back
\* out and act on what is there now.
Recheck(t) ==
  \* The task is at its second look.
  /\ pc[t] = "recheck"
  \* Is an initializer still running?
  /\ IF st = "init"
       \* Yes: sleep if its node is still listed; if the node is gone, register afresh (the bug
       \* ReparkStale sleeps anyway).
       THEN /\ pc' = [pc EXCEPT ![t] = IF Repark(t) THEN "parked" ELSE "push"]
            \* The cell and the list are untouched.
            /\ UNCHANGED <<st, by, q, result>>
       \* No: it takes its node back out of the list,
       ELSE /\ q' = q \ {t}
            \* and acts on what the cell holds now.
            /\ TryInit(t)
  \* Nothing else changes.
  /\ UNCHANGED <<val, woken, towake, published>>

\* The executor polls a woken waiter: "ready", it returns the value;
\* "empty" (the initializer failed or was dropped), it tries to initialize;
\* "init" again (a new initializer took over after the reset that woke it,
\* and that reset took its node), it registers again with a new node.
Poll(t) ==
  \* The task is asleep.
  /\ pc[t] = "parked"
  \* It was woken.
  /\ woken[t]
  \* Its woken bit is cleared.
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  \* Is an initializer running (a new one, started after the reset that woke this task)?
  /\ IF st = "init"
       \* Yes: sleep again if its node is still listed, else register afresh (the bug ReparkStale
       \* sleeps anyway).
       THEN /\ pc' = [pc EXCEPT ![t] = IF Repark(t) THEN "parked" ELSE "push"]
            \* The cell and the list are untouched.
            /\ UNCHANGED <<st, by, result, q>>
       \* No: its node leaves the list,
       ELSE /\ q' = q \ {t}
            \* and it acts on what the cell holds now.
            /\ TryInit(t)
  \* Nothing else changes.
  /\ UNCHANGED <<val, towake, published>>

\* The initializer's future completes with a value: CAS its own "init" to
\* "ready" and wake every waiter. If a synchronous publisher got there
\* first, drop the value and return the published one. Mutant PlainStore:
\* a store, so it publishes over whatever is there.
InitOk(t) ==
  \* The task's initializer future has finished with a value.
  /\ pc[t] = "running"
  \* Is the cell still "init" in this task's name (the bug PlainStore does not ask)?
  /\ IF (st = "init" /\ by = t) \/ Mutant = "PlainStore"
       \* Yes: publish.
       THEN Publish(t)
       \* No, somebody published meanwhile: the task returns that value, dropping its own,
       ELSE /\ result' = [result EXCEPT ![t] = val]
            \* and is done.
            /\ pc' = [pc EXCEPT ![t] = "done"]
            \* The cell is untouched.
            /\ UNCHANGED <<st, by, val, published, towake, q>>
  \* Nobody is woken in this step.
  /\ UNCHANGED woken

\* get_or_try_init's future fails: CAS its own "init" back to "empty" and
\* wake every waiter, one of which takes over. The caller gets the error.
InitErr(t) ==
  \* The task's initializer future has failed.
  /\ pc[t] = "running"
  \* Is the cell still "init" in its name?
  /\ IF st = "init" /\ by = t
       \* Yes: the cell is empty again,
       THEN /\ st' = "empty"
            \* with no initializer,
            /\ by' = None
            \* the task takes every waiter onto its wake list,
            /\ towake' = [towake EXCEPT ![t] = q]
            \* the waiter list is empty,
            /\ q' = {}
            \* and the task goes on to wake them, so that one of them takes over.
            /\ pc' = [pc EXCEPT ![t] = "wake"]
       \* No, somebody published meanwhile: the task is done.
       ELSE /\ pc' = [pc EXCEPT ![t] = "done"]
            \* The cell is untouched.
            /\ UNCHANGED <<st, by, towake, q>>
  \* Nothing else changes.
  /\ UNCHANGED <<val, woken, result, published>>

\* The initializer's future is dropped mid-run: the same reset and wake as
\* a failure, so a waiter takes over. Mutant CancelNoReset: it just goes,
\* leaving "init" naming a task that will never publish.
CancelInit(t) ==
  \* The task's initializer future is running, and is dropped.
  /\ pc[t] = "running"
  \* Is the cell still "init" in its name (and the bug CancelNoReset not planted)?
  /\ IF st = "init" /\ by = t /\ Mutant # "CancelNoReset"
       \* Yes: the cell is empty again,
       THEN /\ st' = "empty"
            \* with no initializer,
            /\ by' = None
            \* the task takes every waiter onto its wake list,
            /\ towake' = [towake EXCEPT ![t] = q]
            \* the waiter list is empty,
            /\ q' = {}
            \* and the task goes on to wake them.
            /\ pc' = [pc EXCEPT ![t] = "wake"]
       \* No (or the bug): the task just stops,
       ELSE /\ pc' = [pc EXCEPT ![t] = "done"]
            \* leaving the cell as it is.
            /\ UNCHANGED <<st, by, towake, q>>
  \* Nothing else changes.
  /\ UNCHANGED <<val, woken, result, published>>

\* A parked waiter's future is dropped: its node leaves the list.
CancelWait(t) ==
  \* The task is asleep as a waiter.
  /\ pc[t] = "parked"
  \* Its node leaves the list.
  /\ q' = q \ {t}
  \* Its woken bit is cleared.
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  \* It is done, having returned nothing.
  /\ pc' = [pc EXCEPT ![t] = "done"]
  \* Nothing else changes.
  /\ UNCHANGED <<st, by, val, towake, result, published>>

\* set(v): one CAS from "empty" or "init" to "ready"; on "ready" it fails
\* and returns the value back (Err(v)), recorded as no result.
Set(t) ==
  \* The task has not started.
  /\ pc[t] = "idle"
  \* Is no value published yet (the bug PlainStore does not ask)?
  /\ IF st # "ready" \/ Mutant = "PlainStore"
       \* Then publish.
       THEN Publish(t)
       \* Otherwise the set fails: the task is done,
       ELSE /\ pc' = [pc EXCEPT ![t] = "done"]
            \* and the cell is untouched.
            /\ UNCHANGED <<st, by, val, published, towake, q, result>>
  \* Nobody is woken in this step.
  /\ UNCHANGED woken

\* get_or_init_racy(f) / Lazy::force: on "ready" return the value;
\* otherwise build a value.
RacyStart(t) ==
  \* The task has not started.
  /\ pc[t] = "idle"
  \* Is a value published?
  /\ IF st = "ready"
       \* Yes: the task returns it
       THEN /\ result' = [result EXCEPT ![t] = val]
            \* and is done.
            /\ pc' = [pc EXCEPT ![t] = "done"]
       \* No: it goes on to build its own value.
       ELSE /\ pc' = [pc EXCEPT ![t] = "building"]
            \* It has returned nothing yet.
            /\ UNCHANGED result
  \* Nothing else changes.
  /\ UNCHANGED <<st, by, val, q, woken, towake, published>>

\* The racer has built its value: one CAS publishes it unless a value is
\* already published, in which case it drops its own and returns that one.
RacyPublish(t) ==
  \* The task has built its value.
  /\ pc[t] = "building"
  \* Is no value published yet (the bug PlainStore does not ask)?
  /\ IF st # "ready" \/ Mutant = "PlainStore"
       \* Then publish.
       THEN Publish(t)
       \* Otherwise the task returns the published value, dropping its own,
       ELSE /\ result' = [result EXCEPT ![t] = val]
            \* and is done.
            /\ pc' = [pc EXCEPT ![t] = "done"]
            \* The cell is untouched.
            /\ UNCHANGED <<st, by, val, published, towake, q>>
  \* Nobody is woken in this step.
  /\ UNCHANGED woken

\* A task wakes the waiters it took, one per step, then is done.
Wake(t) ==
  \* The task is delivering wakes.
  /\ pc[t] = "wake"
  \* None left?
  /\ IF towake[t] = {}
       \* Then it is done.
       THEN pc' = [pc EXCEPT ![t] = "done"] /\ UNCHANGED <<woken, towake>>
       \* Otherwise it picks one waiter u from its list:
       ELSE \E u \in towake[t] :
              \* u is woken,
              /\ woken' = [woken EXCEPT ![u] = TRUE]
              \* and leaves the list.
              /\ towake' = [towake EXCEPT ![t] = @ \ {u}]
              \* The task stays here for the rest.
              /\ UNCHANGED pc
  \* Nothing else changes.
  /\ UNCHANGED <<st, by, val, q, result, published>>

----------------------------------------------------------------------------
\* The specification.

\* The start: an empty cell (`const fn new`), nobody started.
Init ==
  \* The cell is empty.
  /\ st = "empty"
  \* No initializer is running.
  /\ by = None
  \* No value is published.
  /\ val = None
  \* Nobody is registered.
  /\ q = {}
  \* Nobody was woken.
  /\ woken = [t \in Tasks |-> FALSE]
  \* Nobody has wakes to deliver.
  /\ towake = [t \in Tasks |-> {}]
  \* Nobody has returned anything.
  /\ result = [t \in Tasks |-> None]
  \* No task has started.
  /\ pc = [t \in Tasks |-> "idle"]
  \* Nothing was ever published.
  /\ published = <<>>

\* The steps a task takes on its own once started. A running initializer
\* finishes, with a value or an error.
Internal(t) ==
  \* A waiter's steps, a wake, a racing builder's publish,
  \/ Push(t) \/ Recheck(t) \/ Poll(t) \/ Wake(t) \/ RacyPublish(t)
  \* and an initializer's future ending well or badly.
  \/ InitOk(t) \/ InitErr(t)

\* Every step the system can take.
Next ==
  \* Some task
  \E t \in Tasks :
    \* starts get_or_init, calls set, starts a racing build, drops its initializer, drops its wait,
    \* or takes one of its own steps.
    GetOrInit(t) \/ Set(t) \/ RacyStart(t) \/ CancelInit(t) \/ CancelWait(t) \/ Internal(t)

\* Fairness: started operations finish and woken futures are polled.
\* Starting one, and dropping a future, are the caller's choices.
Fairness == \A t \in Tasks : WF_vars(Internal(t))

\* Every behaviour: start in Init, take Next steps or stutter, fairly.
Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  \* The state is one of the three.
  /\ st \in {"empty", "init", "ready"}
  \* The initializer is a task or nobody.
  /\ by \in Tasks \cup {None}
  \* The value is a task's or none.
  /\ val \in Tasks \cup {None}
  \* Only tasks are registered.
  /\ q \subseteq Tasks
  \* Every task is at one of the known places.
  /\ pc \in [Tasks -> PCs]
  \* The cell is ready exactly when it holds a value.
  /\ (st = "ready") <=> (val # None)

\* EXACTLY ONE VALUE IS PUBLISHED. At most one publication ever happens,
\* so the value never changes once set.
\* Rules out, for example: one task publishes value 1, another task has already returned it to its
\* caller, and then a second publisher stores value 2 over it.
PublishedOnce == Len(published) <= 1

\* EVERY READER AGREES. Every value a task returned is the published one.
\* Rules out, for example: two tasks each believe they initialized the cell and return two different
\* values.
ReadersAgree == \A t \in Tasks : result[t] # None => (st = "ready" /\ result[t] = val)

\* NO LOST WAKEUP. "init" always names an initializer that is still
\* running, so it will publish or reset and wake; and a parked waiter on a
\* cell that is not "init" has been woken or is about to be.
NoLostWakeup ==
  \* While the state is "init", the task it names is really running its future.
  /\ st = "init" => pc[by] = "running"
  \* And every task
  /\ \A t \in Tasks :
       \* that sleeps while no initializer is running was woken, or is on somebody's wake list.
       \* Rules out, for example: the initializer is dropped and leaves the cell marked "init" for
       \* ever, and its waiters sleep for ever.
       (pc[t] = "parked" /\ st # "init") => (woken[t] \/ \E d \in Tasks : t \in towake[d])

----------------------------------------------------------------------------
\* Liveness.

\* Every waiter finishes: it gets the value, or initializes itself.
\* Rules out a waiter that never learns the value and never gets its own turn to initialize.
EveryWaiterFinishes == \A t \in Tasks : (pc[t] = "parked") ~> (pc[t] # "parked")

====
