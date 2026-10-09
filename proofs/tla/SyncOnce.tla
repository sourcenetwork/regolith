---- MODULE SyncOnce ----
\* regolith::sync::OnceCell and Lazy (plan 4.11): exactly one value is
\* published, whatever the initializers race, fail or get dropped.
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

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Tasks,   \* the tasks using the cell: positive naturals; task t's value is t
  Mutant   \* "none", "CancelNoReset", "PlainStore", "NoRecheck" or
           \* "ReparkStale"

ASSUME Tasks \subseteq Nat \ {0}
ASSUME Mutant \in {"none", "CancelNoReset", "PlainStore", "NoRecheck", "ReparkStale"}

\* The value "no task", and "no value".
None == 0

VARIABLES
  st,         \* the state word: "empty", "init" or "ready"
  by,         \* the running async initializer while "init", else None
  val,        \* the published value while "ready", else None
  q,          \* the registered waiters
  woken,      \* [Tasks -> BOOLEAN]: Waker::wake ran since it was registered
  towake,     \* [Tasks -> SUBSET Tasks]: waiters a task has yet to wake
  result,     \* [Tasks -> Nat]: the value each finished task returned
  pc,         \* [Tasks -> pc]
  published   \* ghost: every value ever published, in order

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
  /\ st' = "ready"
  /\ by' = None
  /\ val' = t
  /\ published' = Append(published, t)
  /\ towake' = [towake EXCEPT ![t] = q]
  /\ q' = {}
  /\ result' = [result EXCEPT ![t] = t]
  /\ pc' = [pc EXCEPT ![t] = "wake"]

\* Task t looks at the state word on behalf of get_or_init: return the
\* value if "ready", become the initializer if "empty", else register.
TryInit(t) ==
  CASE st = "ready" ->
         /\ result' = [result EXCEPT ![t] = val]
         /\ pc' = [pc EXCEPT ![t] = "done"]
         /\ UNCHANGED <<st, by>>
    [] st = "empty" ->
         /\ st' = "init"
         /\ by' = t
         /\ pc' = [pc EXCEPT ![t] = "running"]
         /\ UNCHANGED result
    [] OTHER ->
         /\ pc' = [pc EXCEPT ![t] = "push"]
         /\ UNCHANGED <<st, by, result>>

----------------------------------------------------------------------------
\* Actions.

\* get_or_init(future) / get_or_try_init(future), first poll.
GetOrInit(t) ==
  /\ pc[t] = "idle"
  /\ TryInit(t)
  /\ UNCHANGED <<val, q, woken, towake, published>>

\* The waiter pushes its node with its Waker. Mutant NoRecheck: it parks
\* at once.
Push(t) ==
  /\ pc[t] = "push"
  /\ q' = q \cup {t}
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  /\ pc' = [pc EXCEPT ![t] = IF Mutant = "NoRecheck" THEN "parked" ELSE "recheck"]
  /\ UNCHANGED <<st, by, val, towake, result, published>>

\* The re-check after the push. Still "init" with the node still listed:
\* park. Still "init" but the node gone: a dropped initializer's reset took
\* it and a new initializer started since, so push a new one (parking now
\* would leave nobody to wake this waiter). Otherwise take the node back
\* out and act on what is there now.
Recheck(t) ==
  /\ pc[t] = "recheck"
  /\ IF st = "init"
       THEN /\ pc' = [pc EXCEPT ![t] = IF Repark(t) THEN "parked" ELSE "push"]
            /\ UNCHANGED <<st, by, q, result>>
       ELSE /\ q' = q \ {t}
            /\ TryInit(t)
  /\ UNCHANGED <<val, woken, towake, published>>

\* The executor polls a woken waiter: "ready", it returns the value;
\* "empty" (the initializer failed or was dropped), it tries to initialize;
\* "init" again (a new initializer took over after the reset that woke it,
\* and that reset took its node), it registers again with a new node.
Poll(t) ==
  /\ pc[t] = "parked"
  /\ woken[t]
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  /\ IF st = "init"
       THEN /\ pc' = [pc EXCEPT ![t] = IF Repark(t) THEN "parked" ELSE "push"]
            /\ UNCHANGED <<st, by, result, q>>
       ELSE /\ q' = q \ {t}
            /\ TryInit(t)
  /\ UNCHANGED <<val, towake, published>>

\* The initializer's future completes with a value: CAS its own "init" to
\* "ready" and wake every waiter. If a synchronous publisher got there
\* first, drop the value and return the published one. Mutant PlainStore:
\* a store, so it publishes over whatever is there.
InitOk(t) ==
  /\ pc[t] = "running"
  /\ IF (st = "init" /\ by = t) \/ Mutant = "PlainStore"
       THEN Publish(t)
       ELSE /\ result' = [result EXCEPT ![t] = val]
            /\ pc' = [pc EXCEPT ![t] = "done"]
            /\ UNCHANGED <<st, by, val, published, towake, q>>
  /\ UNCHANGED woken

\* get_or_try_init's future fails: CAS its own "init" back to "empty" and
\* wake every waiter, one of which takes over. The caller gets the error.
InitErr(t) ==
  /\ pc[t] = "running"
  /\ IF st = "init" /\ by = t
       THEN /\ st' = "empty"
            /\ by' = None
            /\ towake' = [towake EXCEPT ![t] = q]
            /\ q' = {}
            /\ pc' = [pc EXCEPT ![t] = "wake"]
       ELSE /\ pc' = [pc EXCEPT ![t] = "done"]
            /\ UNCHANGED <<st, by, towake, q>>
  /\ UNCHANGED <<val, woken, result, published>>

\* The initializer's future is dropped mid-run: the same reset and wake as
\* a failure, so a waiter takes over. Mutant CancelNoReset: it just goes,
\* leaving "init" naming a task that will never publish.
CancelInit(t) ==
  /\ pc[t] = "running"
  /\ IF st = "init" /\ by = t /\ Mutant # "CancelNoReset"
       THEN /\ st' = "empty"
            /\ by' = None
            /\ towake' = [towake EXCEPT ![t] = q]
            /\ q' = {}
            /\ pc' = [pc EXCEPT ![t] = "wake"]
       ELSE /\ pc' = [pc EXCEPT ![t] = "done"]
            /\ UNCHANGED <<st, by, towake, q>>
  /\ UNCHANGED <<val, woken, result, published>>

\* A parked waiter's future is dropped: its node leaves the list.
CancelWait(t) ==
  /\ pc[t] = "parked"
  /\ q' = q \ {t}
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  /\ pc' = [pc EXCEPT ![t] = "done"]
  /\ UNCHANGED <<st, by, val, towake, result, published>>

\* set(v): one CAS from "empty" or "init" to "ready"; on "ready" it fails
\* and returns the value back (Err(v)), recorded as no result.
Set(t) ==
  /\ pc[t] = "idle"
  /\ IF st # "ready" \/ Mutant = "PlainStore"
       THEN Publish(t)
       ELSE /\ pc' = [pc EXCEPT ![t] = "done"]
            /\ UNCHANGED <<st, by, val, published, towake, q, result>>
  /\ UNCHANGED woken

\* get_or_init_racy(f) / Lazy::force: on "ready" return the value;
\* otherwise build a value.
RacyStart(t) ==
  /\ pc[t] = "idle"
  /\ IF st = "ready"
       THEN /\ result' = [result EXCEPT ![t] = val]
            /\ pc' = [pc EXCEPT ![t] = "done"]
       ELSE /\ pc' = [pc EXCEPT ![t] = "building"]
            /\ UNCHANGED result
  /\ UNCHANGED <<st, by, val, q, woken, towake, published>>

\* The racer has built its value: one CAS publishes it unless a value is
\* already published, in which case it drops its own and returns that one.
RacyPublish(t) ==
  /\ pc[t] = "building"
  /\ IF st # "ready" \/ Mutant = "PlainStore"
       THEN Publish(t)
       ELSE /\ result' = [result EXCEPT ![t] = val]
            /\ pc' = [pc EXCEPT ![t] = "done"]
            /\ UNCHANGED <<st, by, val, published, towake, q>>
  /\ UNCHANGED woken

\* A task wakes the waiters it took, one per step, then is done.
Wake(t) ==
  /\ pc[t] = "wake"
  /\ IF towake[t] = {}
       THEN pc' = [pc EXCEPT ![t] = "done"] /\ UNCHANGED <<woken, towake>>
       ELSE \E u \in towake[t] :
              /\ woken' = [woken EXCEPT ![u] = TRUE]
              /\ towake' = [towake EXCEPT ![t] = @ \ {u}]
              /\ UNCHANGED pc
  /\ UNCHANGED <<st, by, val, q, result, published>>

----------------------------------------------------------------------------
\* The specification.

\* The start: an empty cell (`const fn new`), nobody started.
Init ==
  /\ st = "empty"
  /\ by = None
  /\ val = None
  /\ q = {}
  /\ woken = [t \in Tasks |-> FALSE]
  /\ towake = [t \in Tasks |-> {}]
  /\ result = [t \in Tasks |-> None]
  /\ pc = [t \in Tasks |-> "idle"]
  /\ published = <<>>

\* The steps a task takes on its own once started. A running initializer
\* finishes, with a value or an error.
Internal(t) ==
  \/ Push(t) \/ Recheck(t) \/ Poll(t) \/ Wake(t) \/ RacyPublish(t)
  \/ InitOk(t) \/ InitErr(t)

\* Every step the system can take.
Next ==
  \E t \in Tasks :
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
  /\ st \in {"empty", "init", "ready"}
  /\ by \in Tasks \cup {None}
  /\ val \in Tasks \cup {None}
  /\ q \subseteq Tasks
  /\ pc \in [Tasks -> PCs]
  /\ (st = "ready") <=> (val # None)

\* EXACTLY ONE VALUE IS PUBLISHED. At most one publication ever happens,
\* so the value never changes once set.
PublishedOnce == Len(published) <= 1

\* EVERY READER AGREES. Every value a task returned is the published one.
ReadersAgree == \A t \in Tasks : result[t] # None => (st = "ready" /\ result[t] = val)

\* NO LOST WAKEUP. "init" always names an initializer that is still
\* running, so it will publish or reset and wake; and a parked waiter on a
\* cell that is not "init" has been woken or is about to be.
NoLostWakeup ==
  /\ st = "init" => pc[by] = "running"
  /\ \A t \in Tasks :
       (pc[t] = "parked" /\ st # "init") => (woken[t] \/ \E d \in Tasks : t \in towake[d])

----------------------------------------------------------------------------
\* Liveness.

\* Every waiter finishes: it gets the value, or initializes itself.
EveryWaiterFinishes == \A t \in Tasks : (pc[t] = "parked") ~> (pc[t] # "parked")

====
