---- MODULE SyncRwLock ----
\* regolith::sync::RwLock and ReentrantRwLock (plan 4.11): phase-fair
\* reader-writer locks on the waiter queue of Sync.tla.
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/Sync.lean: the
\* waiter queue's laws (at_most_one_owner, fifo_served, no_stranded_waiter,
\* handed_holds) that each of this lock's two queues obeys. The phase-fair
\* policy and the reentrant owner rules are checked here only, for three
\* tasks; no Lean theorem covers them.
\*
\* THE DESIGN (plan 4.11). `RwLock<T>`: try_read, try_write, read(),
\* write(); phase-fair, so readers and writers alternate when both wait and
\* neither starves. `ReentrantRwLock<T>`: read(owner), write(owner) and try_
\* forms; an owner holding write may also read; owner-aware queueing, so an
\* owner never deadlocks on itself behind a queued writer.
\*
\* THE POLICY MODELLED. Two FIFO queues, readers and writers.
\*   - A fresh read enters at once only if no writer holds or waits;
\*     otherwise it queues. So readers that arrive while a writer waits wait
\*     for that writer: the read phase in progress does not grow past it.
\*   - A fresh write enters at once only if nobody holds and nobody waits.
\*   - When a write phase ends, every queued reader is admitted together:
\*     the next phase is a read phase, even if writers wait. When a read
\*     phase ends, the oldest waiting writer is handed the lock.
\*   - A reentrant request by a task whose Owner already holds what it
\*     needs (read under its own read or write, write under its own write)
\*     enters at once, whatever waits. That is what keeps an owner from
\*     queueing behind a writer that waits for the owner itself.
\*   - Cancellation as in Sync.tla: a waiting node leaves its queue; a
\*     granted one passes its guard on. A waiting writer that leaves admits
\*     the readers that were queued only because of writers.
\*
\* DESIGN CHOICES WHERE THE PLAN IS SILENT, recorded in the final report.
\*   - Upgrade. A task holding a read guard of a ReentrantRwLock, and not
\*     the write, may not ask for write: it would wait for its own read to
\*     end. The model does not offer that step; the implementation must
\*     refuse it with an error, not wait. Another task of the same Owner
\*     may queue for write while its owner reads: it waits for the other
\*     task, not for itself.
\*   - Phase fairness is stated as bounded bypass, the classical form: a
\*     waiting reader sees at most one write phase begin, and a waiting
\*     writer sees readers admitted only in the batches that end the write
\*     phases ahead of it.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - The queue mechanics. Registration, the re-check after the push, the
\*     drain token and the node CAS are Sync.tla's, checked there step by
\*     step. Here a handoff, a cancel and an admission are each one step;
\*     the wakes that follow a handoff are separate steps, so the order
\*     handoff, then wake is still checked.
\*   - Memory ordering: loom's (plan 7.1).
\*
\* CONFIGURATIONS.
\*   MC_SyncRwLock_Green_Plain       RwLock, three tasks reading and
\*                                   writing: every invariant, and every
\*                                   waiter is eventually served.
\*   MC_SyncRwLock_Green_Reentrant   ReentrantRwLock, tasks 1 and 2 of one
\*                                   owner, nesting up to two guards: every
\*                                   safety invariant.
\*   MC_SyncRwLock_Green_ReentrantLive  the same with one guard per task
\*                                   (re-entry across the owner's two
\*                                   tasks): if no owner holds forever,
\*                                   every waiter is served.
\*   MC_SyncRwLock_Red_WriterPreference  a write release hands to the next
\*                                   writer while readers wait:
\*                                   ReadersWaitOnePhase.
\*   MC_SyncRwLock_Red_ReaderBarging a fresh read enters while a writer
\*                                   waits: WritersBoundedBypass.
\*   MC_SyncRwLock_Red_OwnerUnaware  an owner's second read queues behind a
\*                                   waiting writer: NoSelfDeadlock.
\*   MC_SyncRwLock_Red_WriterCancelStrands  a waiting writer leaves and the
\*                                   readers behind it stay queued:
\*                                   NoLostWakeup.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Tasks,     \* the tasks using the lock: positive naturals
  Kind,      \* "Plain" (RwLock) or "Reentrant" (ReentrantRwLock)
  Owner,     \* [Tasks -> positive naturals]: the Owner token of each task
  MaxDepth,  \* the most guards one task holds at once
  Watched,   \* the tasks whose liveness is checked: one per role (below)
  Mutant     \* "none" for the design, or the name of one defect

\* The value "no owner holds write".
NoOwner == 0
\* Every Owner token some task uses.
Owners == {Owner[t] : t \in Tasks}

ASSUME Kind \in {"Plain", "Reentrant"}
ASSUME Tasks \subseteq Nat \ {0} /\ Owners \subseteq Nat \ {0}
ASSUME MaxDepth \in Nat \ {0} /\ Watched \subseteq Tasks
ASSUME Kind = "Plain" => MaxDepth = 1 /\ \A t, u \in Tasks : t # u => Owner[t] # Owner[u]
ASSUME Mutant \in {"none", "WriterPreference", "ReaderBarging", "OwnerUnaware",
                   "WriterCancelStrands"}

\* Configuration helpers, named in the MC_SyncRwLock_*.cfg files.
\* Every task is its own Owner (a plain RwLock).
OwnerEach == [t \in Tasks |-> t]
\* Tasks 1 and 2 share Owner 1, task 3 is Owner 2.
OwnerPair == [t \in Tasks |-> IF t = 3 THEN 2 ELSE 1]

VARIABLES
  rd,      \* [Tasks -> Nat]: read guards each task holds
  wr,      \* [Tasks -> Nat]: write guards each task holds
  rdepth,  \* [Owners -> Nat]: the lock's per-owner read depth
  wowner,  \* the Owner holding write, or NoOwner
  wdepth,  \* write guards out
  rq,      \* queued readers, oldest first
  wq,      \* queued writers, oldest first
  node,    \* [Tasks -> {"none", "waiting", "granted"}]
  want,    \* [Tasks -> {"read", "write"}]: what a queued task waits for
  woken,   \* [Tasks -> BOOLEAN]: Waker::wake ran since it was registered
  towake,  \* [Tasks -> SUBSET Tasks]: waiters a task handed to, not yet woken
  ret,     \* [Tasks -> pc]: where a task resumes once its wakes are done
  pc,      \* [Tasks -> {"idle", "holding", "parked", "wake"}]
  wph,     \* ghost [Tasks -> Nat]: write phases begun while a reader waits
  bypass,  \* ghost [Tasks -> Nat]: readers admitted while a writer waits
  ahead    \* ghost [Tasks -> Nat]: writers queued ahead of a writer at enqueue

\* Every variable, so a step that changes none of them is a stutter.
vars == <<rd, wr, rdepth, wowner, wdepth, rq, wq, node, want, woken, towake,
          ret, pc, wph, bypass, ahead>>

----------------------------------------------------------------------------
\* The lock's words as one record, so a guard drop and the handoff it
\* triggers compose as functions: L1 == Drop(L), L2 == Handoff(L1).

\* The current lock state.
Lock == [rd |-> rd, wr |-> wr, rdepth |-> rdepth, wowner |-> wowner,
         wdepth |-> wdepth, rq |-> rq, wq |-> wq, node |-> node,
         wph |-> wph, bypass |-> bypass, ahead |-> ahead]

\* Make lock state L the next state.
Apply(L) ==
  /\ rd' = L.rd /\ wr' = L.wr /\ rdepth' = L.rdepth /\ wowner' = L.wowner
  /\ wdepth' = L.wdepth /\ rq' = L.rq /\ wq' = L.wq /\ node' = L.node
  /\ wph' = L.wph /\ bypass' = L.bypass /\ ahead' = L.ahead

\* The set of elements of a sequence.
Range(s) == {s[i] : i \in 1..Len(s)}

\* The sum of f[x] over a finite set S.
RECURSIVE SumOf(_, _)
SumOf(f, S) == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

\* No owner holds a read guard in L.
NoReaders(L) == \A o \in Owners : L.rdepth[o] = 0

\* Task t waits in L's queues for `w` ("read" or "write").
WaitsFor(L, t, w) == L.node[t] = "waiting" /\ want[t] = w

\* Admit every queued reader at once. Each waiting writer counts them as
\* readers that passed it.
AdmitAll(L) ==
  LET R == Range(L.rq) IN
  [L EXCEPT !.rd     = [t \in Tasks |-> IF t \in R THEN L.rd[t] + 1 ELSE L.rd[t]],
            !.rdepth = [o \in Owners |-> L.rdepth[o] + Cardinality({t \in R : Owner[t] = o})],
            !.node   = [t \in Tasks |-> IF t \in R THEN "granted" ELSE L.node[t]],
            !.rq     = <<>>,
            !.wph    = [t \in Tasks |-> IF t \in R THEN 0 ELSE L.wph[t]],
            !.bypass = [t \in Tasks |-> IF WaitsFor(L, t, "write")
                                          THEN L.bypass[t] + Cardinality(R) ELSE L.bypass[t]]]

\* Hand write to the oldest waiting writer: a write phase begins, and each
\* waiting reader counts it.
GrantWriter(L) ==
  LET w == Head(L.wq) IN
  [L EXCEPT !.wr     = [L.wr EXCEPT ![w] = @ + 1],
            !.wowner = Owner[w],
            !.wdepth = 1,
            !.node   = [L.node EXCEPT ![w] = "granted"],
            !.wq     = Tail(L.wq),
            !.bypass = [L.bypass EXCEPT ![w] = 0],
            !.ahead  = [L.ahead EXCEPT ![w] = 0],
            !.wph    = [t \in Tasks |-> IF WaitsFor(L, t, "read") THEN L.wph[t] + 1 ELSE L.wph[t]]]

\* After a write guard drops. If the write phase ended, the readers queued
\* during it go next, all together; with none queued, the oldest writer
\* (once no reader holds). Mutant WriterPreference: the next writer goes
\* first.
AfterWrite(L) ==
  IF L.wowner # NoOwner THEN L
  ELSE IF Mutant = "WriterPreference" /\ L.wq # <<>> /\ NoReaders(L) THEN GrantWriter(L)
  ELSE IF L.rq # <<>> THEN AdmitAll(L)
  ELSE IF L.wq # <<>> /\ NoReaders(L) THEN GrantWriter(L)
  ELSE L

\* After a read guard drops. If the read phase ended, the oldest writer
\* goes next. (Readers queue only behind writers, so with no writer left
\* the queued readers enter.)
AfterRead(L) ==
  IF L.wowner # NoOwner \/ ~NoReaders(L) THEN L
  ELSE IF L.wq # <<>> THEN GrantWriter(L)
  ELSE IF L.rq # <<>> THEN AdmitAll(L)
  ELSE L

\* After a waiting writer leaves its queue: if no writer holds or waits any
\* more, the readers queued behind writers enter. Mutant
\* WriterCancelStrands: they stay queued.
AfterWriterLeaves(L) ==
  IF Mutant # "WriterCancelStrands" /\ L.wq = <<>> /\ L.wowner = NoOwner /\ L.rq # <<>>
    THEN AdmitAll(L)
    ELSE L

\* Task t drops one read guard.
DropRead(L, t) ==
  [L EXCEPT !.rd = [@ EXCEPT ![t] = @ - 1],
            !.rdepth = [@ EXCEPT ![Owner[t]] = @ - 1]]

\* Task t drops one write guard; the last one frees write.
DropWrite(L, t) ==
  [L EXCEPT !.wr = [@ EXCEPT ![t] = @ - 1],
            !.wdepth = @ - 1,
            !.wowner = IF L.wdepth = 1 THEN NoOwner ELSE L.wowner]

\* The waiters a step handed the lock to: waiting in L1, granted in L2.
Granted(L1, L2) == {t \in Tasks : L1.node[t] = "waiting" /\ L2.node[t] = "granted"}

\* Task t ends its step: if it handed the lock to anyone it goes on to wake
\* them, and resumes at `next` afterwards.
Finish(t, G, next) ==
  IF G = {}
    THEN /\ pc' = [pc EXCEPT ![t] = next]
         /\ UNCHANGED <<towake, ret>>
    ELSE /\ pc' = [pc EXCEPT ![t] = "wake"]
         /\ towake' = [towake EXCEPT ![t] = G]
         /\ ret' = [ret EXCEPT ![t] = next]

\* Task t's Owner already holds the lock in a mode that covers a read.
OwnerCoversRead(t) ==
  /\ Kind = "Reentrant"
  /\ \/ wowner = Owner[t]
     \/ rdepth[Owner[t]] > 0 /\ Mutant # "OwnerUnaware"

----------------------------------------------------------------------------
\* Actions.

\* read() / read(owner) / try_read. Re-entry when the owner covers it;
\* otherwise in at once only when no writer holds or waits (mutant
\* ReaderBarging: when no writer holds); otherwise queue.
Read(t) ==
  /\ pc[t] \in {"idle", "holding"}
  /\ rd[t] + wr[t] < MaxDepth
  /\ IF OwnerCoversRead(t)
       THEN /\ rd' = [rd EXCEPT ![t] = @ + 1]
            /\ rdepth' = [rdepth EXCEPT ![Owner[t]] = @ + 1]
            /\ pc' = [pc EXCEPT ![t] = "holding"]
            /\ UNCHANGED <<wr, wowner, wdepth, rq, wq, node, want, woken, wph, bypass, ahead>>
       ELSE IF wowner = NoOwner /\ (wq = <<>> \/ Mutant = "ReaderBarging")
       THEN /\ rd' = [rd EXCEPT ![t] = @ + 1]
            /\ rdepth' = [rdepth EXCEPT ![Owner[t]] = @ + 1]
            /\ bypass' = [u \in Tasks |-> IF WaitsFor(Lock, u, "write") THEN bypass[u] + 1 ELSE bypass[u]]
            /\ pc' = [pc EXCEPT ![t] = "holding"]
            /\ UNCHANGED <<wr, wowner, wdepth, rq, wq, node, want, woken, wph, ahead>>
       ELSE /\ rq' = Append(rq, t)
            /\ node' = [node EXCEPT ![t] = "waiting"]
            /\ want' = [want EXCEPT ![t] = "read"]
            /\ woken' = [woken EXCEPT ![t] = FALSE]
            /\ pc' = [pc EXCEPT ![t] = "parked"]
            /\ UNCHANGED <<rd, wr, rdepth, wowner, wdepth, wq, wph, bypass, ahead>>
  /\ UNCHANGED <<towake, ret>>

\* write() / write(owner) / try_write. Re-entry under the owner's own
\* write; a task holding only read may not ask (no upgrade); otherwise in at
\* once only when nobody holds or waits; otherwise queue.
Write(t) ==
  /\ pc[t] \in {"idle", "holding"}
  /\ rd[t] + wr[t] < MaxDepth
  /\ IF Kind = "Reentrant" /\ wowner = Owner[t]
       THEN /\ wr' = [wr EXCEPT ![t] = @ + 1]
            /\ wdepth' = wdepth + 1
            /\ pc' = [pc EXCEPT ![t] = "holding"]
            /\ UNCHANGED <<rd, rdepth, wowner, rq, wq, node, want, woken, wph, bypass, ahead>>
       ELSE /\ rd[t] = 0
            /\ IF wowner = NoOwner /\ NoReaders(Lock) /\ wq = <<>> /\ rq = <<>>
                 THEN /\ wr' = [wr EXCEPT ![t] = 1]
                      /\ wowner' = Owner[t]
                      /\ wdepth' = 1
                      /\ pc' = [pc EXCEPT ![t] = "holding"]
                      /\ UNCHANGED <<rd, rdepth, rq, wq, node, want, woken, wph, bypass, ahead>>
                 ELSE /\ wq' = Append(wq, t)
                      /\ node' = [node EXCEPT ![t] = "waiting"]
                      /\ want' = [want EXCEPT ![t] = "write"]
                      /\ woken' = [woken EXCEPT ![t] = FALSE]
                      /\ ahead' = [ahead EXCEPT ![t] = Len(wq)]
                      /\ pc' = [pc EXCEPT ![t] = "parked"]
                      /\ UNCHANGED <<rd, wr, rdepth, wowner, wdepth, rq, wph, bypass>>
  /\ UNCHANGED <<towake, ret>>

\* A read guard drops, and the handoff it triggers happens with it.
ReleaseRead(t) ==
  /\ pc[t] = "holding"
  /\ rd[t] > 0
  /\ LET L1 == DropRead(Lock, t)
         L2 == AfterRead(L1)
     IN /\ Apply(L2)
        /\ Finish(t, Granted(L1, L2), IF L2.rd[t] + L2.wr[t] > 0 THEN "holding" ELSE "idle")
  /\ UNCHANGED <<want, woken>>

\* A write guard drops, and the handoff it triggers happens with it.
ReleaseWrite(t) ==
  /\ pc[t] = "holding"
  /\ wr[t] > 0
  /\ LET L1 == DropWrite(Lock, t)
         L2 == AfterWrite(L1)
     IN /\ Apply(L2)
        /\ Finish(t, Granted(L1, L2), IF L2.rd[t] + L2.wr[t] > 0 THEN "holding" ELSE "idle")
  /\ UNCHANGED <<want, woken>>

\* A task that handed the lock over wakes those it handed to, one per step,
\* after the handoff.
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
  /\ UNCHANGED <<rd, wr, rdepth, wowner, wdepth, rq, wq, node, want, wph, bypass, ahead>>

\* The executor polls a woken future: granted, it holds its guard;
\* otherwise it registers its waker again.
Poll(t) ==
  /\ pc[t] = "parked"
  /\ woken[t]
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  /\ IF node[t] = "granted"
       THEN /\ node' = [node EXCEPT ![t] = "none"]
            /\ pc' = [pc EXCEPT ![t] = "holding"]
       ELSE UNCHANGED <<node, pc>>
  /\ UNCHANGED <<rd, wr, rdepth, wowner, wdepth, rq, wq, want, towake, ret, wph, bypass, ahead>>

\* The pending future is dropped. A waiting node leaves its queue (a writer
\* leaving may let the readers behind it in). A granted one passes its
\* guard on through the same handoff as a release.
Cancel(t) ==
  /\ pc[t] = "parked"
  /\ woken' = [woken EXCEPT ![t] = FALSE]
  /\ LET L0 == [Lock EXCEPT !.node = [@ EXCEPT ![t] = "none"],
                            !.wph = [@ EXCEPT ![t] = 0],
                            !.bypass = [@ EXCEPT ![t] = 0],
                            !.ahead = [@ EXCEPT ![t] = 0]]
         L1 == IF node[t] = "waiting"
                 THEN [L0 EXCEPT !.rq = SelectSeq(@, LAMBDA u : u # t),
                                 !.wq = SelectSeq(@, LAMBDA u : u # t)]
               ELSE IF want[t] = "read" THEN DropRead(L0, t) ELSE DropWrite(L0, t)
         L2 == IF node[t] = "waiting"
                 THEN IF want[t] = "write" THEN AfterWriterLeaves(L1) ELSE L1
               ELSE IF want[t] = "read" THEN AfterRead(L1) ELSE AfterWrite(L1)
     IN /\ Apply(L2)
        /\ Finish(t, Granted(L1, L2), "idle")
  /\ UNCHANGED want

----------------------------------------------------------------------------
\* The specification.

\* The start: nobody holds, nobody waits.
Init ==
  /\ rd = [t \in Tasks |-> 0]
  /\ wr = [t \in Tasks |-> 0]
  /\ rdepth = [o \in Owners |-> 0]
  /\ wowner = NoOwner
  /\ wdepth = 0
  /\ rq = <<>>
  /\ wq = <<>>
  /\ node = [t \in Tasks |-> "none"]
  /\ want = [t \in Tasks |-> "read"]
  /\ woken = [t \in Tasks |-> FALSE]
  /\ towake = [t \in Tasks |-> {}]
  /\ ret = [t \in Tasks |-> "idle"]
  /\ pc = [t \in Tasks |-> "idle"]
  /\ wph = [t \in Tasks |-> 0]
  /\ bypass = [t \in Tasks |-> 0]
  /\ ahead = [t \in Tasks |-> 0]

\* Every step the system can take.
Next ==
  \E t \in Tasks :
    Read(t) \/ Write(t) \/ ReleaseRead(t) \/ ReleaseWrite(t) \/ Wake(t) \/ Poll(t) \/ Cancel(t)

\* Fairness: wakes are delivered, woken futures are polled, and a holder
\* eventually drops a guard. Asking for the lock and cancelling are the
\* caller's choices.
Fairness ==
  \A t \in Tasks :
    /\ WF_vars(Wake(t) \/ Poll(t))
    /\ WF_vars(ReleaseRead(t) \/ ReleaseWrite(t))

\* Every behaviour: start in Init, take Next steps or stutter, fairly.
Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ rd \in [Tasks -> 0..MaxDepth]
  /\ wr \in [Tasks -> 0..MaxDepth]
  /\ rdepth \in [Owners -> Nat]
  /\ wowner \in Owners \cup {NoOwner}
  /\ node \in [Tasks -> {"none", "waiting", "granted"}]
  /\ want \in [Tasks -> {"read", "write"}]
  /\ pc \in [Tasks -> {"idle", "holding", "parked", "wake"}]
  /\ Range(rq) \subseteq Tasks /\ Range(wq) \subseteq Tasks

\* MUTUAL EXCLUSION. While an owner holds write, no other owner holds read
\* or write; and every guard a task holds is counted on the lock.
MutualExclusion ==
  /\ wowner # NoOwner => \A o \in Owners \ {wowner} : rdepth[o] = 0
  /\ \A t \in Tasks : wr[t] > 0 => Owner[t] = wowner
  /\ \A t \in Tasks : rd[t] > 0 => rdepth[Owner[t]] > 0

\* REENTRANCY DEPTH. The lock's depths are exactly the guards out, and
\* write is held exactly when its depth is not 0.
ReentrancyDepth ==
  /\ wdepth = SumOf(wr, Tasks)
  /\ \A o \in Owners :
       rdepth[o] = SumOf(rd, {t \in Tasks : Owner[t] = o})
  /\ (wowner = NoOwner <=> wdepth = 0)

\* PHASE FAIRNESS, readers. A waiting reader sees at most one write phase
\* begin before it is admitted.
ReadersWaitOnePhase ==
  \A t \in Tasks : WaitsFor(Lock, t, "read") => wph[t] <= 1

\* PHASE FAIRNESS, writers. A waiting writer sees readers admitted only in
\* the batches that end the write phases ahead of it: at most one batch per
\* writer ahead, plus one for the phase in progress.
WritersBoundedBypass ==
  \A t \in Tasks :
    WaitsFor(Lock, t, "write") => bypass[t] <= (ahead[t] + 1) * (Cardinality(Tasks) - 1)

\* NO SELF-DEADLOCK. A task never waits on the lock while it holds a guard
\* of it: whatever it waits for would need its own guard to drop.
NoSelfDeadlock ==
  \A t \in Tasks : node[t] = "waiting" => rd[t] + wr[t] = 0

\* A queued task that nobody will ever hand the lock to: readers queued
\* with no writer holding or waiting, or a writer queued while nobody holds.
Stranded ==
  \/ rq # <<>> /\ wowner = NoOwner /\ wq = <<>>
  \/ wq # <<>> /\ wowner = NoOwner /\ NoReaders(Lock)

\* NO LOST WAKEUP. A parked future handed the lock has been woken or is
\* about to be, and no queued task is stranded.
NoLostWakeup ==
  /\ \A t \in Tasks :
       pc[t] = "parked" /\ node[t] = "granted" =>
         woken[t] \/ \E d \in Tasks : t \in towake[d]
  /\ ~Stranded

\* CANCELLATION PASSES ON. An idle task holds no guard.
CancelPassesOn == \A t \in Tasks : pc[t] = "idle" => rd[t] + wr[t] = 0

----------------------------------------------------------------------------
\* Liveness.

\* Liveness is checked for the tasks in Watched only. Tasks with the same
\* Owner role are interchangeable: renaming them (and their owners) maps
\* every behaviour to a behaviour, a starving one to a starving one, so one
\* task of each role covers all, at a fraction of TLC's liveness cost.

\* Every parked waiter stops waiting: it is served, unless it cancels.
EveryWaiterServed == \A t \in Watched : (pc[t] = "parked") ~> (pc[t] # "parked")

\* Owner o holds the lock in some mode.
OwnerHolds(o) == rdepth[o] > 0 \/ wowner = o

\* Reentrant: no owner keeps the lock forever.
OwnersLetGo == \A o \in Owners : []<>(~OwnerHolds(o))

\* Reentrant: if no owner holds the lock forever, every waiter is served.
ReentrantServed == OwnersLetGo => EveryWaiterServed

====
