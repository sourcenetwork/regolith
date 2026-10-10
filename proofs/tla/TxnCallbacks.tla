---- MODULE TxnCallbacks ----
\* Transaction callbacks (plan 3.16, D44): before_commit, on_commit,
\* on_abort and the database-wide TransactionHooks, for transactions run by
\* `transact` (3.10) and completed on the committing thread (the queue's
\* poll or drop), by `close` or by the owner.
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/Callbacks.lean:
\*   step_inv, reachable_inv   the outcome machine's invariant holds in
\*                             every reachable state
\*   exactly_once, never_both  every callback of an ended attempt ran
\*                             exactly once, of the kind its outcome names,
\*                             and none of the other kind
\*                             (AtMostOnce, ExactlyOnce here)
\*   order,                    before_commit callbacks, then the hooks'
\*   callbacks_before_hooks,   before_commit, then validation, then the
\*   commit_was_validated      transaction's outcome callbacks, then the
\*                             hooks' (CallbacksBeforeHooks here)
\*   finish_commit_runs,       the outcome callbacks run in registration
\*   finish_abort_runs         order, the hooks' after them
\*   before_writes_validated   the validated write set holds every write
\*                             the before_commit callbacks made
\*                             (NoLostUpdate here)
\*   attempts_isolated         an attempt's outcome runs only that
\*                             attempt's callbacks (AttemptIsolation here)
\*   panic_aborts              a panic in before_commit ends the attempt
\*                             aborted, with its on_abort run (PanicAborts)
\*   surviving_callbacks_break_isolation   the RED case, as a counterexample
\*   delivered_once            however many paths try to deliver a decided
\*                             outcome, one CAS lets one of them run it
\*                             (AtMostOnce here, for the delivery paths)
\*   delivered_on_queue_thread every delivery runs on the thread that holds
\*                             the commit's queue (OnCommittingThread here)
\*   no_claim_delivers_twice   the RED case DeliverNoClaim, as a
\*                             counterexample
\* TLC checks the concurrent machine here: two transact calls, two
\* committers that decide and sync, the committing threads that deliver
\* each outcome, and close, for two attempts each.
\*
\* THE DESIGN (plan 3.16).
\*   - Exactly one outcome. For every transaction, exactly one of on_commit
\*     or on_abort runs, once per registered callback, however the outcome
\*     arrives: a ticket, close or a drop.
\*   - On the committing thread (D53). A committed or conflicted outcome is
\*     delivered, and its callbacks run, only on the thread that owns the
\*     commit's queue: at that queue's poll, or when the queue is dropped
\*     (on the dropping thread, which then holds it). Never on a committer
\*     that decided it or synced it. Close runs only the on_abort of
\*     transactions still open, on the closing thread; the owner's own
\*     rollback, drop or error runs on the owner's thread.
\*   - Order. At commit, the transaction's before_commit callbacks run, then
\*     the database hooks', then validation; a write a callback makes is
\*     part of the commit and is validated. After the outcome, the
\*     transaction's callbacks run first, then the hooks'.
\*   - Attempts. Callbacks belong to one attempt. On a conflict under
\*     `transact`, that attempt's on_abort callbacks run with the Conflict,
\*     its on_commit callbacks are dropped, and the re-run registers its own.
\*   - on_commit runs when the commit is visible, and durable at Immediate.
\*   - A panic in before_commit fails the commit with CallbackPanicked and
\*     runs on_abort.
\*   - close runs the on_abort callbacks of transactions still open, and
\*     resolves the tickets its final sync covers.
\*
\* THE MECHANISM MODELLED for exactly-once: two claims, each one CAS.
\*   - The transaction's state word: "open" is CAS'd once, to "committing"
\*     by its owner's commit or to "aborted" by a rollback, a drop, an
\*     error or close. Whoever loses the CAS runs nothing: a commit that
\*     finds the transaction aborted by close returns Closed.
\*   - The commit's outcome word (the ticket's Completion): once the
\*     pipeline decides it, "decided" is CAS'd once to "claimed" by the path
\*     that delivers it, the queue's poll or the queue's drop, both on the
\*     queue holder's thread; only the winner runs callbacks.
\*
\* THE WORKLOAD. Each transaction's body writes a key of its own; its
\* before_commit callback reads a shared counter at the transaction's
\* snapshot and writes it plus one. Validation is first-committer-wins on
\* the validated write set. So the counter equals the number of commits
\* exactly when every callback write is validated.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - One callback of each kind per attempt. With any number of them,
\*     Callbacks.lean proves the outcome callbacks run in registration
\*     order (finish_commit_runs, finish_abort_runs). That before_commit
\*     callbacks run oldest first holds by construction of its runBefore
\*     step; no theorem restates it.
\*   - Rollback, drop and an Err from the closure are one transition (the
\*     owner claims "aborted" and runs on_abort); an Err from before_commit
\*     is the panic transition without the panic flag.
\*   - The pipeline decides one transaction per step; group commit and the
\*     visibility order are GroupCommit.tla's and CommitPipeline.tla's.
\*
\* CONFIGURATIONS.
\*   MC_TxnCallbacks_Green_Immediate   two transact calls, two committers,
\*                                     delivery by poll or drop, close, at
\*                                     Immediate: every invariant, and
\*                                     everything settles.
\*   MC_TxnCallbacks_Green_Eventual    the same at Eventual.
\*   MC_TxnCallbacks_Red_CommitBeforeDurable  on_commit runs before the
\*                                     fsync at Immediate: CommitAfterDurable.
\*   MC_TxnCallbacks_Red_SkipCallbackWrites   validation uses the write
\*                                     set captured before before_commit
\*                                     ran: NoLostUpdate.
\*   MC_TxnCallbacks_Red_CallbacksSurvive     a conflicted attempt's
\*                                     callbacks stay registered for the
\*                                     re-run: AttemptIsolation.
\*   MC_TxnCallbacks_Red_DeliverNoClaim the poll and the drop deliver without
\*                                     claiming the outcome: both run it,
\*                                     AtMostOnce.
\*   MC_TxnCallbacks_Red_HelperDelivers a committer delivers the outcome it
\*                                     decided, as before D53: the callbacks
\*                                     run off the committing thread,
\*                                     OnCommittingThread.
\*   MC_TxnCallbacks_Red_CloseNoClaim  close aborts without claiming the
\*                                     transaction, and its commit goes on:
\*                                     AtMostOnce.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Owners,       \* the tasks each running one `transact` call: naturals
  Committers,   \* the threads that decide and complete commits: naturals
  MaxAttempts,  \* RetryPolicy::max_attempts
  Durability,   \* "Immediate" or "Eventual"
  Mutant        \* "none" for the design, or the name of one defect

ASSUME MaxAttempts \in Nat \ {0}
ASSUME Durability \in {"Immediate", "Eventual"}
ASSUME Mutant \in {"none", "CommitBeforeDurable", "SkipCallbackWrites",
                   "CallbacksSurvive", "DeliverNoClaim", "HelperDelivers",
                   "CloseNoClaim"}

\* The two ways a commit's outcome reaches its ticket, both on the thread
\* that holds the commit's queue: that queue's poll, or the queue's drop.
Paths == {"poll", "drop"}

\* Attempt numbers.
Attempts == 1..MaxAttempts

\* The value "no owner".
NoOwner == 0
ASSUME NoOwner \notin Owners

VARIABLES
  \* The database.
  seq,       \* the last commit sequence
  durable,   \* the sequence the WAL is synced through
  ctr,       \* the shared counter's committed value
  ctrSeq,    \* the sequence of the counter's last committed write
  closed,    \* close has begun: no transaction begins or submits after it
  \* Each owner's current attempt.
  att,       \* [Owners -> 0..MaxAttempts]: the current attempt, 0 before the first
  opc,       \* [Owners -> pc]: where the owner is
  ost,       \* [Owners -> {"open", "committing", "aborted"}]: the state word
  snap,      \* [Owners -> Nat]: the attempt's snapshot sequence
  readv,     \* [Owners -> Nat]: the counter as the snapshot reads it
  buf,       \* [Owners -> SUBSET {"own", "ctr"}]: the keys the attempt writes
  vset,      \* [Owners -> SUBSET {"own", "ctr"}]: the keys validation checks
  reg,       \* [Owners -> SUBSET Attempts]: whose callbacks the transaction holds
  ps,        \* [Owners -> {"none", "queued", "decided", "claimed", "resolved"}]
  verdict,   \* [Owners -> {"none", "commit", "conflict"}]
  cseq,      \* [Owners -> Nat]: the commit's sequence
  \* The pipeline, the committers and the closer.
  subq,      \* submitted transactions, in order
  cpc,       \* [Committers -> {"idle", "callbacks", "hooks"}]
  ctarget,   \* [Committers -> Owners \cup {NoOwner}]: the outcome being completed
  clpc,      \* the closer: "idle", "closing", "clcb", "clhook" or "closed"
  cltarget,  \* the transaction the closer is aborting
  clseen,    \* the transactions the closer has handled
  \* Ghosts, per owner and attempt.
  ranC,      \* [Owners -> [Attempts -> Nat]]: runs of the attempt's on_commit
  ranA,      \* [Owners -> [Attempts -> Nat]]: runs of the attempt's on_abort
  hookC,     \* [Owners -> [Attempts -> Nat]]: runs of the hooks' on_commit
  hookA,     \* [Owners -> [Attempts -> Nat]]: runs of the hooks' on_abort
  beforeRan, \* [Owners -> [Attempts -> BOOLEAN]]: its before_commit ran
  hookBefore,\* [Owners -> [Attempts -> BOOLEAN]]: the hooks' before_commit ran
  validated, \* [Owners -> [Attempts -> BOOLEAN]]: validation ran
  committed, \* [Owners -> [Attempts -> BOOLEAN]]: the attempt committed
  panicked,  \* [Owners -> [Attempts -> BOOLEAN]]: its before_commit panicked
  ranFor,    \* <<owner, callback's attempt, outcome's attempt>> for every run
  \* The delivery of each owner's outcome, per path.
  dpc,       \* [Owners -> [Paths -> {"idle", "callbacks", "hooks"}]]: where it is
  \* A ghost: who ran each set of outcome callbacks.
  runBy      \* <<owner, runner>>: "poll", "drop", "owner", "closer" or "committer"

\* Every variable, so a step that changes none of them is a stutter.
vars == <<seq, durable, ctr, ctrSeq, closed, att, opc, ost, snap, readv, buf,
          vset, reg, ps, verdict, cseq, subq, cpc, ctarget, clpc, cltarget,
          clseen, ranC, ranA, hookC, hookA, beforeRan, hookBefore, validated,
          committed, panicked, ranFor, runBy, dpc>>

\* The ghosts, grouped so steps that leave them alone say so briefly.
ghosts == <<ranC, ranA, hookC, hookA, beforeRan, hookBefore, validated,
            committed, panicked, ranFor, runBy>>
\* The owners' attempt state.
owner == <<att, opc, ost, snap, readv, buf, vset, reg, ps, verdict, cseq>>
\* The database words.
db == <<seq, durable, ctr, ctrSeq, closed>>
\* The committers' and the closer's state.
workers == <<subq, cpc, ctarget, clpc, cltarget, clseen, dpc>>

----------------------------------------------------------------------------
\* Helpers.

\* Set g[x][a] to v.
Set2(g, x, a, v) == [g EXCEPT ![x][a] = v]

\* Add 1 to g[x][b] for every attempt b in B.
Bump(g, x, B) == [g EXCEPT ![x] = [b \in Attempts |-> IF b \in B THEN g[x][b] + 1 ELSE g[x][b]]]

\* Run the transaction's on_commit (kind "C") or on_abort (kind "A")
\* callbacks on the thread `who`: every callback it holds runs once, and
\* each run is recorded with the attempt whose outcome it reports.
RunCallbacks(x, kind, who) ==
  \* The callbacks of the kind run, one more time each.
  /\ IF kind = "C"
       THEN ranC' = Bump(ranC, x, reg[x]) /\ UNCHANGED ranA
       ELSE ranA' = Bump(ranA, x, reg[x]) /\ UNCHANGED ranC
  \* Each run is recorded with the outcome's attempt.
  /\ ranFor' = ranFor \cup {<<x, b, att[x]>> : b \in reg[x]}
  \* And with the thread that ran it.
  /\ runBy' = runBy \cup {<<x, who>>}

\* Run the hooks' on_commit or on_abort for x's current attempt.
RunHook(x, kind) ==
  IF kind = "C"
    THEN hookC' = Bump(hookC, x, {att[x]}) /\ UNCHANGED hookA
    ELSE hookA' = Bump(hookA, x, {att[x]}) /\ UNCHANGED hookC

----------------------------------------------------------------------------
\* The owner: one `transact` call, attempt after attempt.

\* begin: a fresh transaction for the next attempt, with a snapshot, and
\* its three callbacks registered. After close begins, begin fails with
\* Closed and nothing is registered. Mutant CallbacksSurvive: the earlier
\* attempts' callbacks stay registered on the re-run.
Begin(x) ==
  /\ opc[x] = "begin"
  /\ IF closed
       THEN /\ opc' = [opc EXCEPT ![x] = "done"]
            /\ UNCHANGED <<att, ost, snap, readv, buf, vset, reg, ps, verdict, cseq>>
       ELSE /\ att' = [att EXCEPT ![x] = @ + 1]
            /\ snap' = [snap EXCEPT ![x] = seq]
            /\ readv' = [readv EXCEPT ![x] = ctr]
            /\ reg' = [reg EXCEPT ![x] =
                         IF Mutant = "CallbacksSurvive" THEN @ \cup {att[x] + 1} ELSE {att[x] + 1}]
            /\ buf' = [buf EXCEPT ![x] = {"own"}]
            /\ vset' = [vset EXCEPT ![x] = {}]
            /\ ost' = [ost EXCEPT ![x] = "open"]
            /\ ps' = [ps EXCEPT ![x] = "none"]
            /\ verdict' = [verdict EXCEPT ![x] = "none"]
            /\ cseq' = [cseq EXCEPT ![x] = 0]
            /\ opc' = [opc EXCEPT ![x] = "open"]
  /\ UNCHANGED <<db, workers, ghosts>>

\* The closure returns Ok and the owner commits: CAS the state word from
\* "open" to "committing". If close already claimed it, the commit returns
\* Closed and runs nothing: close runs the on_abort callbacks.
OwnerCommit(x) ==
  /\ opc[x] = "open"
  /\ IF ost[x] = "open"
       THEN ost' = [ost EXCEPT ![x] = "committing"] /\ opc' = [opc EXCEPT ![x] = "before"]
       ELSE opc' = [opc EXCEPT ![x] = "done"] /\ UNCHANGED ost
  /\ UNCHANGED <<att, snap, readv, buf, vset, reg, ps, verdict, cseq, db, workers, ghosts>>

\* The transaction ends without committing on its owner's side: rollback,
\* a drop, or an Err from the closure (not retried). CAS "open" to
\* "aborted"; the winner runs on_abort. If close claimed it, it is done.
OwnerAbort(x) ==
  /\ opc[x] = "open"
  /\ IF ost[x] = "open"
       THEN ost' = [ost EXCEPT ![x] = "aborted"] /\ opc' = [opc EXCEPT ![x] = "abortcb"]
       ELSE opc' = [opc EXCEPT ![x] = "done"] /\ UNCHANGED ost
  /\ UNCHANGED <<att, snap, readv, buf, vset, reg, ps, verdict, cseq, db, workers, ghosts>>

\* The transaction's before_commit runs on the committing thread: it reads
\* the counter at the snapshot and writes it plus one, through the
\* transaction.
BeforeOk(x) ==
  /\ opc[x] = "before"
  /\ buf' = [buf EXCEPT ![x] = @ \cup {"ctr"}]
  /\ beforeRan' = Set2(beforeRan, x, att[x], TRUE)
  /\ opc' = [opc EXCEPT ![x] = "hook"]
  /\ UNCHANGED <<att, ost, snap, readv, vset, reg, ps, verdict, cseq, db, workers>>
  /\ UNCHANGED <<ranC, ranA, hookC, hookA, hookBefore, validated, committed, panicked, ranFor, runBy>>

\* The transaction's before_commit panics: the commit fails with
\* CallbackPanicked and the attempt goes to on_abort.
BeforePanic(x) ==
  /\ opc[x] = "before"
  /\ beforeRan' = Set2(beforeRan, x, att[x], TRUE)
  /\ panicked' = Set2(panicked, x, att[x], TRUE)
  /\ opc' = [opc EXCEPT ![x] = "abortcb"]
  /\ UNCHANGED <<att, ost, snap, readv, buf, vset, reg, ps, verdict, cseq, db, workers>>
  /\ UNCHANGED <<ranC, ranA, hookC, hookA, hookBefore, validated, committed, ranFor, runBy>>

\* The hooks' before_commit runs after the transaction's; then the write
\* set to validate is fixed: every write the transaction holds, the
\* callbacks' included. Mutant SkipCallbackWrites: the set captured before
\* the callbacks ran.
HookBefore(x) ==
  /\ opc[x] = "hook"
  /\ hookBefore' = Set2(hookBefore, x, att[x], TRUE)
  /\ vset' = [vset EXCEPT ![x] = IF Mutant = "SkipCallbackWrites" THEN {"own"} ELSE buf[x]]
  /\ opc' = [opc EXCEPT ![x] = "submit"]
  /\ UNCHANGED <<att, ost, snap, readv, buf, reg, ps, verdict, cseq, db, workers>>
  /\ UNCHANGED <<ranC, ranA, hookC, hookA, beforeRan, validated, committed, panicked, ranFor, runBy>>

\* commit_nowait: submit to the pipeline, or, once close has begun, fail
\* with Closed and go to on_abort (one atomic admission check).
Submit(x) ==
  /\ opc[x] = "submit"
  /\ IF closed
       THEN /\ opc' = [opc EXCEPT ![x] = "abortcb"]
            /\ UNCHANGED <<subq, ps>>
       ELSE /\ subq' = Append(subq, x)
            /\ ps' = [ps EXCEPT ![x] = "queued"]
            /\ opc' = [opc EXCEPT ![x] = "waiting"]
  /\ UNCHANGED <<att, ost, snap, readv, buf, vset, reg, verdict, cseq, db>>
  /\ UNCHANGED <<cpc, ctarget, clpc, cltarget, clseen, dpc, ghosts>>

\* The owner's thread runs the transaction's on_abort callbacks.
OwnerAbortCallbacks(x) ==
  /\ opc[x] = "abortcb"
  /\ RunCallbacks(x, "A", "owner")
  /\ opc' = [opc EXCEPT ![x] = "aborthook"]
  /\ UNCHANGED <<att, ost, snap, readv, buf, vset, reg, ps, verdict, cseq, db, workers>>
  /\ UNCHANGED <<hookC, hookA, beforeRan, hookBefore, validated, committed, panicked>>

\* Then the hooks' on_abort; the transact call ends (not retried).
OwnerAbortHook(x) ==
  /\ opc[x] = "aborthook"
  /\ RunHook(x, "A")
  /\ opc' = [opc EXCEPT ![x] = "done"]
  /\ UNCHANGED <<att, ost, snap, readv, buf, vset, reg, ps, verdict, cseq, db, workers>>
  /\ UNCHANGED <<ranC, ranA, beforeRan, hookBefore, validated, committed, panicked, ranFor, runBy>>

\* The committing thread delivers its decided outcome along path p: its
\* queue's poll takes the "done" note, or its queue is dropped and the drop
\* delivers what the queue held. It claims the outcome with one CAS,
\* "decided" to "claimed". A commit at Immediate is delivered only once
\* durable (its group landed: synced, then applied and published). Mutant
\* CommitBeforeDurable: at once. Mutant DeliverNoClaim: without the CAS, so
\* the other path may deliver it too.
Deliver(x, p) ==
  \* The transaction waits for its ticket.
  /\ opc[x] = "waiting"
  \* The pipeline decided it.
  /\ ps[x] = "decided"
  \* This path is not delivering already.
  /\ dpc[x][p] = "idle"
  \* A conflict is told at once; a commit once its group landed.
  /\ \/ verdict[x] = "conflict"
     \/ Durability = "Eventual"
     \/ durable >= cseq[x]
     \/ Mutant = "CommitBeforeDurable"
  \* The CAS: the outcome is claimed (the bug leaves it to be claimed again).
  /\ ps' = [ps EXCEPT ![x] = IF Mutant = "DeliverNoClaim" THEN @ ELSE "claimed"]
  \* This path runs the callbacks next.
  /\ dpc' = [dpc EXCEPT ![x][p] = "callbacks"]
  \* Nothing else changes.
  /\ UNCHANGED <<db, att, opc, ost, snap, readv, buf, vset, reg, verdict, cseq>>
  \* The pipeline, the committers and the closer are untouched.
  /\ UNCHANGED <<subq, cpc, ctarget, clpc, cltarget, clseen, ghosts>>

\* The delivering path runs the transaction's callbacks of the outcome's
\* kind, on the committing thread.
DeliverCallbacks(x, p) ==
  \* This path claimed the outcome.
  /\ dpc[x][p] = "callbacks"
  \* The callbacks run here, recorded as run by this path.
  /\ RunCallbacks(x, IF verdict[x] = "commit" THEN "C" ELSE "A", p)
  \* The hooks are next.
  /\ dpc' = [dpc EXCEPT ![x][p] = "hooks"]
  \* Nothing else changes.
  /\ UNCHANGED <<db, owner, subq, cpc, ctarget, clpc, cltarget, clseen>>
  \* The other ghosts are untouched.
  /\ UNCHANGED <<hookC, hookA, beforeRan, hookBefore, validated, committed, panicked>>

\* Then the hooks', and the ticket is ready.
DeliverHooks(x, p) ==
  \* This path ran the callbacks.
  /\ dpc[x][p] = "hooks"
  \* The hooks' outcome runs.
  /\ RunHook(x, IF verdict[x] = "commit" THEN "C" ELSE "A")
  \* The ticket is ready.
  /\ ps' = [ps EXCEPT ![x] = "resolved"]
  \* The path is done.
  /\ dpc' = [dpc EXCEPT ![x][p] = "idle"]
  \* Nothing else changes.
  /\ UNCHANGED <<db, att, opc, ost, snap, readv, buf, vset, reg, verdict, cseq>>
  \* The pipeline, the committers and the closer are untouched.
  /\ UNCHANGED <<subq, cpc, ctarget, clpc, cltarget, clseen>>
  \* The other ghosts are untouched.
  /\ UNCHANGED <<ranC, ranA, beforeRan, hookBefore, validated, committed, panicked, ranFor, runBy>>

\* The ticket resolves. A commit ends the transact call; a conflict re-runs
\* the closure in a fresh attempt while attempts remain (Exhausted after).
Resolve(x) ==
  /\ opc[x] = "waiting"
  /\ ps[x] = "resolved"
  /\ opc' = [opc EXCEPT ![x] =
               IF verdict[x] = "conflict" /\ att[x] < MaxAttempts THEN "begin" ELSE "done"]
  /\ UNCHANGED <<att, ost, snap, readv, buf, vset, reg, ps, verdict, cseq, db, workers, ghosts>>

----------------------------------------------------------------------------
\* The committers: decide and sync. They never deliver an outcome: that is
\* the committing thread's (Deliver). Mutant HelperDelivers puts back the
\* design before D53, where any committer completed any decided outcome.

\* Validate the oldest submitted transaction, first-committer-wins on its
\* validated write set, and apply it if it commits.
Decide(c) ==
  /\ cpc[c] = "idle"
  /\ subq # <<>>
  /\ LET x == Head(subq)
         conflict == "ctr" \in vset[x] /\ ctrSeq > snap[x]
     IN /\ subq' = Tail(subq)
        /\ validated' = Set2(validated, x, att[x], TRUE)
        /\ ps' = [ps EXCEPT ![x] = "decided"]
        /\ IF conflict
             THEN /\ verdict' = [verdict EXCEPT ![x] = "conflict"]
                  /\ UNCHANGED <<seq, ctr, ctrSeq, cseq, committed>>
             ELSE /\ verdict' = [verdict EXCEPT ![x] = "commit"]
                  /\ seq' = seq + 1
                  /\ cseq' = [cseq EXCEPT ![x] = seq + 1]
                  /\ IF "ctr" \in buf[x]
                       THEN ctr' = readv[x] + 1 /\ ctrSeq' = seq + 1
                       ELSE UNCHANGED <<ctr, ctrSeq>>
                  /\ committed' = Set2(committed, x, att[x], TRUE)
  /\ UNCHANGED <<durable, closed, att, opc, ost, snap, readv, buf, vset, reg>>
  /\ UNCHANGED <<cpc, ctarget, clpc, cltarget, clseen, dpc>>
  /\ UNCHANGED <<ranC, ranA, hookC, hookA, beforeRan, hookBefore, panicked, ranFor, runBy>>

\* A WAL sync: everything committed so far is durable.
Fsync(c) ==
  /\ cpc[c] = "idle"
  /\ durable < seq
  /\ durable' = seq
  /\ UNCHANGED <<seq, ctr, ctrSeq, closed, owner, workers, ghosts>>

\* Mutant HelperDelivers only: a committer claims a decided outcome, CAS
\* "decided" to "claimed", to complete it on its own thread.
Claim(c, x) ==
  \* Only the planted bug lets a committer deliver.
  /\ Mutant = "HelperDelivers"
  /\ cpc[c] = "idle"
  /\ ps[x] = "decided"
  /\ \/ verdict[x] = "conflict"
     \/ Durability = "Eventual"
     \/ durable >= cseq[x]
  /\ ps' = [ps EXCEPT ![x] = "claimed"]
  /\ cpc' = [cpc EXCEPT ![c] = "callbacks"]
  /\ ctarget' = [ctarget EXCEPT ![c] = x]
  /\ UNCHANGED <<db, att, opc, ost, snap, readv, buf, vset, reg, verdict, cseq>>
  /\ UNCHANGED <<subq, clpc, cltarget, clseen, dpc, ghosts>>

\* The claimer runs the transaction's callbacks of the outcome's kind.
CommitterCallbacks(c) ==
  /\ cpc[c] = "callbacks"
  /\ LET x == ctarget[c] IN RunCallbacks(x, IF verdict[x] = "commit" THEN "C" ELSE "A", "committer")
  /\ cpc' = [cpc EXCEPT ![c] = "hooks"]
  /\ UNCHANGED <<db, owner, subq, ctarget, clpc, cltarget, clseen, dpc>>
  /\ UNCHANGED <<hookC, hookA, beforeRan, hookBefore, validated, committed, panicked>>

\* Then the hooks', and the ticket resolves, waking the owner.
CommitterHooks(c) ==
  /\ cpc[c] = "hooks"
  /\ LET x == ctarget[c] IN
       /\ RunHook(x, IF verdict[x] = "commit" THEN "C" ELSE "A")
       /\ ps' = [ps EXCEPT ![x] = "resolved"]
  /\ cpc' = [cpc EXCEPT ![c] = "idle"]
  /\ ctarget' = [ctarget EXCEPT ![c] = NoOwner]
  /\ UNCHANGED <<db, att, opc, ost, snap, readv, buf, vset, reg, verdict, cseq>>
  /\ UNCHANGED <<subq, clpc, cltarget, clseen, dpc>>
  /\ UNCHANGED <<ranC, ranA, beforeRan, hookBefore, validated, committed, panicked, ranFor, runBy>>

----------------------------------------------------------------------------
\* close.

\* close begins: from now on nothing begins or submits.
Close ==
  /\ clpc = "idle"
  /\ closed' = TRUE
  /\ clpc' = "closing"
  /\ UNCHANGED <<seq, durable, ctr, ctrSeq, owner, subq, cpc, ctarget, cltarget, clseen, dpc, ghosts>>

\* close aborts a transaction still open: CAS "open" to "aborted", then
\* run its on_abort. Mutant CloseNoClaim: no CAS, so its owner may still
\* commit it.
CloseAbort(x) ==
  /\ clpc = "closing"
  /\ x \notin clseen
  /\ opc[x] = "open"
  /\ ost[x] = "open"
  /\ ost' = [ost EXCEPT ![x] = IF Mutant = "CloseNoClaim" THEN @ ELSE "aborted"]
  /\ clseen' = clseen \cup {x}
  /\ clpc' = "clcb"
  /\ cltarget' = x
  /\ UNCHANGED <<db, att, opc, snap, readv, buf, vset, reg, ps, verdict, cseq>>
  \* No delivery changes either.
  /\ UNCHANGED <<subq, cpc, ctarget, ghosts, dpc>>

\* The closer runs the aborted transaction's on_abort callbacks.
CloseCallbacks ==
  /\ clpc = "clcb"
  /\ RunCallbacks(cltarget, "A", "closer")
  /\ clpc' = "clhook"
  /\ UNCHANGED <<db, owner, subq, cpc, ctarget, cltarget, clseen, dpc>>
  /\ UNCHANGED <<hookC, hookA, beforeRan, hookBefore, validated, committed, panicked>>

\* Then the hooks' on_abort.
CloseHook ==
  /\ clpc = "clhook"
  /\ RunHook(cltarget, "A")
  /\ clpc' = "closing"
  /\ UNCHANGED <<db, owner, subq, cpc, ctarget, cltarget, clseen, dpc>>
  /\ UNCHANGED <<ranC, ranA, beforeRan, hookBefore, validated, committed, panicked, ranFor, runBy>>

\* No open transaction is left to abort: the final sync, and close is done.
CloseFinish ==
  /\ clpc = "closing"
  /\ ~\E x \in Owners : x \notin clseen /\ opc[x] = "open" /\ ost[x] = "open"
  /\ durable' = seq
  /\ clpc' = "closed"
  /\ UNCHANGED <<seq, ctr, ctrSeq, closed, owner, subq, cpc, ctarget, cltarget, clseen, dpc, ghosts>>

----------------------------------------------------------------------------
\* The specification.

\* The start: an empty database, every owner about to begin attempt 1.
Init ==
  /\ seq = 0 /\ durable = 0 /\ ctr = 0 /\ ctrSeq = 0 /\ closed = FALSE
  /\ att = [x \in Owners |-> 0]
  /\ opc = [x \in Owners |-> "begin"]
  /\ ost = [x \in Owners |-> "open"]
  /\ snap = [x \in Owners |-> 0]
  /\ readv = [x \in Owners |-> 0]
  /\ buf = [x \in Owners |-> {}]
  /\ vset = [x \in Owners |-> {}]
  /\ reg = [x \in Owners |-> {}]
  /\ ps = [x \in Owners |-> "none"]
  /\ verdict = [x \in Owners |-> "none"]
  /\ cseq = [x \in Owners |-> 0]
  /\ subq = <<>>
  /\ cpc = [c \in Committers |-> "idle"]
  /\ ctarget = [c \in Committers |-> NoOwner]
  /\ clpc = "idle" /\ cltarget = NoOwner /\ clseen = {}
  /\ ranC = [x \in Owners |-> [a \in Attempts |-> 0]]
  /\ ranA = [x \in Owners |-> [a \in Attempts |-> 0]]
  /\ hookC = [x \in Owners |-> [a \in Attempts |-> 0]]
  /\ hookA = [x \in Owners |-> [a \in Attempts |-> 0]]
  /\ beforeRan = [x \in Owners |-> [a \in Attempts |-> FALSE]]
  /\ hookBefore = [x \in Owners |-> [a \in Attempts |-> FALSE]]
  /\ validated = [x \in Owners |-> [a \in Attempts |-> FALSE]]
  /\ committed = [x \in Owners |-> [a \in Attempts |-> FALSE]]
  /\ panicked = [x \in Owners |-> [a \in Attempts |-> FALSE]]
  /\ ranFor = {}
  \* No path is delivering anything.
  /\ dpc = [x \in Owners |-> [p \in Paths |-> "idle"]]
  \* Nobody ran any callback.
  /\ runBy = {}

\* An owner's step. Its closure ends one way or another, and its commit
\* runs to an outcome, delivered on its own thread: all of these happen.
OwnerStep(x) ==
  \/ Begin(x) \/ OwnerCommit(x) \/ OwnerAbort(x) \/ BeforeOk(x) \/ BeforePanic(x)
  \/ HookBefore(x) \/ Submit(x) \/ OwnerAbortCallbacks(x) \/ OwnerAbortHook(x) \/ Resolve(x)
  \* Delivery of the ticket, by the queue's poll or the queue's drop.
  \/ \E p \in Paths : Deliver(x, p) \/ DeliverCallbacks(x, p) \/ DeliverHooks(x, p)

\* A committer's step.
CommitterStep(c) ==
  \/ Decide(c) \/ Fsync(c) \/ \E x \in Owners : Claim(c, x)
  \/ CommitterCallbacks(c) \/ CommitterHooks(c)

\* The closer's steps once close has begun.
CloserStep == (\E x \in Owners : CloseAbort(x)) \/ CloseCallbacks \/ CloseHook \/ CloseFinish

\* Every step the system can take.
Next ==
  \/ \E x \in Owners : OwnerStep(x)
  \/ \E c \in Committers : CommitterStep(c)
  \/ Close \/ CloserStep

\* Fairness: owners, committers and a started close all make progress.
\* Calling close at all is the caller's choice.
Fairness ==
  /\ \A x \in Owners : WF_vars(OwnerStep(x))
  /\ \A c \in Committers : WF_vars(CommitterStep(c))
  /\ WF_vars(CloserStep)

\* Every behaviour: start in Init, take Next steps or stutter, fairly.
Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ att \in [Owners -> 0..MaxAttempts]
  /\ ost \in [Owners -> {"open", "committing", "aborted"}]
  /\ ps \in [Owners -> {"none", "queued", "decided", "claimed", "resolved"}]
  /\ verdict \in [Owners -> {"none", "commit", "conflict"}]
  /\ cpc \in [Committers -> {"idle", "callbacks", "hooks"}]
  /\ clpc \in {"idle", "closing", "clcb", "clhook", "closed"}
  \* Each delivery path is idle, or running callbacks, or the hooks.
  /\ dpc \in [Owners -> [Paths -> {"idle", "callbacks", "hooks"}]]

\* AT MOST ONCE. No attempt's callbacks run twice or both ways, and the
\* hooks' outcome runs at most once per attempt. Lean: exactly_once.
AtMostOnce ==
  \A x \in Owners, a \in Attempts :
    /\ ranC[x][a] + ranA[x][a] <= 1
    /\ hookC[x][a] + hookA[x][a] <= 1

\* Nothing is in flight: every transact call returned and every worker is
\* idle.
AllSettled ==
  /\ \A x \in Owners : opc[x] = "done"
  /\ \A c \in Committers : cpc[c] = "idle"
  \* No delivery is under way.
  /\ \A x \in Owners, p \in Paths : dpc[x][p] = "idle"
  /\ clpc \in {"idle", "closed"}
  /\ subq = <<>>

\* EXACTLY ONCE. Once everything has settled, every attempt that began ran
\* exactly one outcome: its on_commit or its on_abort callbacks, and the
\* hooks' matching one. Lean: exactly_once.
ExactlyOnce ==
  AllSettled =>
    \A x \in Owners, a \in Attempts :
      a <= att[x] =>
        /\ ranC[x][a] + ranA[x][a] = 1
        /\ hookC[x][a] + hookA[x][a] = 1
        /\ (ranC[x][a] = 1 <=> committed[x][a])

\* A transact call commits at most once, and only with its last attempt.
OneCommitPerTransact ==
  \A x \in Owners, a \in Attempts : committed[x][a] => a = att[x]

\* ORDER. The hooks' before_commit runs after the transaction's, validation
\* after both, and the hooks' outcome after the transaction's callbacks.
\* Lean: order.
CallbacksBeforeHooks ==
  \A x \in Owners, a \in Attempts :
    /\ hookBefore[x][a] => beforeRan[x][a]
    /\ validated[x][a] => hookBefore[x][a]
    /\ hookC[x][a] > 0 => ranC[x][a] > 0
    /\ hookA[x][a] > 0 => ranA[x][a] > 0

\* BEFORE_COMMIT WRITES ARE VALIDATED. Every committed attempt's callback
\* added one to the counter it read at its snapshot; with those writes
\* validated, no two commits read the same value, so the counter is
\* exactly the number of commits. Lean: before_writes_validated.
NoLostUpdate ==
  ctr = Cardinality({p \in Owners \X Attempts : committed[p[1]][p[2]]})

\* ATTEMPTS ARE ISOLATED. Every callback that ran reported the outcome of
\* its own attempt: a re-run never runs a previous attempt's callbacks.
\* Lean: attempts_isolated.
AttemptIsolation == \A r \in ranFor : r[2] = r[3]

\* ON THE COMMITTING THREAD (D53). Every outcome callback ran on the thread
\* that holds the commit's queue (its poll, or its drop), on the owner's
\* own thread for an abort it chose, or on the closing thread for a
\* transaction close aborted; never on a committer. Example ruled out: the
\* leader that synced a group running a member's on_commit on its own
\* thread while the member's thread is busy. Lean: Callbacks.lean,
\* delivered_on_queue_thread.
OnCommittingThread == \A r \in runBy : r[2] # "committer"

\* on_commit runs only once the commit is durable, at Immediate.
CommitAfterDurable ==
  Durability = "Immediate" =>
    \A x \in Owners : att[x] > 0 /\ ranC[x][att[x]] > 0 => durable >= cseq[x]

\* A PANIC IN BEFORE_COMMIT ABORTS. The attempt never commits and never runs
\* on_commit. Lean: panic_aborts.
PanicAborts ==
  \A x \in Owners, a \in Attempts :
    panicked[x][a] => ~committed[x][a] /\ ranC[x][a] = 0

----------------------------------------------------------------------------
\* Liveness.

\* Everything settles: every transact call returns, and every outcome has
\* run.
Settles == <>AllSettled

====
