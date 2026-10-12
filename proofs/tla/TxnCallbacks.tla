---- MODULE TxnCallbacks ----
\* ===========================================================================
\* THE STORY, for a reader who has never seen the code
\* ===========================================================================
\* A transaction is a batch of reads and writes that either all take effect
\* (it "commits") or none do (it "aborts"). A caller can hang three kinds of
\* callback on one (src/transaction/callbacks.rs): before_commit runs just
\* before the commit is decided and may still write; on_commit runs after
\* the transaction committed; on_abort runs after it ended without
\* committing. A database can also have "hooks" (TransactionHooks): the same
\* three points, for every transaction.
\*
\* Tiny example. A shop sends "your order is placed" from on_commit and
\* releases the reserved stock from on_abort. If both ran, or neither, or
\* on_commit ran twice, or on_commit ran before the order was safely on disk
\* and the machine then lost power, the customer would be told something
\* false. And several threads can reach for the same outcome: the owner of
\* the transaction, the thread that delivers a finished commit, and `close`,
\* which aborts whatever is still open.
\*
\* What the model shows: with two callers that each may retry once, and
\* close racing them, every callback runs exactly once, of the right kind,
\* in the right order, on the right thread, and only after the commit is on
\* disk when the database promises that. Each RED configuration plants one
\* bug, and TLC must then find the broken promise.
\*
\* WHERE THE CODE IS SHAPED DIFFERENTLY. `transact` in the code
\* (src/transaction/retry.rs, `run`) calls the blocking `commit`, which
\* decides and delivers on the owner's own thread. The form whose outcome
\* arrives later is `Transaction::commit_nowait` (src/transaction/nowait.rs):
\* it returns a CommitTicket (src/io_queue/ticket.rs) that the owner's
\* IoQueue delivers at its poll or its drop (src/io_queue/queue.rs). The
\* model gives every commit the ticket form; the blocking commit is the case
\* where the owner's thread is the delivering thread. In the code a commit
\* is validated and logged before its ticket exists, and its result is read
\* from the commit group at delivery (Completion::resolve_with); the model's
\* Decide step stands for that.
\*
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

\* Borrow the standard definitions of numbers, sequences (ordered lists) and finite sets.
EXTENDS Naturals, Sequences, FiniteSets

\* The knobs of a run. Each configuration file (MC_TxnCallbacks_*.cfg) gives them values.
CONSTANTS
  \* The tasks that each run one `transact` call (src/transaction/retry.rs): a set of numbers, one
  \* per task.
  Owners,
  \* The threads of the commit pipeline, which decide commits and sync the log
  \* (src/engine/commit/mod.rs): a set of numbers.
  Committers,
  \* How many times `transact` runs the closure before it gives up: RetryPolicy::max_attempts
  \* (src/transaction/retry.rs).
  MaxAttempts,
  \* "Immediate" (a commit is reported only after its fsync) or "Eventual" (it is reported at once):
  \* DurabilityMode (src/options.rs).
  Durability,
  \* "none" for the design, or the name of one planted bug. A RED configuration names a bug and the
  \* promise it must break.
  Mutant

\* TLC refuses a configuration that allows no attempt at all,
ASSUME MaxAttempts \in Nat \ {0}
\* or one that names no known durability,
ASSUME Durability \in {"Immediate", "Eventual"}
\* or one that names no known bug.
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
\* No real owner may be numbered 0, or "no owner" would be ambiguous.
ASSUME NoOwner \notin Owners

\* The state: everything that changes from one step to the next. Each line says what the variable
\* stands for in the real program.
VARIABLES
  \* The database.
  \* The sequence number of the last commit: the engine's commit counter. A number.
  seq,
  \* The sequence the write-ahead log is synced to disk through; everything at or below it survives
  \* a crash (Wal::sync_data, src/engine/wal.rs). A number.
  durable,
  \* The committed value of the shared counter key that every before_commit callback of the workload
  \* adds one to. A number.
  ctr,
  \* The sequence of the last commit that wrote the counter: what validation compares with a
  \* snapshot. A number.
  ctrSeq,
  \* TRUE once `close` has begun (RegolithEngine::is_closed, src/engine/mod.rs): no transaction
  \* begins or submits after it.
  closed,
  \* Each owner's current attempt.
  \* For each owner, the number of its current attempt, 0 before the first: the loop of `run` in
  \* src/transaction/retry.rs.
  att,
  \* For each owner, where its `transact` call is: "begin", "open" (the closure runs), "before",
  \* "hook", "submit", "waiting" (for its ticket), "abortcb", "aborthook" or "done".
  opc,
  \* For each owner, its transaction's state word: "open", "committing" or "aborted". In the code:
  \* Claim::state, one atomic byte with OPEN, COMMITTING, ABORTED (src/transaction/claim.rs).
  ost,
  \* For each owner, the sequence its attempt reads at: the transaction's snapshot_seq
  \* (src/transaction.rs). A number.
  snap,
  \* For each owner, the counter's value as its snapshot sees it: what the callback's read returns.
  \* A number.
  readv,
  \* For each owner, the keys the attempt has written so far: "own" (the closure's key) and "ctr"
  \* (the callback's). The transaction's write buffer (src/transaction/write_buffer.rs).
  buf,
  \* For each owner, the keys validation checks for a newer commit: the write set handed to the
  \* commit (check_write, src/engine/commit/write_check.rs).
  vset,
  \* For each owner, the attempts whose callbacks its transaction holds: Callbacks in
  \* src/transaction/callbacks.rs, and the on_abort list of Claim. The design holds only the current
  \* attempt's.
  reg,
  \* For each owner, its commit's outcome word: "none", "queued" (submitted), "decided", "claimed"
  \* (being delivered) or "resolved" (the ticket is ready). In the code: Completion::state with
  \* PENDING, DECIDED, DELIVERING, READY (src/io_queue/completion.rs).
  ps,
  \* For each owner, what the pipeline decided: "none" yet, "commit" or "conflict"
  \* (Completion::outcome).
  verdict,
  \* For each owner, the sequence its commit got, 0 if none: what its CommitReceipt reports
  \* (src/transaction/receipt.rs). A number.
  cseq,
  \* The pipeline, the committers and the closer.
  \* The submitted transactions that wait for the pipeline, oldest first: a sequence of owners.
  subq,
  \* For each committer, what it is doing: "idle", or, only under the planted bug HelperDelivers,
  \* running an outcome's "callbacks" or "hooks".
  cpc,
  \* For each committer, the owner whose outcome it is completing, or NoOwner.
  ctarget,
  \* Where `close` is: "idle" (not called), "closing" (looking for open transactions), "clcb" and
  \* "clhook" (running one's on_abort callbacks, then the hooks'), or "closed".
  clpc,
  \* The owner whose transaction the closer is aborting, or NoOwner.
  cltarget,
  \* The owners whose transactions the closer has aborted: a set.
  clseen,
  \* Ghosts, per owner and attempt.
  \* A ghost is a bookkeeping variable the program does not have; it only lets the promises be
  \* stated. This one: for each owner and attempt, how many times the attempt's on_commit callback
  \* ran.
  ranC,
  \* Ghost: for each owner and attempt, how many times the attempt's on_abort callback ran.
  ranA,
  \* Ghost: how many times the database hooks' on_commit ran for the attempt
  \* (TransactionHooks::on_commit, src/transaction/callbacks.rs).
  hookC,
  \* Ghost: how many times the database hooks' on_abort ran for the attempt.
  hookA,
  \* Ghost: TRUE once the attempt's before_commit callback ran.
  beforeRan,
  \* Ghost: TRUE once the hooks' before_commit ran for the attempt.
  hookBefore,
  \* Ghost: TRUE once the pipeline validated the attempt.
  validated,
  \* Ghost: TRUE once the attempt committed.
  committed,
  \* Ghost: TRUE once the attempt's before_commit panicked.
  panicked,
  \* Ghost: one triple <<owner, the attempt that registered the callback, the attempt whose outcome
  \* ran it>> for every callback run.
  ranFor,
  \* The delivery of each owner's outcome, per path.
  \* For each owner and delivery path ("poll" or "drop"), where that path is in delivering the
  \* owner's outcome: "idle", "callbacks" or "hooks".
  dpc,
  \* A ghost: who ran each set of outcome callbacks.
  \* Ghost: one pair <<owner, who>> for every run of outcome callbacks, where who is "poll", "drop",
  \* "owner", "closer" or "committer".
  runBy

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
       \* on_commit: the run count of every callback the transaction holds goes up by one; the
       \* on_abort counts stay.
       THEN ranC' = Bump(ranC, x, reg[x]) /\ UNCHANGED ranA
       \* on_abort: the same, for the on_abort counts.
       ELSE ranA' = Bump(ranA, x, reg[x]) /\ UNCHANGED ranC
  \* Each run is recorded with the outcome's attempt.
  /\ ranFor' = ranFor \cup {<<x, b, att[x]>> : b \in reg[x]}
  \* And with the thread that ran it.
  /\ runBy' = runBy \cup {<<x, who>>}

\* Run the hooks' on_commit or on_abort for x's current attempt.
RunHook(x, kind) ==
  \* Which outcome?
  IF kind = "C"
    \* A commit: the hooks' on_commit count for the current attempt goes up by one.
    THEN hookC' = Bump(hookC, x, {att[x]}) /\ UNCHANGED hookA
    \* An abort: the hooks' on_abort count does.
    ELSE hookA' = Bump(hookA, x, {att[x]}) /\ UNCHANGED hookC

----------------------------------------------------------------------------
\* The owner: one `transact` call, attempt after attempt.

\* begin: a fresh transaction for the next attempt, with a snapshot, and
\* its three callbacks registered. After close begins, begin fails with
\* Closed and nothing is registered. Mutant CallbacksSurvive: the earlier
\* attempts' callbacks stay registered on the re-run.
Begin(x) ==
  \* When: the owner is about to begin an attempt.
  /\ opc[x] = "begin"
  \* Has close begun?
  /\ IF closed
       \* Yes: begin fails with Closed and the transact call ends.
       THEN /\ opc' = [opc EXCEPT ![x] = "done"]
            \* Nothing was registered, so nothing else of the owner changes.
            /\ UNCHANGED <<att, ost, snap, readv, buf, vset, reg, ps, verdict, cseq>>
       \* No: this is the next attempt.
       ELSE /\ att' = [att EXCEPT ![x] = @ + 1]
            \* Its snapshot is the latest commit.
            /\ snap' = [snap EXCEPT ![x] = seq]
            \* Through that snapshot the counter reads its committed value.
            /\ readv' = [readv EXCEPT ![x] = ctr]
            \* The attempt's callbacks are registered. The design drops the earlier attempts'
            \* callbacks; the bug CallbacksSurvive keeps them.
            /\ reg' = [reg EXCEPT ![x] =
                         IF Mutant = "CallbacksSurvive" THEN @ \cup {att[x] + 1} ELSE {att[x] + 1}]
            \* The closure writes its own key.
            /\ buf' = [buf EXCEPT ![x] = {"own"}]
            \* Nothing is fixed for validation yet.
            /\ vset' = [vset EXCEPT ![x] = {}]
            \* The transaction's state word starts "open".
            /\ ost' = [ost EXCEPT ![x] = "open"]
            \* No commit has been submitted.
            /\ ps' = [ps EXCEPT ![x] = "none"]
            \* Nothing is decided.
            /\ verdict' = [verdict EXCEPT ![x] = "none"]
            \* No commit sequence.
            /\ cseq' = [cseq EXCEPT ![x] = 0]
            \* The closure runs: the transaction is open.
            /\ opc' = [opc EXCEPT ![x] = "open"]
  \* The database, the pipeline, the closer and the ghosts do not change.
  /\ UNCHANGED <<db, workers, ghosts>>

\* The closure returns Ok and the owner commits: CAS the state word from
\* "open" to "committing". If close already claimed it, the commit returns
\* Closed and runs nothing: close runs the on_abort callbacks.
OwnerCommit(x) ==
  \* When: the closure returned Ok while the owner still holds its transaction.
  /\ opc[x] = "open"
  \* The CAS: is the state word still "open"?
  /\ IF ost[x] = "open"
       \* Yes: the owner claims the commit, and before_commit runs next.
       THEN ost' = [ost EXCEPT ![x] = "committing"] /\ opc' = [opc EXCEPT ![x] = "before"]
       \* No: close aborted it first. The commit returns Closed and the call ends; close runs the
       \* on_abort callbacks.
       ELSE opc' = [opc EXCEPT ![x] = "done"] /\ UNCHANGED ost
  \* Nothing else changes.
  /\ UNCHANGED <<att, snap, readv, buf, vset, reg, ps, verdict, cseq, db, workers, ghosts>>

\* The transaction ends without committing on its owner's side: rollback,
\* a drop, or an Err from the closure (not retried). CAS "open" to
\* "aborted"; the winner runs on_abort. If close claimed it, it is done.
OwnerAbort(x) ==
  \* When: the owner gives its transaction up (a rollback, a drop, or an Err from the closure).
  /\ opc[x] = "open"
  \* The CAS: is the state word still "open"?
  /\ IF ost[x] = "open"
       \* Yes: the owner claims the abort, and runs on_abort next.
       THEN ost' = [ost EXCEPT ![x] = "aborted"] /\ opc' = [opc EXCEPT ![x] = "abortcb"]
       \* No: close already aborted it and runs its callbacks; the call ends.
       ELSE opc' = [opc EXCEPT ![x] = "done"] /\ UNCHANGED ost
  \* Nothing else changes.
  /\ UNCHANGED <<att, snap, readv, buf, vset, reg, ps, verdict, cseq, db, workers, ghosts>>

\* The transaction's before_commit runs on the committing thread: it reads
\* the counter at the snapshot and writes it plus one, through the
\* transaction.
BeforeOk(x) ==
  \* When: the owner claimed the commit and its before_commit is next.
  /\ opc[x] = "before"
  \* The callback writes the counter through the transaction: the key joins the buffer.
  /\ buf' = [buf EXCEPT ![x] = @ \cup {"ctr"}]
  \* Ghost: this attempt's before_commit ran.
  /\ beforeRan' = Set2(beforeRan, x, att[x], TRUE)
  \* The hooks' before_commit is next.
  /\ opc' = [opc EXCEPT ![x] = "hook"]
  \* Nothing else of the owner, the database or the workers changes.
  /\ UNCHANGED <<att, ost, snap, readv, vset, reg, ps, verdict, cseq, db, workers>>
  \* The other ghosts do not change.
  /\ UNCHANGED <<ranC, ranA, hookC, hookA, hookBefore, validated, committed, panicked, ranFor, runBy>>

\* The transaction's before_commit panics: the commit fails with
\* CallbackPanicked and the attempt goes to on_abort.
BeforePanic(x) ==
  \* When: as BeforeOk, but this time the callback panics.
  /\ opc[x] = "before"
  \* Ghost: this attempt's before_commit ran,
  /\ beforeRan' = Set2(beforeRan, x, att[x], TRUE)
  \* and it panicked.
  /\ panicked' = Set2(panicked, x, att[x], TRUE)
  \* The commit fails; the owner runs on_abort next.
  /\ opc' = [opc EXCEPT ![x] = "abortcb"]
  \* Nothing else of the owner, the database or the workers changes.
  /\ UNCHANGED <<att, ost, snap, readv, buf, vset, reg, ps, verdict, cseq, db, workers>>
  \* The other ghosts do not change.
  /\ UNCHANGED <<ranC, ranA, hookC, hookA, hookBefore, validated, committed, ranFor, runBy>>

\* The hooks' before_commit runs after the transaction's; then the write
\* set to validate is fixed: every write the transaction holds, the
\* callbacks' included. Mutant SkipCallbackWrites: the set captured before
\* the callbacks ran.
HookBefore(x) ==
  \* When: the transaction's own before_commit returned.
  /\ opc[x] = "hook"
  \* Ghost: the hooks' before_commit ran for this attempt.
  /\ hookBefore' = Set2(hookBefore, x, att[x], TRUE)
  \* The write set to validate is fixed now: the whole buffer. The bug SkipCallbackWrites takes only
  \* what the closure wrote.
  /\ vset' = [vset EXCEPT ![x] = IF Mutant = "SkipCallbackWrites" THEN {"own"} ELSE buf[x]]
  \* Submitting is next.
  /\ opc' = [opc EXCEPT ![x] = "submit"]
  \* Nothing else of the owner, the database or the workers changes.
  /\ UNCHANGED <<att, ost, snap, readv, buf, reg, ps, verdict, cseq, db, workers>>
  \* The other ghosts do not change.
  /\ UNCHANGED <<ranC, ranA, hookC, hookA, beforeRan, validated, committed, panicked, ranFor, runBy>>

\* commit_nowait: submit to the pipeline, or, once close has begun, fail
\* with Closed and go to on_abort (one atomic admission check).
Submit(x) ==
  \* When: the callbacks that run before the commit are done.
  /\ opc[x] = "submit"
  \* The admission check: has close begun?
  /\ IF closed
       \* Yes: the commit fails with Closed and the owner runs on_abort next.
       THEN /\ opc' = [opc EXCEPT ![x] = "abortcb"]
            \* Nothing is submitted.
            /\ UNCHANGED <<subq, ps>>
       \* No: the transaction joins the back of the pipeline's queue.
       ELSE /\ subq' = Append(subq, x)
            \* Its outcome word says "queued".
            /\ ps' = [ps EXCEPT ![x] = "queued"]
            \* The owner waits for its ticket.
            /\ opc' = [opc EXCEPT ![x] = "waiting"]
  \* Nothing else of the owner or the database changes.
  /\ UNCHANGED <<att, ost, snap, readv, buf, vset, reg, verdict, cseq, db>>
  \* Nor do the committers, the closer, the delivery paths or the ghosts.
  /\ UNCHANGED <<cpc, ctarget, clpc, cltarget, clseen, dpc, ghosts>>

\* The owner's thread runs the transaction's on_abort callbacks.
OwnerAbortCallbacks(x) ==
  \* When: the owner has an abort to report.
  /\ opc[x] = "abortcb"
  \* The on_abort callbacks run, recorded as run by the owner.
  /\ RunCallbacks(x, "A", "owner")
  \* The hooks' on_abort is next.
  /\ opc' = [opc EXCEPT ![x] = "aborthook"]
  \* Nothing else of the owner, the database or the workers changes.
  /\ UNCHANGED <<att, ost, snap, readv, buf, vset, reg, ps, verdict, cseq, db, workers>>
  \* The other ghosts do not change.
  /\ UNCHANGED <<hookC, hookA, beforeRan, hookBefore, validated, committed, panicked>>

\* Then the hooks' on_abort; the transact call ends (not retried).
OwnerAbortHook(x) ==
  \* When: the owner ran its on_abort callbacks.
  /\ opc[x] = "aborthook"
  \* The hooks' on_abort runs for this attempt.
  /\ RunHook(x, "A")
  \* The transact call ends: an abort the owner chose is not retried.
  /\ opc' = [opc EXCEPT ![x] = "done"]
  \* Nothing else of the owner, the database or the workers changes.
  /\ UNCHANGED <<att, ost, snap, readv, buf, vset, reg, ps, verdict, cseq, db, workers>>
  \* The other ghosts do not change.
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
     \* or the database does not wait for the fsync;
     \/ Durability = "Eventual"
     \* or the fsync has covered the commit;
     \/ durable >= cseq[x]
     \* or the planted bug CommitBeforeDurable skips the wait.
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
  \* When: the owner waits for its ticket
  /\ opc[x] = "waiting"
  \* and the ticket is ready.
  /\ ps[x] = "resolved"
  \* A conflict with attempts left starts the next attempt; a commit, or a conflict on the last
  \* attempt (Exhausted), ends the call.
  /\ opc' = [opc EXCEPT ![x] =
               IF verdict[x] = "conflict" /\ att[x] < MaxAttempts THEN "begin" ELSE "done"]
  \* Nothing else changes.
  /\ UNCHANGED <<att, ost, snap, readv, buf, vset, reg, ps, verdict, cseq, db, workers, ghosts>>

----------------------------------------------------------------------------
\* The committers: decide and sync. They never deliver an outcome: that is
\* the committing thread's (Deliver). Mutant HelperDelivers puts back the
\* design before D53, where any committer completed any decided outcome.

\* Validate the oldest submitted transaction, first-committer-wins on its
\* validated write set, and apply it if it commits.
Decide(c) ==
  \* When: the committer is idle
  /\ cpc[c] = "idle"
  \* and a transaction waits in the pipeline.
  /\ subq # <<>>
  \* x is the oldest submitted transaction.
  /\ LET x == Head(subq)
         \* It conflicts when the counter is in its validated write set and a commit newer than its
         \* snapshot wrote the counter.
         conflict == "ctr" \in vset[x] /\ ctrSeq > snap[x]
     \* x leaves the queue.
     IN /\ subq' = Tail(subq)
        \* Ghost: this attempt was validated.
        /\ validated' = Set2(validated, x, att[x], TRUE)
        \* Its outcome is decided.
        /\ ps' = [ps EXCEPT ![x] = "decided"]
        \* Which way?
        /\ IF conflict
             \* A conflict: that is the verdict,
             THEN /\ verdict' = [verdict EXCEPT ![x] = "conflict"]
                  \* and the database does not change.
                  /\ UNCHANGED <<seq, ctr, ctrSeq, cseq, committed>>
             \* No conflict: the verdict is a commit.
             ELSE /\ verdict' = [verdict EXCEPT ![x] = "commit"]
                  \* It takes the next sequence number,
                  /\ seq' = seq + 1
                  \* which is the commit's sequence.
                  /\ cseq' = [cseq EXCEPT ![x] = seq + 1]
                  \* Did the attempt write the counter?
                  /\ IF "ctr" \in buf[x]
                       \* Yes: the counter becomes the value the attempt read plus one, written at
                       \* this sequence.
                       THEN ctr' = readv[x] + 1 /\ ctrSeq' = seq + 1
                       \* No: the counter is untouched.
                       ELSE UNCHANGED <<ctr, ctrSeq>>
                  \* Ghost: this attempt committed.
                  /\ committed' = Set2(committed, x, att[x], TRUE)
  \* Durability, close and the rest of the owners' state do not change.
  /\ UNCHANGED <<durable, closed, att, opc, ost, snap, readv, buf, vset, reg>>
  \* Nor do the committers, the closer or the delivery paths.
  /\ UNCHANGED <<cpc, ctarget, clpc, cltarget, clseen, dpc>>
  \* Nor do the other ghosts.
  /\ UNCHANGED <<ranC, ranA, hookC, hookA, beforeRan, hookBefore, panicked, ranFor, runBy>>

\* A WAL sync: everything committed so far is durable.
Fsync(c) ==
  \* When: the committer is idle
  /\ cpc[c] = "idle"
  \* and some commit is not durable yet.
  /\ durable < seq
  \* Everything committed so far becomes durable.
  /\ durable' = seq
  \* Nothing else changes.
  /\ UNCHANGED <<seq, ctr, ctrSeq, closed, owner, workers, ghosts>>

\* Mutant HelperDelivers only: a committer claims a decided outcome, CAS
\* "decided" to "claimed", to complete it on its own thread.
Claim(c, x) ==
  \* Only the planted bug lets a committer deliver.
  /\ Mutant = "HelperDelivers"
  \* When: the committer is idle,
  /\ cpc[c] = "idle"
  \* the outcome is decided and nobody claimed it,
  /\ ps[x] = "decided"
  \* and it may be told: a conflict at once,
  /\ \/ verdict[x] = "conflict"
     \* a commit at once when the database does not wait for the fsync,
     \/ Durability = "Eventual"
     \* or a commit once the fsync has covered it.
     \/ durable >= cseq[x]
  \* The CAS: the outcome is claimed.
  /\ ps' = [ps EXCEPT ![x] = "claimed"]
  \* The committer runs the callbacks next,
  /\ cpc' = [cpc EXCEPT ![c] = "callbacks"]
  \* for this owner.
  /\ ctarget' = [ctarget EXCEPT ![c] = x]
  \* Nothing else of the database or the owners changes.
  /\ UNCHANGED <<db, att, opc, ost, snap, readv, buf, vset, reg, verdict, cseq>>
  \* Nor do the queue, the closer, the delivery paths or the ghosts.
  /\ UNCHANGED <<subq, clpc, cltarget, clseen, dpc, ghosts>>

\* The claimer runs the transaction's callbacks of the outcome's kind.
CommitterCallbacks(c) ==
  \* When: the committer claimed an outcome.
  /\ cpc[c] = "callbacks"
  \* The callbacks of the outcome's kind run, recorded as run by a committer: the wrong thread.
  /\ LET x == ctarget[c] IN RunCallbacks(x, IF verdict[x] = "commit" THEN "C" ELSE "A", "committer")
  \* The hooks are next.
  /\ cpc' = [cpc EXCEPT ![c] = "hooks"]
  \* Nothing else of the database, the owners or the workers changes.
  /\ UNCHANGED <<db, owner, subq, ctarget, clpc, cltarget, clseen, dpc>>
  \* The other ghosts do not change.
  /\ UNCHANGED <<hookC, hookA, beforeRan, hookBefore, validated, committed, panicked>>

\* Then the hooks', and the ticket resolves, waking the owner.
CommitterHooks(c) ==
  \* When: the committer ran the callbacks.
  /\ cpc[c] = "hooks"
  \* x is the owner whose outcome it completes.
  /\ LET x == ctarget[c] IN
       \* The hooks' outcome runs.
       /\ RunHook(x, IF verdict[x] = "commit" THEN "C" ELSE "A")
       \* The ticket is ready.
       /\ ps' = [ps EXCEPT ![x] = "resolved"]
  \* The committer is idle again,
  /\ cpc' = [cpc EXCEPT ![c] = "idle"]
  \* with no target.
  /\ ctarget' = [ctarget EXCEPT ![c] = NoOwner]
  \* Nothing else of the database or the owners changes.
  /\ UNCHANGED <<db, att, opc, ost, snap, readv, buf, vset, reg, verdict, cseq>>
  \* Nor do the queue, the closer or the delivery paths.
  /\ UNCHANGED <<subq, clpc, cltarget, clseen, dpc>>
  \* The other ghosts do not change.
  /\ UNCHANGED <<ranC, ranA, beforeRan, hookBefore, validated, committed, panicked, ranFor, runBy>>

----------------------------------------------------------------------------
\* close.

\* close begins: from now on nothing begins or submits.
Close ==
  \* When: close was not called before.
  /\ clpc = "idle"
  \* From now on, begin and submit fail.
  /\ closed' = TRUE
  \* The closer starts looking for open transactions.
  /\ clpc' = "closing"
  \* Nothing else changes.
  /\ UNCHANGED <<seq, durable, ctr, ctrSeq, owner, subq, cpc, ctarget, cltarget, clseen, dpc, ghosts>>

\* close aborts a transaction still open: CAS "open" to "aborted", then
\* run its on_abort. Mutant CloseNoClaim: no CAS, so its owner may still
\* commit it.
CloseAbort(x) ==
  \* When: close is looking for open transactions,
  /\ clpc = "closing"
  \* has not handled this one,
  /\ x \notin clseen
  \* its owner still holds it (it has neither started its commit nor given it up),
  /\ opc[x] = "open"
  \* and its state word is still "open".
  /\ ost[x] = "open"
  \* The CAS: close claims the abort. The bug CloseNoClaim leaves the word "open", so the owner can
  \* still commit.
  /\ ost' = [ost EXCEPT ![x] = IF Mutant = "CloseNoClaim" THEN @ ELSE "aborted"]
  \* The closer has handled this transaction.
  /\ clseen' = clseen \cup {x}
  \* It runs the transaction's on_abort callbacks next,
  /\ clpc' = "clcb"
  \* for this owner.
  /\ cltarget' = x
  \* Nothing else of the database or the owners changes.
  /\ UNCHANGED <<db, att, opc, snap, readv, buf, vset, reg, ps, verdict, cseq>>
  \* No delivery changes either.
  /\ UNCHANGED <<subq, cpc, ctarget, ghosts, dpc>>

\* The closer runs the aborted transaction's on_abort callbacks.
CloseCallbacks ==
  \* When: close claimed a transaction's abort.
  /\ clpc = "clcb"
  \* Its on_abort callbacks run, recorded as run by the closer.
  /\ RunCallbacks(cltarget, "A", "closer")
  \* The hooks' on_abort is next.
  /\ clpc' = "clhook"
  \* Nothing else of the database, the owners or the workers changes.
  /\ UNCHANGED <<db, owner, subq, cpc, ctarget, cltarget, clseen, dpc>>
  \* The other ghosts do not change.
  /\ UNCHANGED <<hookC, hookA, beforeRan, hookBefore, validated, committed, panicked>>

\* Then the hooks' on_abort.
CloseHook ==
  \* When: the closer ran the callbacks.
  /\ clpc = "clhook"
  \* The hooks' on_abort runs for that transaction's attempt.
  /\ RunHook(cltarget, "A")
  \* The closer looks for the next open transaction.
  /\ clpc' = "closing"
  \* Nothing else of the database, the owners or the workers changes.
  /\ UNCHANGED <<db, owner, subq, cpc, ctarget, cltarget, clseen, dpc>>
  \* The other ghosts do not change.
  /\ UNCHANGED <<ranC, ranA, beforeRan, hookBefore, validated, committed, panicked, ranFor, runBy>>

\* No open transaction is left to abort: the final sync, and close is done.
CloseFinish ==
  \* When: close is looking for open transactions
  /\ clpc = "closing"
  \* and none is left that it has not handled.
  /\ ~\E x \in Owners : x \notin clseen /\ opc[x] = "open" /\ ost[x] = "open"
  \* The final sync: everything committed is durable.
  /\ durable' = seq
  \* close is done.
  /\ clpc' = "closed"
  \* Nothing else changes.
  /\ UNCHANGED <<seq, ctr, ctrSeq, closed, owner, subq, cpc, ctarget, cltarget, clseen, dpc, ghosts>>

----------------------------------------------------------------------------
\* The specification.

\* The start: an empty database, every owner about to begin attempt 1.
Init ==
  \* Nothing committed, nothing durable, the counter 0 and never written, the database open.
  /\ seq = 0 /\ durable = 0 /\ ctr = 0 /\ ctrSeq = 0 /\ closed = FALSE
  \* No owner has begun an attempt.
  /\ att = [x \in Owners |-> 0]
  \* Every owner is about to begin.
  /\ opc = [x \in Owners |-> "begin"]
  \* Every state word is "open".
  /\ ost = [x \in Owners |-> "open"]
  \* No snapshot yet.
  /\ snap = [x \in Owners |-> 0]
  \* Nothing read yet.
  /\ readv = [x \in Owners |-> 0]
  \* Nothing written.
  /\ buf = [x \in Owners |-> {}]
  \* Nothing to validate.
  /\ vset = [x \in Owners |-> {}]
  \* No callbacks registered.
  /\ reg = [x \in Owners |-> {}]
  \* No commit submitted.
  /\ ps = [x \in Owners |-> "none"]
  \* Nothing decided.
  /\ verdict = [x \in Owners |-> "none"]
  \* No commit sequence.
  /\ cseq = [x \in Owners |-> 0]
  \* The pipeline's queue is empty.
  /\ subq = <<>>
  \* Every committer is idle,
  /\ cpc = [c \in Committers |-> "idle"]
  \* with no target.
  /\ ctarget = [c \in Committers |-> NoOwner]
  \* close has not been called.
  /\ clpc = "idle" /\ cltarget = NoOwner /\ clseen = {}
  \* No on_commit callback ran.
  /\ ranC = [x \in Owners |-> [a \in Attempts |-> 0]]
  \* No on_abort callback ran.
  /\ ranA = [x \in Owners |-> [a \in Attempts |-> 0]]
  \* No hook on_commit ran.
  /\ hookC = [x \in Owners |-> [a \in Attempts |-> 0]]
  \* No hook on_abort ran.
  /\ hookA = [x \in Owners |-> [a \in Attempts |-> 0]]
  \* No before_commit ran.
  /\ beforeRan = [x \in Owners |-> [a \in Attempts |-> FALSE]]
  \* No hook before_commit ran.
  /\ hookBefore = [x \in Owners |-> [a \in Attempts |-> FALSE]]
  \* Nothing was validated.
  /\ validated = [x \in Owners |-> [a \in Attempts |-> FALSE]]
  \* Nothing committed.
  /\ committed = [x \in Owners |-> [a \in Attempts |-> FALSE]]
  \* Nothing panicked.
  /\ panicked = [x \in Owners |-> [a \in Attempts |-> FALSE]]
  \* No callback run is recorded.
  /\ ranFor = {}
  \* No path is delivering anything.
  /\ dpc = [x \in Owners |-> [p \in Paths |-> "idle"]]
  \* Nobody ran any callback.
  /\ runBy = {}

\* An owner's step. Its closure ends one way or another, and its commit
\* runs to an outcome, delivered on its own thread: all of these happen.
OwnerStep(x) ==
  \* The steps of the closure and of the commit up to its submission,
  \/ Begin(x) \/ OwnerCommit(x) \/ OwnerAbort(x) \/ BeforeOk(x) \/ BeforePanic(x)
  \* the owner's own abort, and reading the ready ticket.
  \/ HookBefore(x) \/ Submit(x) \/ OwnerAbortCallbacks(x) \/ OwnerAbortHook(x) \/ Resolve(x)
  \* Delivery of the ticket, by the queue's poll or the queue's drop.
  \/ \E p \in Paths : Deliver(x, p) \/ DeliverCallbacks(x, p) \/ DeliverHooks(x, p)

\* A committer's step.
CommitterStep(c) ==
  \* Decide a commit, sync the log, or (only under the bug HelperDelivers) claim an outcome
  \/ Decide(c) \/ Fsync(c) \/ \E x \in Owners : Claim(c, x)
  \* and complete it.
  \/ CommitterCallbacks(c) \/ CommitterHooks(c)

\* The closer's steps once close has begun.
CloserStep == (\E x \in Owners : CloseAbort(x)) \/ CloseCallbacks \/ CloseHook \/ CloseFinish

\* Every step the system can take.
Next ==
  \* An owner takes a step,
  \/ \E x \in Owners : OwnerStep(x)
  \* or a committer does,
  \/ \E c \in Committers : CommitterStep(c)
  \* or close is called, or the closer takes a step.
  \/ Close \/ CloserStep

\* Fairness: owners, committers and a started close all make progress.
\* Calling close at all is the caller's choice.
Fairness ==
  \* Each owner that can take a step eventually takes one.
  /\ \A x \in Owners : WF_vars(OwnerStep(x))
  \* So does each committer.
  /\ \A c \in Committers : WF_vars(CommitterStep(c))
  \* So does a close that has begun.
  /\ WF_vars(CloserStep)

\* Every behaviour: start in Init, take Next steps or stutter, fairly.
Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  \* Attempt numbers stay within the policy.
  /\ att \in [Owners -> 0..MaxAttempts]
  \* Each state word is one of its three values.
  /\ ost \in [Owners -> {"open", "committing", "aborted"}]
  \* Each outcome word is one of its five values.
  /\ ps \in [Owners -> {"none", "queued", "decided", "claimed", "resolved"}]
  \* Each verdict is one of its three values.
  /\ verdict \in [Owners -> {"none", "commit", "conflict"}]
  \* Each committer is idle or completing an outcome.
  /\ cpc \in [Committers -> {"idle", "callbacks", "hooks"}]
  \* The closer is in one of its five places.
  /\ clpc \in {"idle", "closing", "clcb", "clhook", "closed"}
  \* Each delivery path is idle, or running callbacks, or the hooks.
  /\ dpc \in [Owners -> [Paths -> {"idle", "callbacks", "hooks"}]]

\* AT MOST ONCE. No attempt's callbacks run twice or both ways, and the
\* hooks' outcome runs at most once per attempt. Lean: exactly_once.
\* Example ruled out: the queue's poll and the queue's drop both deliver the
\* same commit, and the shop's "order placed" message goes out twice. The
\* program needs this because a callback acts outside the database, where
\* nothing can be rolled back.
AtMostOnce ==
  \* For every owner and attempt:
  \A x \in Owners, a \in Attempts :
    \* its on_commit and its on_abort callbacks together ran at most once;
    /\ ranC[x][a] + ranA[x][a] <= 1
    \* and so did the hooks' outcome.
    /\ hookC[x][a] + hookA[x][a] <= 1

\* Nothing is in flight: every transact call returned and every worker is
\* idle.
AllSettled ==
  \* Every transact call returned.
  /\ \A x \in Owners : opc[x] = "done"
  \* Every committer is idle.
  /\ \A c \in Committers : cpc[c] = "idle"
  \* No delivery is under way.
  /\ \A x \in Owners, p \in Paths : dpc[x][p] = "idle"
  \* close was never called, or is done.
  /\ clpc \in {"idle", "closed"}
  \* Nothing waits in the pipeline.
  /\ subq = <<>>

\* EXACTLY ONCE. Once everything has settled, every attempt that began ran
\* exactly one outcome: its on_commit or its on_abort callbacks, and the
\* hooks' matching one. Lean: exactly_once.
\* Example ruled out: close and the owner each leave the abort to the other,
\* neither runs on_abort, and the reserved stock is never released. The
\* program needs this because a caller that registered a callback is waiting
\* to be told how its transaction ended.
ExactlyOnce ==
  \* Once everything has settled,
  AllSettled =>
    \A x \in Owners, a \in Attempts :
      \* for every attempt that began:
      a <= att[x] =>
        \* exactly one of its on_commit and on_abort callbacks ran;
        /\ ranC[x][a] + ranA[x][a] = 1
        \* exactly one hook outcome ran;
        /\ hookC[x][a] + hookA[x][a] = 1
        \* and on_commit ran exactly when the attempt committed.
        /\ (ranC[x][a] = 1 <=> committed[x][a])

\* A transact call commits at most once, and only with its last attempt.
\* Example ruled out: attempt 1 commits, transact runs the closure again, and
\* the caller's change is applied twice.
OneCommitPerTransact ==
  \* A committed attempt is its owner's current one: after a commit, transact starts no further
  \* attempt.
  \A x \in Owners, a \in Attempts : committed[x][a] => a = att[x]

\* ORDER. The hooks' before_commit runs after the transaction's, validation
\* after both, and the hooks' outcome after the transaction's callbacks.
\* Lean: order.
\* Example ruled out: validation runs first and a before_commit callback then
\* adds a write nobody checked; or a hook that records "committed" runs before
\* the transaction's own on_commit. The program needs this because the order
\* is documented and callers build on it.
CallbacksBeforeHooks ==
  \* For every owner and attempt:
  \A x \in Owners, a \in Attempts :
    \* the hooks' before_commit ran only after the transaction's own;
    /\ hookBefore[x][a] => beforeRan[x][a]
    \* validation ran only after the hooks' before_commit;
    /\ validated[x][a] => hookBefore[x][a]
    \* the hooks' on_commit ran only after the transaction's on_commit;
    /\ hookC[x][a] > 0 => ranC[x][a] > 0
    \* the hooks' on_abort ran only after the transaction's on_abort.
    /\ hookA[x][a] > 0 => ranA[x][a] > 0

\* BEFORE_COMMIT WRITES ARE VALIDATED. Every committed attempt's callback
\* added one to the counter it read at its snapshot; with those writes
\* validated, no two commits read the same value, so the counter is
\* exactly the number of commits. Lean: before_writes_validated.
\* Example ruled out: two transactions both read 0 in their callbacks and
\* both commit 1. One increment is lost, because validation looked only at
\* the keys the closures wrote and never at the counter.
NoLostUpdate ==
  \* The counter equals the number of (owner, attempt) pairs that committed.
  ctr = Cardinality({p \in Owners \X Attempts : committed[p[1]][p[2]]})

\* ATTEMPTS ARE ISOLATED. Every callback that ran reported the outcome of
\* its own attempt: a re-run never runs a previous attempt's callbacks.
\* Lean: attempts_isolated.
\* Example ruled out: attempt 1 conflicts and attempt 2 commits; attempt 1's
\* on_commit, still registered, runs with attempt 2's outcome, so the caller
\* acts twice on one commit, once with values the failed attempt computed.
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
\* Example ruled out: on_commit tells the customer the order is placed, the
\* machine loses power before the fsync, and after the restart the order is
\* gone. The program needs this because Immediate durability promises that a
\* reported commit survives a crash.
CommitAfterDurable ==
  \* At Immediate durability,
  Durability = "Immediate" =>
    \* an owner whose current attempt's on_commit ran has a commit that the log sync already covers.
    \A x \in Owners : att[x] > 0 /\ ranC[x][att[x]] > 0 => durable >= cseq[x]

\* A PANIC IN BEFORE_COMMIT ABORTS. The attempt never commits and never runs
\* on_commit. Lean: panic_aborts.
\* Example ruled out: a before_commit callback panics halfway through its
\* writes and the half-written transaction commits anyway.
PanicAborts ==
  \* For every owner and attempt:
  \A x \in Owners, a \in Attempts :
    \* one whose before_commit panicked did not commit, and its on_commit never ran.
    panicked[x][a] => ~committed[x][a] /\ ranC[x][a] = 0

----------------------------------------------------------------------------
\* Liveness.

\* Everything settles: every transact call returns, and every outcome has
\* run. Example ruled out: an outcome is decided but no path ever delivers
\* it, so its owner waits for its ticket for ever. Unlike the invariants,
\* which look at one state at a time, this is a promise about whole runs: TLC
\* checks that every run allowed by Fairness reaches a settled state.
Settles == <>AllSettled

====
