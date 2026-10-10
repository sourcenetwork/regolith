---- MODULE StallRelief ----
\* ===========================================================================
\* THE STORY
\* ===========================================================================
\* A write stall "stop" refuses every write until compaction makes room (too
\* many tables in level 0). On a database with no compaction worker and
\* inline compaction on (Options::inline_compaction), nobody compacts in the
\* background: a stopped writer relieves the stop itself, with compaction
\* steps on its own thread (RegolithEngine::relieve_inline, src/engine/mod.rs).
\* A step needs the compaction gate. When another thread holds the gate the
\* step is "contended", and the writer, instead of waiting for the gate,
\* returns at once with a wait (WouldBlock::Stall) on one shared unit that
\* lands when the stop clears (StallSignal, src/engine/commit/stall.rs). The
\* thread holding the gate is trusted to relieve the stop.
\*
\* A foreground job (compact_range, an ingest, a checkpoint;
\* src/engine/foreground.rs) holds the gate for its whole run. An ingest or a
\* checkpoint compacts nothing. So:
\*
\* Tiny example. Two writers, one ingest, level 0 at the stop. The ingest
\* takes the gate. Writer 1 is stopped, its step finds the gate held, and it
\* waits on the unit. Writer 2 does the same. The ingest finishes and
\* releases the gate. Nobody compacts, nobody lands the unit, and both
\* writers wait for ever, though the gate is free and a step would clear the
\* stop at once.
\*
\* The fix (RegolithEngine::relieve_after_foreground): when a job ends on a
\* database with no worker and inline compaction on, the job's own thread,
\* the one the contended writers were told to trust, runs the same steps a
\* stopped writer would, then lands the unit (when the stop cleared, or when
\* it could not clear it, so each writer looks again and reports why). If a
\* writer is already relieving the stop, the job leaves it to that writer.
\*
\* What this model checks cannot happen: once nothing is running or about
\* to run a relief, a writer is still waiting on the stall (NoStrandedWait).
\*
\* WHAT IS MODELLED, and the code each piece mirrors:
\*   stopped   whether level 0 is at the stop (StallSignal::classify)
\*   gate      who holds the compaction gate: nobody, the job, or a writer
\*             whose relief step is compacting
\*   job       the foreground job's progress: not started, holding the gate,
\*             relieving after it released the gate, finished
\*   wpc       each writer's progress: about to write, relieving the stop,
\*             waiting on the stall's unit, written
\*
\* WHAT IS LEFT OUT, and why that loses nothing:
\*   - A compaction step that cannot clear the stop: the fix lands the unit
\*     then too, so the waiters look again; here a step always clears it.
\*   - Several jobs: they take the gate one at a time, and each ends with
\*     the same relief.
\*   - The queue a writer may record its wait on: the unit lands the same
\*     way; the queue only decides where the wait is reported.
\*
\* CONFIGURATIONS (each GREEN must pass, each RED must break the one
\* invariant it names):
\*   MC_StallRelief_Green         two writers, one ingest, the relief after
\*                                the job: NoStrandedWait holds.
\*   MC_StallRelief_Red_NoRelief  the job releases the gate and ends with no
\*                                relief: NoStrandedWait breaks.
\*
\* Lean, proofs/lean/Regolith/StallRelief.lean, proves the job's end strands
\* no waiter for any number of writers.

\* Numbers, for nothing more than the writers' names.
EXTENDS Naturals

\* The fixed inputs of a configuration.
CONSTANTS
  \* The writer threads.
  Writers,
  \* "Green" for the real code, or "NoRelief" for the bug.
  Mode

\* The bug name this model knows.
ASSUME Mode \in {"Green", "NoRelief"}

\* The state that changes from step to step.
VARIABLES
  \* Whether a write would be stopped right now.
  stopped,
  \* "free", "job", or the writer whose step holds the gate.
  gate,
  \* "idle", "holding", "relieving" or "done".
  job,
  \* [Writers -> {"write", "relieving", "waiting", "done"}].
  wpc

\* Every variable.
vars == <<stopped, gate, job, wpc>>

\* The start: level 0 at the stop, the gate free, the job not started, every
\* writer about to write.
Init ==
  \* Too many tables in level 0.
  /\ stopped = TRUE
  \* Nobody holds the gate.
  /\ gate = "free"
  \* The job has not started.
  /\ job = "idle"
  \* Every writer is about to write.
  /\ wpc = [w \in Writers |-> "write"]

\* The unit lands: every writer waiting on it wakes and writes again
\* (StallSignal::land, then the writer's retry).
Woken(w) == IF wpc[w] = "waiting" THEN "write" ELSE wpc[w]

\* The job starts and takes the gate exclusively (Gate::write).
JobStart ==
  \* Not started, and the gate is free.
  /\ job = "idle"
  /\ gate = "free"
  \* It holds the gate for its whole run.
  /\ gate' = "job"
  /\ job' = "holding"
  \* Nothing else changes.
  /\ UNCHANGED <<stopped, wpc>>

\* The job's work is done (it added no room) and it releases the gate. The
\* real code goes on to relieve; the bug ends here.
JobEnd ==
  \* It holds the gate.
  /\ job = "holding"
  \* The gate is free again.
  /\ gate' = "free"
  \* The fix relieves next; the bug is finished.
  /\ job' = IF Mode = "Green" THEN "relieving" ELSE "done"
  \* Nothing else changes.
  /\ UNCHANGED <<stopped, wpc>>

\* The job's relief (relieve_after_foreground): when the stop holds and the
\* gate is free, one step clears it; when a writer's step holds the gate,
\* that writer relieves it. Then the unit lands whatever the stop is, so the
\* waiters look again.
JobRelieve ==
  \* It released the gate and has not relieved yet.
  /\ job = "relieving"
  /\ IF gate = "free"
     \* The gate is free: its step clears the stop (if there was one) and
     \* the unit lands.
     THEN /\ stopped' = FALSE
          /\ wpc' = [w \in Writers |-> Woken(w)]
     \* A writer's step holds the gate: that writer relieves and lands it.
     ELSE UNCHANGED <<stopped, wpc>>
  \* The job is finished.
  /\ job' = "done"
  \* The gate is as it was.
  /\ UNCHANGED gate

\* Writer w writes. Not stopped: the write goes in. Stopped: it relieves the
\* stop itself when the gate is free, and otherwise waits on the unit.
WriterTry(w) ==
  \* The writer is about to write.
  /\ wpc[w] = "write"
  /\ IF ~stopped
     \* No stop: written.
     THEN /\ wpc' = [wpc EXCEPT ![w] = "done"]
          /\ UNCHANGED gate
     ELSE IF gate = "free"
          \* Stopped, gate free: its step takes the gate.
          THEN /\ gate' = w
               /\ wpc' = [wpc EXCEPT ![w] = "relieving"]
          \* Stopped, gate held: contended, so it waits on the unit.
          ELSE /\ wpc' = [wpc EXCEPT ![w] = "waiting"]
               /\ UNCHANGED gate
  \* Nothing else changes.
  /\ UNCHANGED <<stopped, job>>

\* Writer w's step compacts: the stop clears, the gate is released, the
\* unit lands (refresh), and w writes again.
WriterStep(w) ==
  \* The writer is relieving and holds the gate.
  /\ wpc[w] = "relieving"
  \* Level 0 is below the stop now.
  /\ stopped' = FALSE
  \* The gate is free again.
  /\ gate' = "free"
  \* The unit lands, and w goes back to its write.
  /\ wpc' = [x \in Writers |-> IF x = w THEN "write" ELSE Woken(x)]
  \* Nothing else changes.
  /\ UNCHANGED job

\* Every step anyone can take.
Next ==
  \* The job starts, ends, or relieves.
  \/ JobStart \/ JobEnd \/ JobRelieve
  \* A writer writes or steps.
  \/ \E w \in Writers : WriterTry(w) \/ WriterStep(w)

\* Every behaviour: start in Init, then take Next steps or stutter.
Spec == Init /\ [][Next]_vars

\* Every variable holds what its comment says.
TypeOK ==
  \* The stop is a yes or a no.
  /\ stopped \in BOOLEAN
  \* The gate is free, the job's, or a writer's.
  /\ gate \in {"free", "job"} \cup Writers
  \* The job is at one of its steps.
  /\ job \in {"idle", "holding", "relieving", "done"}
  \* Each writer is at one of its steps.
  /\ wpc \in [Writers -> {"write", "relieving", "waiting", "done"}]

\* THE RULE. Once the job is finished and no writer is relieving, no writer
\* is left waiting on the stall: someone is always on the way to land its
\* unit. Rules out the story: both writers waiting, the job finished, the
\* gate free, and nobody to compact. Lean: job_end_strands_no_waiter.
NoStrandedWait ==
  \* With the job finished and no writer relieving ...
  (job = "done" /\ \A w \in Writers : wpc[w] # "relieving")
    \* ... no writer waits.
    => \A w \in Writers : wpc[w] # "waiting"

====
