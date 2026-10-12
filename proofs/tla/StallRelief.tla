---- MODULE StallRelief ----
\* ===========================================================================
\* THE STORY
\* ===========================================================================
\* A write stall "stop" refuses every write until the background makes room
\* (too many memtables, or too many tables in level 0). On a database with
\* no compaction worker and inline compaction on (Options::inline_compaction)
\* nobody does that in the background: a stopped writer relieves the stop
\* itself, with flush and compaction steps on its own thread
\* (RegolithEngine::relieve_inline, src/engine/mod.rs). A step needs the
\* "gate" (the flush exclusion, or the compaction gate). When another thread
\* holds it the step is "contended", and the writer, instead of waiting for
\* the gate, returns at once with a wait (WouldBlock::Stall) on one shared
\* unit (StallSignal, src/engine/commit/stall.rs), trusting the thread that
\* holds the gate.
\*
\* Three kinds of thread hold the gate:
\*   - a stopped writer relieving the stop, step after step;
\*   - a writer whose write went in and left one step owing, which it runs
\*     once after its commit (run_owed, src/engine/background_step.rs) and
\*     then returns: it relieves nothing more;
\*   - a foreground job (compact_range, an ingest, a checkpoint;
\*     src/engine/foreground.rs), which holds the gate for its whole run.
\*
\* Tiny example 1, the owed step. Writer 1's write goes in and brings on the
\* stop. Its owed step takes the gate. Writer 2 is stopped, its step finds
\* the gate held, and it waits on the unit. Writer 1's step leaves the stop
\* on (one flush, and still too many tables), and writer 1 returns: that
\* was its last write. If the unit landed only when the stop cleared, nobody
\* would land it, and writer 2 would wait for ever. This is the hang seen in
\* the test `the_published_high_water_mark_holds_under_many_concurrent_writers`:
\* twelve writers parked on the stall, nobody running a step.
\*
\* The fix, "relief handed back": where writers relieve the stop, every
\* piece of progress (each step, once its gate is released) counts itself
\* and lands the unit, stop or no stop (StallSignal::refresh). Each waiter
\* looks again, and relieves the stop itself, or is contended anew.
\*
\* Tiny example 2, the gap. Writer 2 found the gate held, but registers its
\* wait only a moment later. In that moment writer 1's step ends and lands
\* the unit, with nobody on it yet. Writer 2 registers after the landing and
\* waits for ever. So the writer reads the progress count before its step,
\* reads it again once registered, and, if it moved, lands its own unit
\* (StallSignal::wait, `seen`).
\*
\* Tiny example 3, the job. A job holds the gate; writers find it held and
\* wait; the job ends. A job compacts nothing on its own, so it must relieve
\* the stop once it releases the gate, and land the unit
\* (RegolithEngine::relieve_after_foreground).
\*
\* What this model checks cannot happen: every writer has finished or
\* waits on the stall, the job is not running or still to relieve, and a
\* writer waits: nobody is left to land its unit (NoStrandedWait).
\*
\* WHAT IS MODELLED, and the code each piece mirrors:
\*   stopped   whether writes are stopped now (StallSignal::classify)
\*   gate      who holds the gate: nobody, the job, or a writer
\*   job       the job's progress: not started, holding the gate, about to
\*             relieve after releasing it, finished
\*   wpc       each writer's progress (see TypeOK)
\*   progress  the progress count (StallSignal::progress)
\*   seen      the count each contended writer read before its step
\*
\* WHAT IS LEFT OUT, and why that loses nothing:
\*   - The kind of stop and of step (flush or compaction): any step may
\*     clear the stop or leave it on, and a write that goes in may bring it
\*     on, so every mix is covered.
\*   - The job's relief steps hold the gate too; here they are one step with
\*     the gate free. A writer contended on them waits for their progress
\*     the same way it waits for a writer's.
\*   - A stopped writer with a queue: its relieving step is a job on one
\*     writer's queue, and a queue dropped before running it lands the unit
\*     (StallStep::release), the same hand-back.
\*   - Several jobs: they take the gate one at a time, each ends with the
\*     same relief.
\*   - The bound on a writer's steps: here a writer may give up after any
\*     step with the stop on, which covers every bound.
\*
\* CONFIGURATIONS (each GREEN must pass, each RED must break the one
\* invariant it names):
\*   MC_StallRelief_Green           two writers, one job, the real code:
\*                                  NoStrandedWait holds.
\*   MC_StallRelief_Red_NoRelief    the job releases the gate and ends with
\*                                  no relief: NoStrandedWait breaks.
\*   MC_StallRelief_Red_NoHandBack  progress lands the unit only when the
\*                                  stop cleared (example 1):
\*                                  NoStrandedWait breaks.
\*   MC_StallRelief_Red_NoRecheck   a contended writer registers without
\*                                  reading the count again (example 2):
\*                                  NoStrandedWait breaks.
\*
\* Lean, proofs/lean/Regolith/StallRelief.lean, proves the rule for any
\* number of writers, and each RED as a run of the buggy steps.

\* Numbers, for the progress count.
EXTENDS Naturals

\* The fixed inputs of a configuration.
CONSTANTS
  \* The writer threads.
  Writers,
  \* "Green" for the real code, or the bug planted.
  Mode,
  \* How many pieces of progress may leave the stop on; after that every
  \* step clears it, so the runs end.
  MaxSteps

\* The bug names this model knows.
ASSUME Mode \in {"Green", "NoRelief", "NoHandBack", "NoRecheck"}

\* The state that changes from step to step.
VARIABLES
  \* Whether a write would be stopped right now.
  stopped,
  \* "free", "job", or the writer whose step holds the gate.
  gate,
  \* "idle", "holding", "relieving" or "done".
  job,
  \* Each writer's progress.
  wpc,
  \* The progress count.
  progress,
  \* The count each writer read before its last step.
  seen

\* Every variable.
vars == <<stopped, gate, job, wpc, progress, seen>>

\* The start: stopped or not, the gate free, the job not started, every
\* writer about to write, nothing counted.
Init ==
  \* Either.
  /\ stopped \in BOOLEAN
  \* Nobody holds the gate.
  /\ gate = "free"
  \* The job has not started.
  /\ job = "idle"
  \* Every writer is about to write.
  /\ wpc = [w \in Writers |-> "write"]
  \* Nothing counted, nothing read.
  /\ progress = 0
  /\ seen = [w \in Writers |-> 0]

\* What a step may leave: the stop on or off, while the budget for leaving
\* it on lasts; then off.
Outcomes == IF progress < MaxSteps THEN BOOLEAN ELSE {FALSE}

\* Whether a piece of progress lands the unit, with the stop now `s`: in the
\* real code always (relief handed back); in bug NoHandBack only once the
\* stop cleared.
Lands(s) == Mode # "NoHandBack" \/ ~s

\* The unit lands: every writer waiting on it wakes and writes again
\* (StallSignal::land, then the writer's retry).
Land(f) == [x \in Writers |-> IF f[x] = "waiting" THEN "write" ELSE f[x]]

\* The job starts and takes the gate (Gate::write).
JobStart ==
  \* Not started, and the gate is free.
  /\ job = "idle"
  /\ gate = "free"
  \* It holds the gate for its whole run.
  /\ gate' = "job"
  /\ job' = "holding"
  \* Nothing else changes.
  /\ UNCHANGED <<stopped, wpc, progress, seen>>

\* The job's work is done and it releases the gate. The real code goes on
\* to relieve; bug NoRelief ends here.
JobEnd ==
  \* It holds the gate.
  /\ job = "holding"
  \* The gate is free again.
  /\ gate' = "free"
  \* The relief is next, or, for the bug, nothing.
  /\ job' = IF Mode = "NoRelief" THEN "done" ELSE "relieving"
  \* Nothing else changes.
  /\ UNCHANGED <<stopped, wpc, progress, seen>>

\* The job's relief (relieve_after_foreground). With the gate free, its
\* steps run, leaving the stop on or off, and its progress lands the unit.
\* With a writer's step holding the gate, it leaves the stop to that
\* writer, who counts its own progress.
JobRelieve ==
  \* It released the gate and has not relieved yet.
  /\ job = "relieving"
  /\ IF gate = "free"
     \* Steps, then the count and the landing.
     THEN /\ stopped' \in Outcomes
          /\ progress' = progress + 1
          /\ wpc' = Land(wpc)
     \* Left to the writer holding the gate.
     ELSE UNCHANGED <<stopped, progress, wpc>>
  \* The job is finished.
  /\ job' = "done"
  \* The gate and what writers read are as they were.
  /\ UNCHANGED <<gate, seen>>

\* Writer w writes. Not stopped: the write goes in, may bring on the stop,
\* and leaves one step owing. Stopped: it relieves the stop itself when the
\* gate is free; else it reads the count and is contended.
WriterTry(w) ==
  \* The writer is about to write.
  /\ wpc[w] = "write"
  /\ IF ~stopped
     \* Written; the stop may come on; one step owed.
     THEN /\ stopped' \in BOOLEAN
          /\ wpc' = [wpc EXCEPT ![w] = "owing"]
          /\ UNCHANGED <<gate, seen>>
     ELSE IF gate = "free"
          \* Stopped, gate free: its step takes the gate.
          THEN /\ gate' = w
               /\ wpc' = [wpc EXCEPT ![w] = "relieving"]
               /\ UNCHANGED <<stopped, seen>>
          \* Stopped, gate held: it read the count before its step, and
          \* the step is contended.
          ELSE /\ seen' = [seen EXCEPT ![w] = progress]
               /\ wpc' = [wpc EXCEPT ![w] = "contended"]
               /\ UNCHANGED <<stopped, gate>>
  \* Nothing else changes.
  /\ UNCHANGED <<job, progress>>

\* Writer w, contended, registers its wait on the unit, then looks again
\* (StallSignal::wait). The stop cleared: it counts that and lands the unit
\* (refresh). The count moved since it read it: it lands the unit (bug
\* NoRecheck skips this look). Otherwise it waits.
WriterRegister(w) ==
  \* The writer was contended.
  /\ wpc[w] = "contended"
  /\ IF ~stopped
     \* Cleared: counted, landed, and w writes again.
     THEN /\ progress' = progress + 1
          /\ wpc' = [Land(wpc) EXCEPT ![w] = "write"]
     ELSE IF Mode # "NoRecheck" /\ seen[w] # progress
          \* Progress it missed: landed, and w writes again.
          THEN /\ wpc' = [Land(wpc) EXCEPT ![w] = "write"]
               /\ UNCHANGED progress
          \* Nothing missed: it waits.
          ELSE /\ wpc' = [wpc EXCEPT ![w] = "waiting"]
               /\ UNCHANGED progress
  \* Nothing else changes.
  /\ UNCHANGED <<stopped, gate, job, seen>>

\* Writer w's relieving step ends: the stop is left on or off, and the gate
\* released; its progress is counted next.
WriterStepEnd(w) ==
  \* The writer is relieving and holds the gate.
  /\ wpc[w] = "relieving"
  /\ stopped' \in Outcomes
  /\ gate' = "free"
  /\ wpc' = [wpc EXCEPT ![w] = "relRefresh"]
  \* Nothing else changes.
  /\ UNCHANGED <<job, progress, seen>>

\* Writer w counts its step's progress (refresh), which lands the unit as
\* Lands says; then it looks again, or, with the stop on, gives up (its
\* bound reached: Error::Busy).
WriterRefresh(w) ==
  \* The writer released the gate after its relieving step.
  /\ wpc[w] = "relRefresh"
  /\ progress' = progress + 1
  /\ \E next \in (IF stopped THEN {"write", "done"} ELSE {"write"}) :
       wpc' = [(IF Lands(stopped) THEN Land(wpc) ELSE wpc) EXCEPT ![w] = next]
  \* Nothing else changes.
  /\ UNCHANGED <<stopped, gate, job, seen>>

\* Writer w's owed step, after its commit: it takes the gate when free;
\* contended, it leaves the step owing for a next write and returns.
OwedTry(w) ==
  \* The writer's write went in and left a step owing.
  /\ wpc[w] = "owing"
  /\ IF gate = "free"
     \* The step takes the gate.
     THEN /\ gate' = w
          /\ wpc' = [wpc EXCEPT ![w] = "owedStep"]
     \* Contended: the writer returns.
     ELSE /\ wpc' = [wpc EXCEPT ![w] = "done"]
          /\ UNCHANGED gate
  \* Nothing else changes.
  /\ UNCHANGED <<stopped, job, progress, seen>>

\* Writer w's owed step ends: the stop is left on or off, and the gate
\* released.
OwedStepEnd(w) ==
  \* The owed step holds the gate.
  /\ wpc[w] = "owedStep"
  /\ stopped' \in Outcomes
  /\ gate' = "free"
  /\ wpc' = [wpc EXCEPT ![w] = "owedRefresh"]
  \* Nothing else changes.
  /\ UNCHANGED <<job, progress, seen>>

\* Writer w counts its owed step's progress, which lands the unit as Lands
\* says, and returns: it relieves nothing more.
OwedRefresh(w) ==
  \* The owed step released the gate.
  /\ wpc[w] = "owedRefresh"
  /\ progress' = progress + 1
  /\ wpc' = [(IF Lands(stopped) THEN Land(wpc) ELSE wpc) EXCEPT ![w] = "done"]
  \* Nothing else changes.
  /\ UNCHANGED <<stopped, gate, job, seen>>

\* Every step anyone can take.
Next ==
  \* The job starts, ends, or relieves.
  \/ JobStart \/ JobEnd \/ JobRelieve
  \* A writer writes, registers, steps or counts.
  \/ \E w \in Writers :
       \/ WriterTry(w) \/ WriterRegister(w) \/ WriterStepEnd(w) \/ WriterRefresh(w)
       \/ OwedTry(w) \/ OwedStepEnd(w) \/ OwedRefresh(w)

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
  \* Each writer: about to write, owing its step, in its owed step,
  \* relieving, counting either step, contended, waiting, or finished.
  /\ wpc \in [Writers -> {"write", "owing", "owedStep", "relieving", "relRefresh",
                          "owedRefresh", "contended", "waiting", "done"}]
  \* The count is a number, and so is what each writer read.
  /\ progress \in Nat
  /\ seen \in [Writers -> Nat]

\* THE RULE. Once every writer has finished or waits on the stall, and the
\* job is not running or still to relieve, no writer waits: someone was
\* always on the way to land its unit. Rules out the three stories: writer
\* 2 left waiting after writer 1's last owed step, after a landing it
\* registered too late for, and after the job. Lean: no_stranded_wait.
NoStrandedWait ==
  \* With nobody left but waiters ...
  (job \notin {"holding", "relieving"} /\ \A w \in Writers : wpc[w] \in {"waiting", "done"})
    \* ... no writer waits.
    => \A w \in Writers : wpc[w] # "waiting"

====
