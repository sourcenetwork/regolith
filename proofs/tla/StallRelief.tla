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
\* Tiny example 4, the latch (E35). The engine "latches" when its log is
\* left in a state nobody can vouch for (a sync that failed while a rotation
\* sealed the log, a rollback that failed): from then on every write fails
\* with that reason (RegolithEngine::latch, src/engine/mod.rs). A latched
\* engine relieves no stop: a write fails before it runs any step. Writer 2
\* waits on the unit; the engine latches; nothing is promised to clear the
\* stop any more, so writer 2 would wait until the database closes. So the
\* latch lands the unit, and writer 2, writing again, is told the latch, as
\* a fresh write is (admit_write).
\*
\* The same gap as example 2 opens here. Writer 2 was let in before the
\* latch, and registers its wait after the latch landed the unit: it would
\* wait on a unit nobody lands. So the latch stores its flag BEFORE it takes
\* the unit, and a writer reads the flag again once registered
\* (RegolithEngine::stall_wait): either the latch found the writer on the
\* unit, or the writer reads the flag.
\*
\* Tiny example 5, the rotation that fails. Writer 1's write was let in with
\* no stop, and finds the active memtable full and the memtable cap reached:
\* it flushes the oldest frozen memtable itself, holding the gate, before it
\* seals the active one (rotate_if_full). Meanwhile the stop comes on;
\* writer 2 finds the gate held and waits. Writer 1's flush ends, with the
\* stop still on. Then its seal fails (the next log cannot be created, or
\* the old one cannot be synced), and writer 1 returns the error. The flush
\* changed what the stop counts, so the rotation counts its progress on
\* every way out, failed or not; if it counted only once the seal went
\* through, writer 2 would be left waiting. (The step the flush left owing
\* does not save it: it waits on writer 1's queue until that is polled, and
\* on a latched engine it fails before it counts anything.)
\*
\* Tiny example 6, the relief that fails (E36). The work that relieves a
\* stop is a flush or a compaction, and it can fail: the disk is full, a
\* file is missing. Its failure is recorded
\* (BackgroundHealth::record_failure, src/engine/background_health.rs) and
\* stays recorded until that work next succeeds. A write that is stopped
\* while it is recorded is not handed a wait: it is told the failure
\* (RegolithEngine::stopped), because the stop will not clear while its
\* relief fails. Writer 2 was stopped a moment earlier, when the relief was
\* still working, and waits on the unit; then the relief fails. Writer 2
\* would wait on, while every write that arrives after it is told why. So
\* recording a failure lands the unit, and writer 2, writing again, is told
\* what a fresh write is told. When the relief succeeds again the record is
\* cleared, and a stopped write waits as before.
\*
\* The gap of example 2 opens a third time, and is closed the same way: the
\* failure is stored BEFORE the unit is taken, and a writer reads it again
\* once registered, as a fresh write would: only while a stop still holds
\* (RegolithEngine::stall_wait).
\*
\* What this model checks cannot happen: every writer has finished or
\* waits on the stall, the job is not running or still to relieve, no latch
\* and no recorded failure is on its way to land the unit, and a writer
\* waits: nobody is left to land its unit (NoStrandedWait). And: the engine
\* latched, its landing is done, and a writer waits (NoWaitOnceLatched).
\* And: the relief's failure is recorded, its landing is done, and a writer
\* waits (NoWaitOnceFailing).
\*
\* WHAT IS MODELLED, and the code each piece mirrors:
\*   stopped   whether writes are stopped now (StallSignal::classify)
\*   gate      who holds the gate: nobody, the job, or a writer
\*   job       the job's progress: not started, holding the gate, about to
\*             relieve after releasing it, finished
\*   wpc       each writer's progress (see TypeOK)
\*   progress  the progress count (StallSignal::progress)
\*   seen      the count each contended writer read before its step
\*   latched   whether the engine latched (RegolithEngine::is_latched)
\*   landing   whether a latch stored its flag and has yet to land the unit
\*   failing   whether the relief's last attempt failed and none has
\*             succeeded since (BackgroundHealth::failing)
\*   telling   whether a failure was recorded and has yet to land the unit
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
\*   - A database with a compaction worker. There a stopped writer runs no
\*     step: it waits for the worker's. The latch rule is the same, and is
\*     the case of this model where no writer ever holds the gate: after the
\*     latch nothing is promised to clear the stop, so the latch lands the
\*     unit.
\*   - Why the engine latched, and which thread did it: any thread, at any
\*     moment, once.
\*   - Which work failed and on which thread: the worker's flush or
\*     compaction, or a writer's own flush. Here the relief of the stop fails
\*     at any moment and recovers at any later one, as often as it likes. A
\*     failure of the other kind of work only lands the unit: the writers
\*     look again and wait again, which the model's landings already cover.
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
\*   MC_StallRelief_Green_Failures  the real code, with what can fail: the
\*                                  engine latching, and a rotation at the
\*                                  memtable cap whose seal may fail. Both
\*                                  rules hold.
\*   MC_StallRelief_Red_NoLatchLand the latch stores its flag and lands
\*                                  nothing (example 4): NoWaitOnceLatched
\*                                  breaks.
\*   MC_StallRelief_Red_NoLatchRecheck
\*                                  a writer registers without reading the
\*                                  latch's flag again (example 4, the
\*                                  gap): NoWaitOnceLatched breaks.
\*   MC_StallRelief_Red_NoRotateRefresh
\*                                  a rotation whose seal fails counts no
\*                                  progress (example 5): NoStrandedWait
\*                                  breaks.
\*   MC_StallRelief_Green_ReliefFails
\*                                  the real code, with a relief that fails
\*                                  and recovers (example 6). All three
\*                                  rules hold.
\*   MC_StallRelief_Red_NoFailLand  a failure is recorded and lands nothing:
\*                                  NoWaitOnceFailing breaks.
\*   MC_StallRelief_Red_NoFailRecheck
\*                                  a writer registers without reading the
\*                                  recorded failure again (example 6, the
\*                                  gap): NoWaitOnceFailing breaks.
\*
\* Lean, proofs/lean/Regolith/StallRelief.lean, proves the rules for any
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
  MaxSteps,
  \* Whether the run follows what can fail: the engine latching, and a
  \* rotation at the memtable cap, whose seal may fail. FALSE leaves the
  \* model as it was before those were added.
  Failures,
  \* Whether the run follows a relief that fails and recovers. FALSE leaves
  \* the model as it was before that was added.
  ReliefFails

\* The bug names this model knows.
ASSUME Mode \in {"Green", "NoRelief", "NoHandBack", "NoRecheck",
                 "NoLatchLand", "NoLatchRecheck", "NoRotateRefresh",
                 "NoFailLand", "NoFailRecheck"}

\* Failures is a yes or a no.
ASSUME Failures \in BOOLEAN

\* So is ReliefFails.
ASSUME ReliefFails \in BOOLEAN

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
  seen,
  \* Whether the engine latched: every write fails from then on.
  latched,
  \* Whether a latch stored its flag and has yet to land the unit.
  landing,
  \* Whether the relief's failure is recorded: a stopped write is told it.
  failing,
  \* Whether a failure was recorded and has yet to land the unit.
  telling

\* Every variable.
vars == <<stopped, gate, job, wpc, progress, seen, latched, landing, failing, telling>>

\* The two the latch owns, for the steps that leave them alone.
latch == <<latched, landing>>

\* The two the relief's failure owns, for the steps that leave them alone.
relief == <<failing, telling>>

\* The start: stopped or not, the gate free, the job not started, every
\* writer about to write, nothing counted, nothing latched, the relief
\* working.
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
  \* The engine takes writes, and no latch is under way.
  /\ latched = FALSE
  /\ landing = FALSE
  \* The relief works, and no failure is being told.
  /\ failing = FALSE
  /\ telling = FALSE

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
  /\ UNCHANGED <<stopped, wpc, progress, seen, latch, relief>>

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
  /\ UNCHANGED <<stopped, wpc, progress, seen, latch, relief>>

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
  \* The gate, what writers read and the latch are as they were.
  /\ UNCHANGED <<gate, seen, latch, relief>>

\* Writer w writes. On a latched engine it is told the latch and returns.
\* Not stopped: the write goes in, may bring on the stop, and leaves one
\* step owing; or, in a run that follows failures, it first has to rotate at
\* the memtable cap, flushing under the gate. Stopped, with the relief's
\* failure recorded: it is told that failure and returns. Stopped
\* otherwise: it relieves the stop itself when the gate is free; else it
\* reads the count and is contended.
WriterTry(w) ==
  \* The writer is about to write.
  /\ wpc[w] = "write"
  /\ IF latched
     \* Told the latch (admit_write, or the write itself): it returns.
     THEN /\ wpc' = [wpc EXCEPT ![w] = "done"]
          /\ UNCHANGED <<stopped, gate, seen>>
     ELSE IF ~stopped
          THEN \* Written; the stop may come on; one step owed.
               \/ /\ stopped' \in BOOLEAN
                  /\ wpc' = [wpc EXCEPT ![w] = "owing"]
                  /\ UNCHANGED <<gate, seen>>
               \* Or let in, and the memtable cap is reached: its rotation
               \* takes the free gate to flush (rotate_if_full). The stop
               \* may come on meanwhile.
               \/ /\ Failures
                  /\ gate = "free"
                  /\ gate' = w
                  /\ stopped' \in BOOLEAN
                  /\ wpc' = [wpc EXCEPT ![w] = "rotating"]
                  /\ UNCHANGED seen
          ELSE IF failing
               \* Stopped, and the relief's failure is recorded: told that
               \* failure (RegolithEngine::stopped), and it returns.
               THEN /\ wpc' = [wpc EXCEPT ![w] = "done"]
                    /\ UNCHANGED <<stopped, gate, seen>>
               ELSE IF gate = "free"
                    \* Stopped, gate free: its step takes the gate.
                    THEN /\ gate' = w
                         /\ wpc' = [wpc EXCEPT ![w] = "relieving"]
                         /\ UNCHANGED <<stopped, seen>>
                    \* Stopped, gate held: it read the count before its
                    \* step, and the step is contended.
                    ELSE /\ seen' = [seen EXCEPT ![w] = progress]
                         /\ wpc' = [wpc EXCEPT ![w] = "contended"]
                         /\ UNCHANGED <<stopped, gate>>
  \* Nothing else changes.
  /\ UNCHANGED <<job, progress, latch, relief>>

\* Writer w, contended, registers its wait on the unit, then looks again
\* (RegolithEngine::stall_wait, StallSignal::wait). The engine latched: it
\* lands the unit and is told the latch (bug NoLatchRecheck skips this
\* look). The stop cleared: it counts that and lands the unit (refresh).
\* The stop holds and the relief's failure is recorded: it lands the unit
\* and is told the failure (bug NoFailRecheck skips this look). The count
\* moved since it read it: it lands the unit (bug NoRecheck skips this
\* look). Otherwise it waits.
WriterRegister(w) ==
  \* The writer was contended.
  /\ wpc[w] = "contended"
  /\ IF latched /\ Mode # "NoLatchRecheck"
     \* Latched: landed for whoever else is on the unit, and w returns
     \* the latch.
     THEN /\ wpc' = [Land(wpc) EXCEPT ![w] = "done"]
          /\ UNCHANGED progress
     ELSE IF ~stopped
          \* Cleared: counted, landed, and w writes again.
          THEN /\ progress' = progress + 1
               /\ wpc' = [Land(wpc) EXCEPT ![w] = "write"]
          ELSE IF failing /\ Mode # "NoFailRecheck"
               \* The relief is failing: landed for whoever else is on
               \* the unit, and w returns the failure.
               THEN /\ wpc' = [Land(wpc) EXCEPT ![w] = "done"]
                    /\ UNCHANGED progress
               ELSE IF Mode # "NoRecheck" /\ seen[w] # progress
                    \* Progress it missed: landed, and w writes again.
                    THEN /\ wpc' = [Land(wpc) EXCEPT ![w] = "write"]
                         /\ UNCHANGED progress
                    \* Nothing missed: it waits.
                    ELSE /\ wpc' = [wpc EXCEPT ![w] = "waiting"]
                         /\ UNCHANGED progress
  \* Nothing else changes.
  /\ UNCHANGED <<stopped, gate, job, seen, latch, relief>>

\* Writer w's relieving step ends: the stop is left on or off, and the gate
\* released; its progress is counted next.
WriterStepEnd(w) ==
  \* The writer is relieving and holds the gate.
  /\ wpc[w] = "relieving"
  /\ stopped' \in Outcomes
  /\ gate' = "free"
  /\ wpc' = [wpc EXCEPT ![w] = "relRefresh"]
  \* Nothing else changes.
  /\ UNCHANGED <<job, progress, seen, latch, relief>>

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
  /\ UNCHANGED <<stopped, gate, job, seen, latch, relief>>

\* Writer w's owed step, after its commit: it takes the gate when free;
\* contended, it leaves the step owing for a next write and returns. On a
\* latched engine the step fails before it starts, and the writer returns.
OwedTry(w) ==
  \* The writer's write went in and left a step owing.
  /\ wpc[w] = "owing"
  /\ IF ~latched /\ gate = "free"
     \* The step takes the gate.
     THEN /\ gate' = w
          /\ wpc' = [wpc EXCEPT ![w] = "owedStep"]
     \* Contended, or latched: the writer returns.
     ELSE /\ wpc' = [wpc EXCEPT ![w] = "done"]
          /\ UNCHANGED gate
  \* Nothing else changes.
  /\ UNCHANGED <<stopped, job, progress, seen, latch, relief>>

\* Writer w's owed step ends: the stop is left on or off, and the gate
\* released.
OwedStepEnd(w) ==
  \* The owed step holds the gate.
  /\ wpc[w] = "owedStep"
  /\ stopped' \in Outcomes
  /\ gate' = "free"
  /\ wpc' = [wpc EXCEPT ![w] = "owedRefresh"]
  \* Nothing else changes.
  /\ UNCHANGED <<job, progress, seen, latch, relief>>

\* Writer w counts its owed step's progress, which lands the unit as Lands
\* says, and returns: it relieves nothing more.
OwedRefresh(w) ==
  \* The owed step released the gate.
  /\ wpc[w] = "owedRefresh"
  /\ progress' = progress + 1
  /\ wpc' = [(IF Lands(stopped) THEN Land(wpc) ELSE wpc) EXCEPT ![w] = "done"]
  \* Nothing else changes.
  /\ UNCHANGED <<stopped, gate, job, seen, latch, relief>>

\* Writer w's rotation ends its flush: the stop is left on or off, and the
\* gate released; the seal is next (rotate_full, src/engine/mod.rs).
RotateEnd(w) ==
  \* The rotation holds the gate.
  /\ wpc[w] = "rotating"
  /\ stopped' \in Outcomes
  /\ gate' = "free"
  /\ wpc' = [wpc EXCEPT ![w] = "rotLeave"]
  \* Nothing else changes.
  /\ UNCHANGED <<job, progress, seen, latch, relief>>

\* Writer w's rotation leaves (rotate_if_full). The seal goes through: the
\* progress is counted, lands the unit as Lands says, and the write goes in
\* and leaves a step owing. Or the seal fails: the real code counts the
\* progress all the same, and the writer returns its error; bug
\* NoRotateRefresh counts nothing.
RotateLeave(w) ==
  \* The rotation's flush is done and the gate released.
  /\ wpc[w] = "rotLeave"
  /\ \/ \* Sealed: counted, landed, and the write is in.
        /\ progress' = progress + 1
        /\ wpc' = [(IF Lands(stopped) THEN Land(wpc) ELSE wpc) EXCEPT ![w] = "owing"]
     \/ \* The seal failed.
        IF Mode # "NoRotateRefresh"
        \* Counted and landed on the way out, and w returns the error.
        THEN /\ progress' = progress + 1
             /\ wpc' = [(IF Lands(stopped) THEN Land(wpc) ELSE wpc) EXCEPT ![w] = "done"]
        \* The bug: w returns the error, and nothing is counted.
        ELSE /\ wpc' = [wpc EXCEPT ![w] = "done"]
             /\ UNCHANGED progress
  \* Nothing else changes.
  /\ UNCHANGED <<stopped, gate, job, seen, latch, relief>>

\* The engine latches, first half (RegolithEngine::latch): the flag is
\* stored, and every write is told the latch from now on. Any thread, at any
\* moment, once.
LatchFlag ==
  \* Only in a run that follows failures, and only once.
  /\ Failures
  /\ ~latched
  \* The flag is stored; the landing is owed.
  /\ latched' = TRUE
  /\ landing' = TRUE
  \* Nothing else changes.
  /\ UNCHANGED <<stopped, gate, job, wpc, progress, seen, relief>>

\* The engine latches, second half: the unit is landed, so every writer
\* waiting on it writes again and is told the latch. Bug NoLatchLand lands
\* nothing.
LatchLand ==
  \* The flag was stored and the landing is owed.
  /\ landing
  \* The landing is done.
  /\ landing' = FALSE
  \* The waiters wake, or, for the bug, stay.
  /\ wpc' = IF Mode # "NoLatchLand" THEN Land(wpc) ELSE wpc
  \* Nothing else changes.
  /\ UNCHANGED <<stopped, gate, job, progress, seen, latched, relief>>

\* The relief fails, first half (BackgroundHealth::record_failure): the
\* failure is stored, and a stopped write is told it from now on. Any
\* thread, at any moment the relief is not already failing.
FailFlag ==
  \* Only in a run that follows a failing relief, and only while it works.
  /\ ReliefFails
  /\ ~failing
  \* The failure is stored; the landing is owed.
  /\ failing' = TRUE
  /\ telling' = TRUE
  \* Nothing else changes.
  /\ UNCHANGED <<stopped, gate, job, wpc, progress, seen, latch>>

\* The relief fails, second half: the unit is landed, so every writer
\* waiting on it writes again and is told the failure. Bug NoFailLand lands
\* nothing.
FailLand ==
  \* A failure was stored and its landing is owed.
  /\ telling
  \* The landing is done.
  /\ telling' = FALSE
  \* The waiters wake, or, for the bug, stay.
  /\ wpc' = IF Mode # "NoFailLand" THEN Land(wpc) ELSE wpc
  \* Nothing else changes.
  /\ UNCHANGED <<stopped, gate, job, progress, seen, latch, failing>>

\* The relief succeeds again (BackgroundHealth::record_success): the record
\* is cleared, and a stopped write waits as before. A landing still owed
\* stays owed: it wakes the waiters once more, and they look again.
ReliefRecovers ==
  \* The failure is recorded.
  /\ failing
  \* It no longer is.
  /\ failing' = FALSE
  \* Nothing else changes.
  /\ UNCHANGED <<stopped, gate, job, wpc, progress, seen, latch, telling>>

\* Every step anyone can take.
Next ==
  \* The job starts, ends, or relieves.
  \/ JobStart \/ JobEnd \/ JobRelieve
  \* The engine latches.
  \/ LatchFlag \/ LatchLand
  \* The relief fails, tells the waiters, recovers.
  \/ FailFlag \/ FailLand \/ ReliefRecovers
  \* A writer writes, registers, steps, rotates or counts.
  \/ \E w \in Writers :
       \/ WriterTry(w) \/ WriterRegister(w) \/ WriterStepEnd(w) \/ WriterRefresh(w)
       \/ OwedTry(w) \/ OwedStepEnd(w) \/ OwedRefresh(w)
       \/ RotateEnd(w) \/ RotateLeave(w)

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
  \* relieving, counting either step, rotating, leaving its rotation,
  \* contended, waiting, or finished.
  /\ wpc \in [Writers -> {"write", "owing", "owedStep", "relieving", "relRefresh",
                          "owedRefresh", "rotating", "rotLeave", "contended",
                          "waiting", "done"}]
  \* The count is a number, and so is what each writer read.
  /\ progress \in Nat
  /\ seen \in [Writers -> Nat]
  \* The latch and its owed landing are each a yes or a no.
  /\ latched \in BOOLEAN
  /\ landing \in BOOLEAN
  \* So are the relief's recorded failure and its owed landing.
  /\ failing \in BOOLEAN
  /\ telling \in BOOLEAN

\* THE RULE. Once every writer has finished or waits on the stall, the job
\* is not running or still to relieve, and neither a latch nor a recorded
\* failure has its landing owed, no writer waits: someone was always on the
\* way to land its unit. Rules out the stories: writer 2 left waiting after
\* writer 1's last owed step, after a landing it registered too late for,
\* after the job, and after a rotation whose seal failed. Lean:
\* no_stranded_wait.
NoStrandedWait ==
  \* With nobody left but waiters ...
  (/\ job \notin {"holding", "relieving"}
   /\ ~landing
   /\ ~telling
   /\ \A w \in Writers : wpc[w] \in {"waiting", "done"})
    \* ... no writer waits.
    => \A w \in Writers : wpc[w] # "waiting"

\* THE LATCH'S RULE (E35). Once the engine latched and its landing is done,
\* no writer waits: a latched engine clears no stop, so a writer still
\* waiting then would wait until the database closes. Rules out example 4,
\* and its gap: a writer that registers after the latch landed the unit.
\* Lean: no_wait_once_latched.
NoWaitOnceLatched ==
  \* Latched, and the landing done ...
  (latched /\ ~landing)
    \* ... no writer waits.
    => \A w \in Writers : wpc[w] # "waiting"

\* THE FAILING RELIEF'S RULE (E36). While the relief's failure is recorded
\* and its landing is done, no writer waits: a write that arrives then is
\* told the failure, so one that was already waiting is told it too. Rules
\* out example 6, and its gap: a writer that registers after the failure
\* landed the unit. Once the relief recovers the rule asks nothing, and
\* writers wait for the stop again. Lean: no_wait_once_failing.
NoWaitOnceFailing ==
  \* The failure recorded, and the landing done ...
  (failing /\ ~telling)
    \* ... no writer waits.
    => \A w \in Writers : wpc[w] # "waiting"

====
