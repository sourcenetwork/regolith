---- MODULE OwedStep ----
\* ===========================================================================
\* THE STORY, for a reader who has never seen the code
\* ===========================================================================
\* regolith keeps new writes in memory, in a "memtable". When the memtable is
\* full it is "sealed" and has to be written out to a file: a "flush". The
\* files a flush writes land in "L0", the top level of the tree. When L0
\* holds too many files they are merged into the next level: a "compaction".
\* Every read looks at every L0 file, so a growing L0 makes every read
\* slower, and past a limit the database stops accepting writes.
\*
\* Usually a background thread, the "worker", flushes and compacts. A
\* database opened with no worker (for example on a wasm target that has no
\* threads) has nobody to do that. So the writes do it themselves:
\*   - a write that seals a memtable leaves one step of background work
\*     "owed";
\*   - the next write to come out of the commit pipeline runs exactly ONE
\*     step, then returns to its caller;
\*   - one step is one flush of the oldest sealed memtable, or, when nothing
\*     is sealed, one compaction pass;
\*   - a step that did work owes the next step, and so does every flush.
\* That way the writes pace the background work and no write pays for more
\* than one step.
\*
\* Tiny example, with a memtable of two writes and a trigger of two files:
\*   write 2 seals, and its step flushes:            L0 = 1
\*   write 3 runs a pass, which finds nothing to do:  L0 = 1
\*   write 4 seals, and its step flushes:            L0 = 2, the trigger
\*   write 5 runs a pass, which compacts L0:          L0 = 0
\* L0 never passes 2, and no write ran more than one step.
\*
\* WHAT WENT WRONG BEFORE (E16). A flush owed nothing. In the example, write
\* 5 would then run no step at all (nothing owed), write 6 would seal and
\* flush, and L0 would be 3, then 4, and so on until the database stopped
\* writes. The other way to get it wrong is a write that keeps running steps
\* until nothing is owed: the caller of one small write then waits for a
\* flush, a compaction and whatever follows.
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/OwedStep.lean:
\*   write_one_step           a write runs one step when one is owed as it
\*                            leaves the pipeline, none otherwise
\*                            (OneStepPerWrite, ExactlyTheOwedStep here)
\*   write_inv, l0_bounded    with at least two writes per memtable, L0
\*                            never passes its trigger and no sealed
\*                            memtable is left waiting (L0Bounded,
\*                            FrozenBounded here, for any sizes)
\*   stopped_write_inv, l0_bounded_by_stop
\*                            for any memtable size, L0 never passes the
\*                            stop trigger
\*   flush_owes_nothing_overfills, step_until_idle_runs_three
\*                            the RED cases, as counterexamples
\*
\* THE ENGINE (src/engine/background_step.rs unless said otherwise).
\*   RegolithEngine::flush_sealed_later   a seal with no worker owes a step
\*   RegolithEngine::after_flush          so does every flush (E16)
\*   RegolithEngine::run_owed_step        called by a write once its commit
\*     returned (submit_settled, src/engine/commit/mod.rs); `run_owed`
\*     takes the debt and runs one `run_one_background_step`: a flush of the
\*     oldest sealed memtable, else one compaction pass. `DidWork` owes the
\*     next step; `Idle` owes nothing.
\*   pick_and_run_level_compaction        src/engine/compaction.rs: a pass
\*     looks at L0 first, and `compact_l0` merges all of L0 into L1.
\*   RegolithEngine::relieve_inline       src/engine/mod.rs: a write stopped
\*     because L0 reached the stop trigger runs steps until the stop clears.
\*
\* THE DEFECTS, one per mutant value.
\*   "FlushOwesNothing"  a step that flushed leaves nothing owed (the engine
\*                       before E16).
\*   "StepUntilIdle"     a write keeps running steps while one is owed.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - Several threads writing at once. A step can then find another thread
\*     flushing or compacting, do nothing, and owe again; and writes can
\*     outrun the one thread that works. The bound on L0 is then the stop
\*     trigger's, and how a stop is relieved is StallRelief.tla. Here one
\*     write runs at a time: a database with no worker used from one thread.
\*   - Where the step runs: inline, or as a job on the writing thread's own
\*     queue (NonBlocking.tla). Either way it is one step for that write.
\*   - What the deeper levels hold. A pass that leaves L0 alone may still
\*     find work below it; the model lets it go either way (see RunOwed).
\*   - A step that fails. It owes nothing more until the next seal, and the
\*     failure is reported where the step records it.
\*   - The bytes: a memtable is "full" after SealEvery writes.
\*
\* CONFIGURATIONS.
\*   MC_OwedStep_Green                   two writes per memtable: L0 stays
\*                                       at its trigger
\*   MC_OwedStep_Green_TinyMemtable      every write seals: L0 stays within
\*                                       the stop trigger
\*   MC_OwedStep_Red_FlushOwesNothing    L0Bounded fails
\*   MC_OwedStep_Red_StepUntilIdle       OneStepPerWrite fails

\* Borrow the standard definitions of numbers.
EXTENDS Naturals

\* The knobs of a run. Each configuration file (MC_OwedStep_*.cfg) gives them values.
CONSTANTS
  \* How many writes fill a memtable: the write that fills it seals it. It stands for
  \* `write_buffer_size` (src/options.rs), counted in writes.
  SealEvery,
  \* How many L0 files make a pass compact L0: `l0_compaction_trigger` (src/options.rs).
  Trigger,
  \* How many L0 files stop writes: `level0_stop_writes_trigger` (src/options.rs).
  Stop,
  \* "none" for the design, or the name of one planted bug.
  Mutant

\* TLC refuses a configuration with a memtable that holds no write,
ASSUME SealEvery \in Nat \ {0}
\* with a trigger of no file,
ASSUME Trigger \in Nat \ {0}
\* with a stop trigger below the compaction trigger,
ASSUME Stop \in Nat /\ Stop >= Trigger
\* or that names no known bug.
ASSUME Mutant \in {"none", "FlushOwesNothing", "StepUntilIdle"}

\* The state: everything that changes from one step to the next. Each line says what the variable
\* stands for in the real program.
VARIABLES
  \* How many writes the active memtable holds (MemTable, src/engine/memtable.rs). A number.
  filled,
  \* How many sealed memtables wait for their flush: the frozen list of the read view
  \* (ReadView::frozen, src/engine/read_view.rs). A number.
  frozen,
  \* How many files L0 holds (Version::levels[0], src/engine/manifest.rs). A number.
  l0,
  \* TRUE when one step of background work is owed: the OWED_STEP bit of RegolithEngine::owed, an
  \* atomic byte (src/engine/background_step.rs).
  owed,
  \* Where the one writer is: "idle" (between writes) or "left" (its commit returned and it has
  \* yet to run what is owed).
  pc,
  \* A ghost (bookkeeping the program does not have; it only lets the promises be stated): how
  \* many steps the current write has run since its commit returned.
  ran,
  \* A ghost: whether a step was owed at the moment the current write's commit returned.
  owedAtLeave

\* Every variable, so a step that changes none of them is a stutter.
vars == <<filled, frozen, l0, owed, pc, ran, owedAtLeave>>

----------------------------------------------------------------------------
\* Actions.

\* The start: an empty memtable, nothing sealed, an empty L0, nothing owed, no write under way.
Init ==
  \* The memtable is empty.
  /\ filled = 0
  \* Nothing is sealed.
  /\ frozen = 0
  \* L0 is empty.
  /\ l0 = 0
  \* Nothing is owed.
  /\ owed = FALSE
  \* No write is under way.
  /\ pc = "idle"
  \* No step was run.
  /\ ran = 0
  \* Nothing was owed.
  /\ owedAtLeave = FALSE

\* A write goes through the commit pipeline. The write that fills the memtable seals it and
\* swaps in a fresh one; with no worker, that seal owes one step (flush_sealed_later).
Commit ==
  \* When: no write is under way,
  /\ pc = "idle"
  \* and writes are not stopped.
  /\ l0 < Stop
  \* Does this write fill the memtable?
  /\ LET seals == filled + 1 = SealEvery
     \* The memtable: fresh after a seal, else one write fuller.
     IN /\ filled' = IF seals THEN 0 ELSE filled + 1
        \* A seal adds one memtable to those waiting for a flush.
        /\ frozen' = IF seals THEN frozen + 1 ELSE frozen
        \* A seal owes a step; an earlier debt stays.
        /\ owed' = (owed \/ seals)
        \* The ghost notes whether a step is owed as the commit returns.
        /\ owedAtLeave' = (owed \/ seals)
  \* The write has run no step yet.
  /\ ran' = 0
  \* Its commit has returned; what is owed comes next.
  /\ pc' = "left"
  \* L0 is untouched by a commit.
  /\ UNCHANGED l0

\* The write runs what is owed (run_owed_step). Nothing owed: it returns. A step owed: it takes
\* the debt and runs ONE step, a flush if a sealed memtable waits, else a compaction pass, and
\* returns. A step that did work owes the next one. The bug FlushOwesNothing forgets the debt
\* after a flush; the bug StepUntilIdle goes round again while a step is owed.
RunOwed ==
  \* When: the write's commit has returned.
  /\ pc = "left"
  \* Is a step owed?
  /\ IF ~owed
       \* Nothing owed: the write returns, having changed nothing.
       THEN /\ pc' = "idle"
            \* No step ran.
            /\ UNCHANGED <<frozen, l0, owed, ran>>
       \* A step is owed. Does a sealed memtable wait?
       ELSE /\ IF frozen > 0
                 \* Yes: flush the oldest. One sealed memtable fewer,
                 THEN /\ frozen' = frozen - 1
                      \* one file more in L0,
                      /\ l0' = l0 + 1
                      \* and the flush owes the next step (the bug owes nothing).
                      /\ owed' = (Mutant # "FlushOwesNothing")
                 \* No: a compaction pass. Is L0 at its trigger?
                 ELSE IF l0 >= Trigger
                        \* Yes: the pass merges all of L0 into the next level,
                        THEN /\ l0' = 0
                             \* and, having done work, owes the next step.
                             /\ owed' = TRUE
                             \* Nothing is sealed.
                             /\ UNCHANGED frozen
                        \* No: L0 is left alone. The pass either found work in a deeper level
                        \* (and owes the next step) or found nothing (and owes nothing).
                        ELSE /\ owed' \in BOOLEAN
                             \* L0 and the sealed memtables are untouched.
                             /\ UNCHANGED <<frozen, l0>>
            \* One more step ran in this write.
            /\ ran' = ran + 1
            \* The design returns after the one step; the bug StepUntilIdle goes round again
            \* while a step is owed.
            /\ pc' = IF Mutant = "StepUntilIdle" /\ owed' THEN "left" ELSE "idle"
  \* The memtable and the ghost of the commit are untouched.
  /\ UNCHANGED <<filled, owedAtLeave>>

\* A write that finds L0 at the stop trigger is stopped, and relieves the stop on its own
\* thread (relieve_inline): the same background step, a flush if a sealed memtable waits, else a
\* compaction pass, which at the stop trigger always has L0 to merge.
Relieve ==
  \* When: no write is under way,
  /\ pc = "idle"
  \* and writes are stopped.
  /\ l0 >= Stop
  \* Does a sealed memtable wait?
  /\ IF frozen > 0
       \* Yes: flush the oldest. One sealed memtable fewer,
       THEN /\ frozen' = frozen - 1
            \* one file more in L0,
            /\ l0' = l0 + 1
            \* and the flush owes a step.
            /\ owed' = TRUE
       \* No: the pass merges all of L0 away (the stop trigger is not below the compaction
       \* trigger).
       ELSE /\ l0' = 0
            \* Nothing is sealed, and the debt is as it was.
            /\ UNCHANGED <<frozen, owed>>
  \* The memtable, the writer and the ghosts are untouched.
  /\ UNCHANGED <<filled, pc, ran, owedAtLeave>>

\* Every step the system can take.
Next ==
  \* A write commits, or runs what is owed, or a stopped write relieves the stop.
  \/ Commit \/ RunOwed \/ Relieve

\* Every behaviour: start in Init, then take Next steps or stutter.
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Invariants.

\* The most files L0 may ever hold. With at least two writes per memtable the write after the
\* flush that fills L0 does not seal, so its step is the compaction: the bound is the compaction
\* trigger. When every write seals, every step is a flush, and it is the stop trigger that makes
\* a write compact: the bound is the stop trigger.
L0Limit == IF SealEvery >= 2 THEN Trigger ELSE Stop

\* Every variable holds what its comment says.
TypeOK ==
  \* The memtable is never fuller than full.
  /\ filled \in 0..(SealEvery - 1)
  \* The sealed memtables are counted by a number.
  /\ frozen \in Nat
  \* So are the L0 files.
  /\ l0 \in Nat
  \* A step is owed or not.
  /\ owed \in BOOLEAN
  \* The writer is between writes or after its commit.
  /\ pc \in {"idle", "left"}
  \* The steps a write ran are counted by a number.
  /\ ran \in Nat
  \* A step was owed at the commit's return or not.
  /\ owedAtLeave \in BOOLEAN

\* A write runs at most one step. Example ruled out: the write that seals a memtable flushes it,
\* then compacts L0, then runs a third pass, all before it returns to a caller that asked for
\* one small write. The program needs this because the step is paid on the caller's own thread:
\* it must be bounded. Lean: write_one_step.
OneStepPerWrite ==
  \* The steps of the current write are 0 or 1.
  ran <= 1

\* A write that has returned ran exactly what was owed when its commit returned: one step if a
\* step was owed, none if not. Example ruled out: a step is owed and the write returns without
\* running it, so the sealed memtable sits in memory until some later write. Lean: write_one_step.
ExactlyTheOwedStep ==
  \* Once the write has returned,
  pc = "idle" =>
    \* it ran one step if one was owed, and none otherwise.
    ran = (IF owedAtLeave THEN 1 ELSE 0)

\* THE HEADLINE. L0 never holds more files than its limit. Example ruled out: a trigger of 2,
\* and an L0 of 3 files because the write after the flush that filled L0 ran no compaction. The
\* program needs this because every read looks at every L0 file. Lean: l0_bounded,
\* l0_bounded_by_stop.
L0Bounded ==
  \* The L0 files are within the limit.
  l0 <= L0Limit

\* At most one sealed memtable waits for its flush: the write that seals one flushes it before it
\* returns. Example ruled out: sealed memtables piling up in memory because nobody flushes them.
\* Lean: l0_bounded (its second half).
FrozenBounded ==
  \* Zero or one sealed memtable waits.
  frozen <= 1

====
