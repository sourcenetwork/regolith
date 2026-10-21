---- MODULE LandingLifetime ----
\* A completed I/O wait can remain queued while other tasks run. Its blocks
\* must stay landed until its caller resumes, however many other polls land.
\* An abandoned wait has no caller handles and can still age out.
\* Correspondence: live counts caller IoWait handles beyond Ledger's Arc;
\* held is the kept wait in Ledger; age is Ledger::round minus Kept::round.
\* Tick is Ledger::settle, Run and OtherRead are Ledger::seen with its
\* caller-ownership guard, and Drop is dropping an IoWait.
\* Rust: src/io_queue/ledger.rs:111 (seen), :141 (settle),
\* :116 and :149 (the two caller-ownership checks).
\* This supplies the delayed-resumption case omitted by LandingHold.tla;
\* its held-block invariant continues to apply between every caller run.
\* Finite bounds preserve the boundary: two clones and one age past expiry.
EXTENDS Naturals
\* The grace period and the guard mutation under test.
CONSTANTS Keep, Mutant
\* At least one poll of grace, and only the calibrated mutations.
ASSUME Keep > 0 /\ Mutant \in {"none", "ExpireLive", "LeakAbandoned", "ConsumeLive"}
\* Caller handles still alive.
VARIABLE live
\* Polls since the completed wait, saturated past the grace period.
VARIABLE age
\* Whether the completed wait still protects its landing.
VARIABLE held
\* Whether the caller consumed its result.
VARIABLE done
\* The complete model state.
vars == <<live, age, held, done>>
\* Start immediately after a wait completed, before its caller resumes.
Init == live = 1 /\ age = 0 /\ held = TRUE /\ done = FALSE
\* A caller may clone its wait before either copy resumes.
Clone == live > 0 /\ live < 2 /\ ~done /\ live' = live + 1
         \* Cloning does not change the landing or its age.
         /\ UNCHANGED <<age, held, done>>
\* A caller may abandon a handle; the last one leaves only Ledger's Arc.
Drop == live > 0 /\ live' = live - 1 /\ UNCHANGED <<age, held, done>>
\* A ready caller reads the protected landing and completes.
Run == live > 0 /\ held /\ ~done /\ live' = 0 /\ done' = TRUE
       \* Consuming the result releases its retained landing.
       /\ held' = FALSE /\ UNCHANGED age
\* Another reader consumes the same blocks, without consuming our wait.
OtherRead == held /\ held' = (live > 0 /\ Mutant # "ConsumeLive")
             \* Its read changes none of our caller's ownership or timing.
             /\ UNCHANGED <<live, age, done>>
\* Other work lands; its poll ages this completed wait.
Tick ==
    \* Saturating age keeps the state graph finite without changing expiry.
    /\ age' = IF age < Keep + 1 THEN age + 1 ELSE age
    \* Only old waits without a caller may expire. Both guards are calibrated.
    /\ held' = (held /\ ~(age' > Keep /\ Mutant # "LeakAbandoned"
                         /\ (live = 0 \/ Mutant = "ExpireLive")))
    \* A poll neither invents caller handles nor completes a call.
    /\ UNCHANGED <<live, done>>
\* Any caller action or unrelated landing may be next.
Next == Clone \/ Drop \/ Run \/ OtherRead \/ Tick
\* Polls continue, and a caller that remains ready eventually runs.
Spec == Init /\ [][Next]_vars /\ WF_vars(Tick) /\ WF_vars(Run)
\* Every state stays within the finite representation.
TypeOK == live \in 0..2 /\ age \in 0..(Keep + 1)
          \* Ownership and completion are Boolean facts.
          /\ held \in BOOLEAN /\ done \in BOOLEAN
\* A caller waiting to resume never loses its already completed I/O.
LiveLandingRetained == live > 0 => held
\* Once all callers abandon a protected landing, later polls release it.
AbandonedReleased == (live = 0 /\ held) ~> ~held
====
