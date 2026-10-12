---- MODULE Allocate ----
\* ===========================================================================
\* THE STORY
\* ===========================================================================
\* Programs need fresh numbers: the next document id, the next field id.
\* `Db::allocate(key, n)` (src/allocate.rs) hands out the next n numbers of a
\* counter stored under `key`, as a range. Two callers must never get the
\* same number, not at the same moment and not after a power cut either.
\*
\* The counter is not part of any transaction. The reservation happens in the
\* one step of the engine that handles one write at a time, the ordered step
\* (RegolithEngine::allocate, src/engine/commit/allocate.rs): it reads the
\* counter, adds n, and writes the new counter to the write-ahead log before
\* it returns. It does not wait for the disk.
\*
\* Tiny example of what can go wrong. Suppose the counter lived only in
\* memory and its record reached the log later. A caller is handed 1, and
\* commits a document with id 1; that commit is synced to disk. The power is
\* cut before the record "1 was handed out" reaches the disk. After the
\* restart the counter is 0 again, the next caller is handed 1 as well, and
\* two documents carry id 1. Because the engine writes the reservation before
\* allocate returns, the log always holds it ahead of any commit that uses
\* the value, and a power cut keeps a front part of the log: whenever the
\* use survives, so does the reservation.
\*
\* What this model shows: over every interleaving of a few callers, commits,
\* aborts, syncs and a power cut, no number is handed out twice, ranges only
\* grow, allocation never makes a transaction fail, and a number used by a
\* commit that survived is never handed out again. (Plan 3.7.)
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/Allocate.lean:
\*   step_inv, reachable_inv   every allocation starts right after the
\*                             counter the older records left, and every use
\*                             is covered by an allocation earlier in the
\*                             log, after any allocations, uses and crashes
\*   ranges_disjoint           two allocation records never share a value
\*   ranges_grow               a later allocation starts after an earlier ends
\*   uses_allocated            every use in the log has its allocation
\*                             before it, so in any prefix a crash keeps
\*   alloc_fresh               a new range shares no value with any
\*                             allocation or use the log holds, so a value
\*                             used by a surviving commit is never reissued
\*   log_after_use_reissues    the RED LogAfterUse, as a counterexample
\*   design_refuses_use_before_alloc
\*                             the design cannot log a use before its
\*                             allocation
\* TLC checks the invariants below over every interleaving of a few
\* callers, their commits and aborts, syncs and a power cut.
\*
\* THE DESIGN (plan 3.7), and the code that implements it.
\*   Db::allocate     runs in the ordered step (RegolithEngine::allocate
\*     and decide_allocation, src/engine/commit/allocate.rs: it takes a slot
\*     of the commit ring like a write, decided in ring order): it reads the
\*     counter key from the decided prefix (the log), reserves
\*     [c + 1, c + n], and writes an allocation record with the new counter
\*     to the WAL (a put of the counter key, with durability Eventual). It
\*     returns without a sync: the caller does not wait for the device.
\*   A commit that uses a value is ordered after the allocation that
\*     returned it, because allocate returned before the commit began. So
\*     the WAL holds the allocation record first.
\*   Durability       a sync makes every written record durable; under
\*     Immediate each commit syncs. A power cut keeps a gap-free prefix of
\*     the records holding every durable one (WalRotation.tla). A surviving
\*     use therefore always has its allocation, and the recovered counter is
\*     at or above every surviving value.
\*   Aborts           a transaction that aborts after allocating leaves its
\*     values unused: gaps, like a SQL sequence.
\*
\* THE MISUSES (REDs).
\*   Mutant = "InTxn"        the counter is read and written inside the
\*     caller's transaction, as an ordinary validated write in its write
\*     set. Two concurrent allocators conflict on it.
\*   Mutant = "LogAfterUse"  allocate hands values out of an in-memory
\*     counter and logs the allocation record later (say, at the next
\*     flush). A commit using a value can reach the WAL, and be synced,
\*     before the allocation record. A crash then keeps the use and drops
\*     the allocation, the counter recovers too low, and the value is
\*     handed out again.
\*
\* READINGS CHOSEN WHERE THE PLAN LEAVES ROOM.
\*   - One counter key. Two keys are two copies of this model that share
\*     only the WAL order.
\*   - "No value is handed out twice among durable allocations" is checked
\*     over every allocation record in the log (INV_Unique), which contains
\*     the durable ones; an allocation a crash dropped is forgotten with its
\*     values, which no surviving use holds (INV_UseDurable).
\*   - "A committed use implies its allocation is durable" is checked on
\*     the durable prefix: every use in a durable commit record is covered
\*     by a durable allocation record (INV_UseDurable).
\*   - The ordered step is sequential (slots are decided one at a time, in
\*     ring order), so each allocation is one step; commits that share a
\*     sync add nothing a sequential order of records does not have.
\*   - A lazily logged allocation (LogAfterUse) is logged in the order it
\*     was handed out, so only the use-before-allocation order is wrong.
\*
\* CONFIGURATIONS. Each RED lists the invariants it is not about before the
\* one it names; each mutant also has a Teeth configuration, GREEN, that
\* checks those over its whole state space.
\*   MC_Allocate_Green_Immediate     every invariant holds
\*   MC_Allocate_Green_Eventual      every invariant holds
\*   MC_Allocate_Red_InTxn           INV_NeverConflicts fails
\*   MC_Allocate_Red_LogAfterUse     INV_UseDurable fails
\*   MC_Allocate_Red_LogAfterUse_Reuse
\*                                   INV_UsesUnique fails: the value really
\*                                   is used twice after a crash
\*   MC_Allocate_Teeth_InTxn, MC_Allocate_Teeth_LogAfterUse   GREEN

\* Borrow the standard TLA+ books: counting numbers, lists, and sizes of finite sets.
EXTENDS Naturals, Sequences, FiniteSets

\* The fixed inputs a configuration chooses.
CONSTANTS
  \* The callers of allocate, each named by a string.
  Clients,
  \* How many values each caller reserves in its one call (the `n` of Db::allocate).
  N,
  \* The callers whose transaction may give up after allocating, leaving its values unused.
  MayAbort,
  \* When a commit counts as done: "Immediate" (only once it is on disk) or "Eventual" (before
  \* that). DurabilityMode, src/options.rs.
  Durability,
  \* The largest number of power cuts the model injects.
  MaxCrashes,
  \* "none" for the design the engine implements, or the planted bug: "InTxn" or "LogAfterUse".
  Mutant

\* Each caller reserves at least one value, only callers may abort, and the power-cut budget is a
\* number.
ASSUME N \in Nat \ {0} /\ MayAbort \subseteq Clients /\ MaxCrashes \in Nat
\* The durability is one of the two modes.
ASSUME Durability \in {"Immediate", "Eventual"}
\* The mutant is "none" or one of the two planted bugs.
ASSUME Mutant \in {"none", "InTxn", "LogAfterUse"}

\* The state: everything that changes from one step to the next. Each line says what the variable
\* stands for in the real program.
VARIABLES
  \* The write-ahead log: the records written so far, in order (Wal, src/engine/wal.rs). Their two
  \* kinds are described under "Records" below.
  wal,
  \* How many records, counted from the start of the log, a sync has put safely on disk.
  durable,
  \* Where each caller is (Phases below).
  phase,
  \* The values allocate returned to each caller: the Range<u64> that Db::allocate hands back
  \* (src/allocate.rs).
  held,
  \* InTxn bug only: the counter value each caller's transaction read in its snapshot.
  snap,
  \* LogAfterUse bug only: a counter kept in memory, ahead of what the log holds.
  mem,
  \* LogAfterUse bug only: the allocation records already handed out but not yet written to the log,
  \* oldest first.
  late,
  \* How many power cuts happened so far.
  crashes

\* Every variable, so a step that changes none of them is a stutter.
vars == <<wal, durable, phase, held, snap, mem, late, crashes>>

\* A caller's phases: not begun, open (InTxn: its transaction has read the
\* counter), holding values, committed, aborted by its own logic, aborted
\* by a conflict on the counter, or killed by a power cut.
Phases == {"idle", "open", "holding", "done", "aborted", "conflict", "lost"}

\* The greatest element of a finite, nonempty set of naturals.
Max(S) == CHOOSE m \in S : \A n \in S : n <= m

\* The least element of a finite, nonempty set of naturals.
Min(S) == CHOOSE m \in S : \A n \in S : m <= n

----------------------------------------------------------------------------
\* Records. Every record is [kind, c, lo, hi, uses, counter]:
\*   an allocation: kind "alloc", the range [lo, hi], counter = hi, no uses;
\*   a commit: kind "commit", the values it uses, and counter = the new
\*     counter value when it writes the counter key (InTxn only), else 0.

\* The allocation record handing [lo, hi] to caller c.
AllocRec(c, lo, hi) ==
  \* A record of kind "alloc": the caller, the range, no uses, and the counter set to the range's
  \* last value.
  [kind |-> "alloc", c |-> c, lo |-> lo, hi |-> hi, uses |-> {}, counter |-> hi]

\* The commit record of caller c using values us; ctr is its counter write.
CommitRec(c, us, ctr) ==
  \* A record of kind "commit": the caller, no range, the values used, and the counter it writes (0
  \* for none).
  [kind |-> "commit", c |-> c, lo |-> 0, hi |-> 0, uses |-> us, counter |-> ctr]

\* The counter key after the first n records: the last value written to
\* it, 0 when absent.
CounterIn(n) ==
  \* ks: the records among the first n that wrote the counter.
  LET ks == {k \in 1..n : wal[k].counter # 0}
  \* None: the counter is 0. Otherwise the value the last of them wrote.
  IN IF ks = {} THEN 0 ELSE wal[Max(ks)].counter

\* The values record k allocates: an allocation's range, or, for an InTxn
\* commit that writes the counter, the values it took.
AllocOf(k) ==
  \* An allocation record: every value from lo to hi.
  CASE wal[k].kind = "alloc"  -> wal[k].lo..wal[k].hi
    \* A commit that writes the counter (InTxn bug): the values it used.
    [] wal[k].counter # 0     -> wal[k].uses
    \* Any other record: nothing.
    [] OTHER                  -> {}

----------------------------------------------------------------------------
\* Actions.

\* The start: an empty log, no caller begun, the counter absent.
Init ==
  \* The log is empty.
  /\ wal     = <<>>
  \* Nothing is on disk.
  /\ durable = 0
  \* No caller has begun.
  /\ phase   = [c \in Clients |-> "idle"]
  \* Nobody holds a value.
  /\ held    = [c \in Clients |-> {}]
  \* Nobody read the counter.
  /\ snap    = [c \in Clients |-> 0]
  \* The in-memory counter is 0.
  /\ mem     = 0
  \* No allocation waits to be logged.
  /\ late    = <<>>
  \* No power cut happened.
  /\ crashes = 0

\* The design: caller c's allocate runs in the ordered step. It reads the
\* counter from the log, reserves the next N values, and writes the
\* allocation record. Nothing is synced: no I/O on the caller.
\* LogAfterUse: the values come from the in-memory counter and the record
\* waits in `late`.
Allocate(c) ==
  \* Under the InTxn bug there is no such step: the counter is handled inside the transaction.
  /\ Mutant # "InTxn"
  \* The caller has not begun.
  /\ phase[c] = "idle"
  \* base: the counter the reservation starts after: the in-memory counter under the LogAfterUse
  \* bug, otherwise the counter the log holds.
  /\ LET base == IF Mutant = "LogAfterUse" THEN mem ELSE CounterIn(Len(wal))
         \* r: the allocation record for the next N values.
         r    == AllocRec(c, base + 1, base + N)
     \* The caller now holds those N values.
     IN /\ held' = [held EXCEPT ![c] = (base + 1)..(base + N)]
        \* Under the LogAfterUse bug:
        /\ IF Mutant = "LogAfterUse"
             \* the in-memory counter moves past them,
             THEN /\ mem'  = base + N
                  \* the record waits to be logged,
                  /\ late' = Append(late, r)
                  \* and the log is not written.
                  /\ UNCHANGED wal
             \* In the design the record is written to the log before allocate returns,
             ELSE /\ wal' = Append(wal, r)
                  \* and the bug's variables are untouched.
                  /\ UNCHANGED <<mem, late>>
  \* The caller holds values now.
  /\ phase' = [phase EXCEPT ![c] = "holding"]
  \* Nothing is synced: the on-disk count, the snapshots and the power cuts stay.
  /\ UNCHANGED <<durable, snap, crashes>>

\* LogAfterUse only: the oldest lazily logged allocation reaches the WAL.
LogLate ==
  \* Some allocation record waits to be logged.
  /\ late # <<>>
  \* The oldest one is written to the log.
  /\ wal'  = Append(wal, Head(late))
  \* It no longer waits.
  /\ late' = Tail(late)
  \* Nothing else changes.
  /\ UNCHANGED <<durable, phase, held, snap, mem, crashes>>

\* Caller c's transaction commits, using every value it holds. Under
\* Immediate the commit syncs the WAL, which makes every earlier record
\* durable too.
Commit(c) ==
  \* The caller holds values.
  /\ phase[c] = "holding"
  \* Its commit record, naming every value it uses, is written to the log.
  /\ wal'     = Append(wal, CommitRec(c, held[c], 0))
  \* Under Immediate the commit syncs the log: everything up to and including its record is on disk.
  /\ durable' = IF Durability = "Immediate" THEN Len(wal) + 1 ELSE durable
  \* The caller is done.
  /\ phase'   = [phase EXCEPT ![c] = "done"]
  \* Nothing else changes.
  /\ UNCHANGED <<held, snap, mem, late, crashes>>

\* InTxn only: caller c's transaction reads the counter in its snapshot.
BeginInTxn(c) ==
  \* Only under the InTxn bug.
  /\ Mutant = "InTxn"
  \* The caller has not begun.
  /\ phase[c] = "idle"
  \* Its transaction reads the counter the log holds now.
  /\ snap'  = [snap EXCEPT ![c] = CounterIn(Len(wal))]
  \* It is open.
  /\ phase' = [phase EXCEPT ![c] = "open"]
  \* Nothing else changes.
  /\ UNCHANGED <<wal, durable, held, mem, late, crashes>>

\* InTxn only: the transaction commits counter = snapshot + N and uses the
\* values it took. Its read of the counter is validated: if another commit
\* wrote the counter since, it aborts on the conflict.
CommitInTxn(c) ==
  \* Only under the InTxn bug.
  /\ Mutant = "InTxn"
  \* The caller's transaction is open.
  /\ phase[c] = "open"
  \* Is the counter still what the transaction read?
  /\ IF CounterIn(Len(wal)) = snap[c]
       \* Yes: it commits one record that uses the next N values and writes the new counter.
       THEN /\ wal'     = Append(wal, CommitRec(c, (snap[c] + 1)..(snap[c] + N), snap[c] + N))
            \* Under Immediate the commit syncs the log.
            /\ durable' = IF Durability = "Immediate" THEN Len(wal) + 1 ELSE durable
            \* The caller holds those values.
            /\ held'    = [held EXCEPT ![c] = (snap[c] + 1)..(snap[c] + N)]
            \* The caller is done.
            /\ phase'   = [phase EXCEPT ![c] = "done"]
       \* No, another commit wrote the counter: the transaction is refused on the conflict,
       ELSE /\ phase'   = [phase EXCEPT ![c] = "conflict"]
            \* and nothing is written.
            /\ UNCHANGED <<wal, durable, held>>
  \* Nothing else changes.
  /\ UNCHANGED <<snap, mem, late, crashes>>

\* Caller c's transaction aborts by its own logic after allocating. Its
\* values stay reserved and unused: a gap.
Abort(c) ==
  \* The caller is one that may abort.
  /\ c \in MayAbort
  \* Its transaction is under way.
  /\ phase[c] \in {"open", "holding"}
  \* It gives up.
  /\ phase' = [phase EXCEPT ![c] = "aborted"]
  \* Nothing is written; the values it held stay reserved.
  /\ UNCHANGED <<wal, durable, held, snap, mem, late, crashes>>

\* A sync makes every written record durable: a background sync under
\* Eventual, or any other commit's sync.
Sync ==
  \* Some record is not on disk yet.
  /\ durable < Len(wal)
  \* Now every written record is.
  /\ durable' = Len(wal)
  \* Nothing else changes.
  /\ UNCHANGED <<wal, phase, held, snap, mem, late, crashes>>

\* A power cut keeps a gap-free prefix of the records holding every
\* durable one. Callers in the middle of a transaction die with the
\* process. The in-memory counter is rebuilt from the recovered log, and
\* lazily logged allocations are gone.
Crash ==
  \* The power-cut budget is not used up.
  /\ crashes < MaxCrashes
  \* The log is cut at some record k: nothing on disk is lost, anything after may be.
  /\ \E k \in durable..Len(wal) :
       \* Only the first k records remain.
       /\ wal'     = SubSeq(wal, 1, k)
       \* All of them are on disk.
       /\ durable' = k
       \* Under the LogAfterUse bug the in-memory counter is rebuilt:
       /\ mem'     = IF Mutant = "LogAfterUse"
                       \* ks: the surviving records that wrote the counter;
                       THEN LET ks == {j \in 1..k : wal[j].counter # 0}
                            \* none: 0; otherwise the value the last of them wrote.
                            IN IF ks = {} THEN 0 ELSE wal[Max(ks)].counter
                       \* Without the bug the variable is unused.
                       ELSE mem
  \* Every caller in the middle of a transaction dies with the process.
  /\ phase'   = [c \in Clients |-> IF phase[c] \in {"open", "holding"} THEN "lost" ELSE phase[c]]
  \* The allocations that were waiting to be logged are gone.
  /\ late'    = <<>>
  \* One more power cut happened.
  /\ crashes' = crashes + 1
  \* What the callers were handed is not taken back: they may have shown it to the outside world.
  /\ UNCHANGED <<held, snap>>

\* Every step the system can take.
Next ==
  \* A caller allocates, commits, begins or commits under the InTxn bug, or aborts.
  \/ \E c \in Clients : Allocate(c) \/ Commit(c) \/ BeginInTxn(c) \/ CommitInTxn(c) \/ Abort(c)
  \* A waiting allocation record is logged (LogAfterUse bug).
  \/ LogLate
  \* The log is synced.
  \/ Sync
  \* The power is cut.
  \/ Crash

\* Every behaviour: start in Init, then take Next steps or stutter.
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  \* The on-disk count is at most the log's length.
  /\ durable \in 0..Len(wal)
  \* Every caller is in one of the seven phases.
  /\ phase \in [Clients -> Phases]
  \* Every caller holds a set of numbers.
  /\ held \in [Clients -> SUBSET Nat]
  \* Every snapshot counter is a number.
  /\ snap \in [Clients -> Nat]
  \* The in-memory counter is a number.
  /\ mem \in Nat
  \* No more power cuts than the budget.
  /\ crashes \in 0..MaxCrashes

\* Allocation never aborts a transaction.
\* Rules out, for example: two callers allocate at the same moment and one of their transactions is
\* refused because both wrote the counter key. Handing out ids must never cost a retry.
INV_NeverConflicts == \A c \in Clients : phase[c] # "conflict"

\* No value is handed out by two allocation records in the log (which holds
\* every durable one). Lean: ranges_disjoint.
INV_Unique ==
  \* Rules out, for example: two records in the log that both hand out the value 3. Two callers
  \* would then create two things with the same id.
  \A j, k \in 1..Len(wal) : j # k => AllocOf(j) \cap AllocOf(k) = {}

\* The ranges only grow: in log order, each allocation starts after every
\* earlier one ends. Lean: ranges_grow.
INV_Monotonic ==
  \* For every two records, the earlier one first:
  \A j, k \in 1..Len(wal) :
    \* if both allocate something, the largest value of the earlier is below the smallest of the
    \* later. Rules out, for example: a first call returning 3..4 and a later call returning 1..2.
    j < k /\ AllocOf(j) # {} /\ AllocOf(k) # {} => Max(AllocOf(j)) < Min(AllocOf(k))

\* A committed use implies its allocation is durable: every value a durable
\* commit record uses is allocated by a durable record. Lean: uses_allocated.
INV_UseDurable ==
  \* For every record on disk:
  \A i \in 1..durable :
    \* if it is a commit, each value it uses is allocated by some record on disk. Rules out, for
    \* example: a commit using value 1 is on disk while the record "1 was handed out" is not; after
    \* a power cut the counter restarts at 0 and 1 is handed out again.
    wal[i].kind = "commit" => \A v \in wal[i].uses : \E j \in 1..durable : v \in AllocOf(j)

\* No value is used by two commits the log holds. Lean: alloc_fresh.
INV_UsesUnique ==
  \* For every two different commit records in the log:
  \A j, k \in 1..Len(wal) :
    \* they use no value in common. Rules out, for example: after a power cut a second transaction
    \* is handed value 1 and commits with it, while the first transaction's use of 1 survived.
    j # k /\ wal[j].kind = "commit" /\ wal[k].kind = "commit" => wal[j].uses \cap wal[k].uses = {}

====
