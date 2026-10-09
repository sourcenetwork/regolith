---- MODULE Allocate ----
\* Conflict-free allocation (plan 3.7): `Db::allocate(key, n)` reserves n
\* values from a u64 counter at `key` in the ordered step and returns them
\* as a range. It is unique, monotonic and never a conflict; it does no I/O
\* on the caller's thread; and its record is durable no later than the
\* first commit that uses one of its values, across crashes.
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
\* THE DESIGN (plan 3.7; the code is not written yet).
\*   Db::allocate     runs in the ordered step: it reads the counter key
\*     from the decided prefix (the log), reserves [c + 1, c + n], and
\*     writes an allocation record with the new counter to the WAL. It
\*     returns without a sync: no I/O on the caller.
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
\*   - The ordered step is sequential (the commit mutex or the decide stage
\*     of 4.7), so each allocation is one step; group commit adds nothing a
\*     sequential order of records does not have.
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

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Clients,     \* the callers of allocate, strings
  N,           \* the values each caller reserves
  MayAbort,    \* callers whose transaction may abort after allocating
  Durability,  \* "Immediate" or "Eventual"
  MaxCrashes,  \* the most power cuts the model injects
  Mutant       \* "none" (the design), "InTxn" or "LogAfterUse"

ASSUME N \in Nat \ {0} /\ MayAbort \subseteq Clients /\ MaxCrashes \in Nat
ASSUME Durability \in {"Immediate", "Eventual"}
ASSUME Mutant \in {"none", "InTxn", "LogAfterUse"}

VARIABLES
  wal,      \* the records written, in log order (see below)
  durable,  \* how many leading records a sync made durable
  phase,    \* [Clients -> Phases]: where each caller is
  held,     \* [Clients -> SUBSET Nat]: the values allocate returned to it
  snap,     \* [Clients -> Nat]: InTxn only, the counter its snapshot read
  mem,      \* LogAfterUse only: the in-memory counter, ahead of the log
  late,     \* LogAfterUse only: allocation records handed out, not logged
  crashes   \* the power cuts so far

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
  [kind |-> "alloc", c |-> c, lo |-> lo, hi |-> hi, uses |-> {}, counter |-> hi]

\* The commit record of caller c using values us; ctr is its counter write.
CommitRec(c, us, ctr) ==
  [kind |-> "commit", c |-> c, lo |-> 0, hi |-> 0, uses |-> us, counter |-> ctr]

\* The counter key after the first n records: the last value written to
\* it, 0 when absent.
CounterIn(n) ==
  LET ks == {k \in 1..n : wal[k].counter # 0}
  IN IF ks = {} THEN 0 ELSE wal[Max(ks)].counter

\* The values record k allocates: an allocation's range, or, for an InTxn
\* commit that writes the counter, the values it took.
AllocOf(k) ==
  CASE wal[k].kind = "alloc"  -> wal[k].lo..wal[k].hi
    [] wal[k].counter # 0     -> wal[k].uses
    [] OTHER                  -> {}

----------------------------------------------------------------------------
\* Actions.

\* The start: an empty log, no caller begun, the counter absent.
Init ==
  /\ wal     = <<>>
  /\ durable = 0
  /\ phase   = [c \in Clients |-> "idle"]
  /\ held    = [c \in Clients |-> {}]
  /\ snap    = [c \in Clients |-> 0]
  /\ mem     = 0
  /\ late    = <<>>
  /\ crashes = 0

\* The design: caller c's allocate runs in the ordered step. It reads the
\* counter from the log, reserves the next N values, and writes the
\* allocation record. Nothing is synced: no I/O on the caller.
\* LogAfterUse: the values come from the in-memory counter and the record
\* waits in `late`.
Allocate(c) ==
  /\ Mutant # "InTxn"
  /\ phase[c] = "idle"
  /\ LET base == IF Mutant = "LogAfterUse" THEN mem ELSE CounterIn(Len(wal))
         r    == AllocRec(c, base + 1, base + N)
     IN /\ held' = [held EXCEPT ![c] = (base + 1)..(base + N)]
        /\ IF Mutant = "LogAfterUse"
             THEN /\ mem'  = base + N
                  /\ late' = Append(late, r)
                  /\ UNCHANGED wal
             ELSE /\ wal' = Append(wal, r)
                  /\ UNCHANGED <<mem, late>>
  /\ phase' = [phase EXCEPT ![c] = "holding"]
  /\ UNCHANGED <<durable, snap, crashes>>

\* LogAfterUse only: the oldest lazily logged allocation reaches the WAL.
LogLate ==
  /\ late # <<>>
  /\ wal'  = Append(wal, Head(late))
  /\ late' = Tail(late)
  /\ UNCHANGED <<durable, phase, held, snap, mem, crashes>>

\* Caller c's transaction commits, using every value it holds. Under
\* Immediate the commit syncs the WAL, which makes every earlier record
\* durable too.
Commit(c) ==
  /\ phase[c] = "holding"
  /\ wal'     = Append(wal, CommitRec(c, held[c], 0))
  /\ durable' = IF Durability = "Immediate" THEN Len(wal) + 1 ELSE durable
  /\ phase'   = [phase EXCEPT ![c] = "done"]
  /\ UNCHANGED <<held, snap, mem, late, crashes>>

\* InTxn only: caller c's transaction reads the counter in its snapshot.
BeginInTxn(c) ==
  /\ Mutant = "InTxn"
  /\ phase[c] = "idle"
  /\ snap'  = [snap EXCEPT ![c] = CounterIn(Len(wal))]
  /\ phase' = [phase EXCEPT ![c] = "open"]
  /\ UNCHANGED <<wal, durable, held, mem, late, crashes>>

\* InTxn only: the transaction commits counter = snapshot + N and uses the
\* values it took. Its read of the counter is validated: if another commit
\* wrote the counter since, it aborts on the conflict.
CommitInTxn(c) ==
  /\ Mutant = "InTxn"
  /\ phase[c] = "open"
  /\ IF CounterIn(Len(wal)) = snap[c]
       THEN /\ wal'     = Append(wal, CommitRec(c, (snap[c] + 1)..(snap[c] + N), snap[c] + N))
            /\ durable' = IF Durability = "Immediate" THEN Len(wal) + 1 ELSE durable
            /\ held'    = [held EXCEPT ![c] = (snap[c] + 1)..(snap[c] + N)]
            /\ phase'   = [phase EXCEPT ![c] = "done"]
       ELSE /\ phase'   = [phase EXCEPT ![c] = "conflict"]
            /\ UNCHANGED <<wal, durable, held>>
  /\ UNCHANGED <<snap, mem, late, crashes>>

\* Caller c's transaction aborts by its own logic after allocating. Its
\* values stay reserved and unused: a gap.
Abort(c) ==
  /\ c \in MayAbort
  /\ phase[c] \in {"open", "holding"}
  /\ phase' = [phase EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<wal, durable, held, snap, mem, late, crashes>>

\* A sync makes every written record durable: a background sync under
\* Eventual, or any other commit's sync.
Sync ==
  /\ durable < Len(wal)
  /\ durable' = Len(wal)
  /\ UNCHANGED <<wal, phase, held, snap, mem, late, crashes>>

\* A power cut keeps a gap-free prefix of the records holding every
\* durable one. Callers in the middle of a transaction die with the
\* process. The in-memory counter is rebuilt from the recovered log, and
\* lazily logged allocations are gone.
Crash ==
  /\ crashes < MaxCrashes
  /\ \E k \in durable..Len(wal) :
       /\ wal'     = SubSeq(wal, 1, k)
       /\ durable' = k
       /\ mem'     = IF Mutant = "LogAfterUse"
                       THEN LET ks == {j \in 1..k : wal[j].counter # 0}
                            IN IF ks = {} THEN 0 ELSE wal[Max(ks)].counter
                       ELSE mem
  /\ phase'   = [c \in Clients |-> IF phase[c] \in {"open", "holding"} THEN "lost" ELSE phase[c]]
  /\ late'    = <<>>
  /\ crashes' = crashes + 1
  /\ UNCHANGED <<held, snap>>

\* Every step the system can take.
Next ==
  \/ \E c \in Clients : Allocate(c) \/ Commit(c) \/ BeginInTxn(c) \/ CommitInTxn(c) \/ Abort(c)
  \/ LogLate
  \/ Sync
  \/ Crash

\* Every behaviour: start in Init, then take Next steps or stutter.
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ durable \in 0..Len(wal)
  /\ phase \in [Clients -> Phases]
  /\ held \in [Clients -> SUBSET Nat]
  /\ snap \in [Clients -> Nat]
  /\ mem \in Nat
  /\ crashes \in 0..MaxCrashes

\* Allocation never aborts a transaction.
INV_NeverConflicts == \A c \in Clients : phase[c] # "conflict"

\* No value is handed out by two allocation records in the log (which holds
\* every durable one). Lean: ranges_disjoint.
INV_Unique ==
  \A j, k \in 1..Len(wal) : j # k => AllocOf(j) \cap AllocOf(k) = {}

\* The ranges only grow: in log order, each allocation starts after every
\* earlier one ends. Lean: ranges_grow.
INV_Monotonic ==
  \A j, k \in 1..Len(wal) :
    j < k /\ AllocOf(j) # {} /\ AllocOf(k) # {} => Max(AllocOf(j)) < Min(AllocOf(k))

\* A committed use implies its allocation is durable: every value a durable
\* commit record uses is allocated by a durable record. Lean: uses_allocated.
INV_UseDurable ==
  \A i \in 1..durable :
    wal[i].kind = "commit" => \A v \in wal[i].uses : \E j \in 1..durable : v \in AllocOf(j)

\* No value is used by two commits the log holds. Lean: alloc_fresh.
INV_UsesUnique ==
  \A j, k \in 1..Len(wal) :
    j # k /\ wal[j].kind = "commit" /\ wal[k].kind = "commit" => wal[j].uses \cap wal[k].uses = {}

====
