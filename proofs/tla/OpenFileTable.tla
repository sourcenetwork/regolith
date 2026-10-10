---- MODULE OpenFileTable ----
\* ===========================================================================
\* THE STORY
\* ===========================================================================
\* A database keeps one file open for every table it reads. A big database,
\* or a process allowed only a few open files, runs out. So when
\* max_open_files is set, regolith keeps the open files in a small table of
\* "slots" (SlotTable, src/env/open_file_limit/slots.rs): one open file per
\* slot, never more slots than the limit. A read that finds its file in a
\* slot "joins" the slot; a read that does not "claims" a slot, closes the
\* file that was there, opens its own, and joins that.
\*
\* Tiny example. One slot, two threads. Thread 1 reads table A: it claims
\* the empty slot, opens A, reads, leaves. Thread 2 reads table B: the slot
\* holds A and nobody is reading it, so thread 2 claims it, closes A, opens B.
\* Meanwhile thread 1 comes back for A: it finds B in the slot, so it must
\* claim the slot again (later), never read B by mistake.
\*
\* What can go wrong, and what this model checks cannot happen:
\*   - more files open at once than the limit (AtMostCap);
\*   - a file closed while a thread is in the middle of reading it, so the
\*     read fails or reads freed memory (NeverClosedInUse);
\*   - a thread that saw its file in a slot joins just as the slot is
\*     reloaded with another file, and reads the wrong file (ReadsOwnFile).
\*
\* HOW A JOIN WORKS IN THE CODE (and here). A slot has a state word: its
\* phase (empty, claimed, open) and how many readers it has. A thread looks
\* at the word and at the slot's owner, then joins with one compare-and-swap
\* (CAS) on the word that adds one reader. The CAS only compares the word,
\* not the owner, so between the look and the CAS the slot could have been
\* claimed, reloaded with another file, read and left, ending with the very
\* same word. That is why the code checks the owner again AFTER the CAS:
\* once it counts as a reader, nobody can claim the slot, so the owner it
\* sees then is final.
\*
\* WHAT IS MODELLED, and the code each piece mirrors:
\*   phase, holders  the state word of each slot: Slot::state (holders is
\*                   the set of reading threads; the word holds its size)
\*   owner           Slot::owner, the table whose file the slot holds
\*   desc            Slot::file, the open file (a number per opening)
\*   alive, fileOf   the files open right now, and which table each is
\*
\* WHAT IS LEFT OUT, and why that loses nothing:
\*   - The CLOCK reference bit: it only chooses WHICH free slot a claim
\*     takes, never lets a claim take a slot with readers.
\*   - The DRAIN bit: it makes a starved thread wait for one slot's current
\*     readers instead of looking forever; like CLOCK it changes which claim
\*     happens and when, not whether a claim can take a slot with readers.
\*     The loom model a_starved_open_drains_a_busy_slot checks it.
\*   - Memory ordering: the loom models (tests/loom_tables.rs) check it.
\*   - Removing a table while it is read (renamed aside, unlinked by the
\*     last reader): it never closes a slot's file, so it adds no step here.
\*
\* CONFIGURATIONS (each GREEN must pass, each RED must break the one
\* invariant it names):
\*   MC_OpenFileTable_Green           one slot, two threads, two tables.
\*   MC_OpenFileTable_Green_TwoSlots  two slots, three threads.
\*   MC_OpenFileTable_Red_IgnoreReaders   a claim that takes a slot whatever
\*                                    its readers: NeverClosedInUse breaks.
\*   MC_OpenFileTable_Red_NoOwnerRecheck  a join that trusts the owner it
\*                                    saw before its CAS: ReadsOwnFile breaks.
\*   MC_OpenFileTable_Red_OutsideTable    a thread that finds no free slot
\*                                    opens its file outside the table:
\*                                    AtMostCap breaks.
\*
\* Lean, proofs/lean/Regolith/OpenFileTable.lean, proves the same three
\* rules for every number of slots, threads and steps.

\* We use numbers and finite sets.
EXTENDS Naturals, FiniteSets

\* The fixed inputs of a configuration.
CONSTANTS
  \* The threads that read.
  Threads,
  \* The tables (files) they read, named by numbers above 0.
  Files,
  \* How many slots the table has: max_open_files.
  Cap,
  \* [Threads -> Files]: the one table each thread reads.
  Want,
  \* How many times each thread reads its table.
  Reads,
  \* The most files that may ever be opened in one run (a bound for TLC).
  MaxDesc,
  \* "none" for the real code, or the name of one planted bug.
  Mutant

\* The slot numbers.
Slots == 1..Cap
\* The numbers a file opening can get.
Descs == 1..MaxDesc
\* "No file" in a slot, and "no owner".
None == 0

\* The limit is at least one slot.
ASSUME Cap \in Nat \ {0}
\* Every thread reads one table.
ASSUME Want \in [Threads -> Files]
\* Table names are positive, so None never names a table.
ASSUME \A f \in Files : f \in Nat \ {0}
\* The bug names this model knows.
ASSUME Mutant \in {"none", "IgnoreReaders", "NoOwnerRecheck", "OutsideTable"}

\* For the configurations: thread 1 reads table 1, thread 2 reads table 2.
WantTwo == [t \in {1, 2} |-> t]
\* For the configurations: threads 1 and 2 read table 1, thread 3 table 2.
WantThree == [t \in {1, 2, 3} |-> IF t = 3 THEN 2 ELSE 1]

\* The state that changes from step to step.
VARIABLES
  \* [Slots -> {"empty","claimed","open"}]: the phase bits of each slot's
  \* state word (Slot::state).
  phase,
  \* [Slots -> SUBSET Threads]: the threads counted as readers of each
  \* slot; the state word holds how many there are.
  holders,
  \* [Slots -> Files \cup {None}]: which table each slot's file is
  \* (Slot::owner).
  owner,
  \* [Slots -> Descs \cup {None}]: the open file in each slot (Slot::file).
  desc,
  \* The open files right now: every number here is a real open file.
  alive,
  \* [Descs -> Files \cup {None}]: which table each opening opened.
  fileOf,
  \* The next opening's number.
  next,
  \* [Threads -> step name]: where each thread is in its read.
  pc,
  \* [Threads -> Slots \cup {None}]: the slot a thread is joining or holds.
  at,
  \* [Threads -> [phase, count]]: the state word a thread looked at before
  \* its CAS.
  seen,
  \* [Threads -> Descs \cup {None}]: the open file a thread reads through.
  using,
  \* [Threads -> Files \cup {None}]: the table a thread's last read returned.
  got,
  \* [Threads -> Nat]: how many reads each thread still has to do.
  left

\* All the variables, for "nothing else changes".
vars == <<phase, holders, owner, desc, alive, fileOf, next, pc, at, seen,
          using, got, left>>

\* Every variable holds the kind of value it should.
TypeOK ==
  \* Each slot is in one of the three phases.
  /\ phase \in [Slots -> {"empty", "claimed", "open"}]
  \* Each slot's readers are some of the threads.
  /\ holders \in [Slots -> SUBSET Threads]
  \* Each slot's owner is a table or nobody.
  /\ owner \in [Slots -> Files \cup {None}]
  \* Each slot holds an opening or nothing.
  /\ desc \in [Slots -> Descs \cup {None}]
  \* The open files are openings.
  /\ alive \subseteq Descs
  \* Each opening opened a table, or has not happened yet.
  /\ fileOf \in [Descs -> Files \cup {None}]
  \* The next opening number is in range (one past the last at most).
  /\ next \in 1..(MaxDesc + 1)
  \* Each thread is at one of the steps of a read.
  /\ pc \in [Threads -> {"start", "cas", "recheck", "claim", "close",
                          "open", "read", "leave", "done"}]
  \* Each thread names a slot or none.
  /\ at \in [Threads -> Slots \cup {None}]
  \* Each thread reads through an opening or none.
  /\ using \in [Threads -> Descs \cup {None}]
  \* Each thread's last answer is a table or nothing yet.
  /\ got \in [Threads -> Files \cup {None}]
  \* Each thread has some reads left.
  /\ left \in [Threads -> 0..Reads]

\* The start: every slot empty, no file open, every thread about to read.
Init ==
  \* No slot holds anything.
  /\ phase = [s \in Slots |-> "empty"]
  \* Nobody reads any slot.
  /\ holders = [s \in Slots |-> {}]
  \* No slot has an owner.
  /\ owner = [s \in Slots |-> None]
  \* No slot has a file.
  /\ desc = [s \in Slots |-> None]
  \* No file is open.
  /\ alive = {}
  \* No opening has happened.
  /\ fileOf = [d \in Descs |-> None]
  \* The first opening will be number 1.
  /\ next = 1
  \* Every thread starts its first read.
  /\ pc = [t \in Threads |-> "start"]
  \* No thread is at a slot.
  /\ at = [t \in Threads |-> None]
  \* No thread has looked at a word yet.
  /\ seen = [t \in Threads |-> [phase |-> "empty", count |-> 0]]
  \* No thread reads through a file.
  /\ using = [t \in Threads |-> None]
  \* No thread has an answer.
  /\ got = [t \in Threads |-> None]
  \* Every thread has all its reads to do.
  /\ left = [t \in Threads |-> Reads]

\* A slot a claim may take: empty, or open with nobody reading it. The bug
\* IgnoreReaders also takes an open slot that has readers.
Claimable(s) ==
  \/ phase[s] = "empty"
  \/ /\ phase[s] = "open"
     /\ (holders[s] = {} \/ Mutant = "IgnoreReaders")

\* Thread t looks at slot s and finds its own table there, open: it
\* remembers the state word it saw and goes to join with a CAS
\* (SlotTable::join, the check before the CAS).
Look(t, s) ==
  \* The thread is starting a read and has reads left.
  /\ pc[t] = "start"
  /\ left[t] > 0
  \* The slot is open and holds the table this thread wants.
  /\ phase[s] = "open"
  /\ owner[s] = Want[t]
  \* It remembers the word: the phase and how many readers.
  /\ seen' = [seen EXCEPT ![t] = [phase |-> phase[s], count |-> Cardinality(holders[s])]]
  \* It remembers the slot.
  /\ at' = [at EXCEPT ![t] = s]
  \* Next it tries the CAS.
  /\ pc' = [pc EXCEPT ![t] = "cas"]
  \* Nothing else changes.
  /\ UNCHANGED <<phase, holders, owner, desc, alive, fileOf, next, using, got, left>>

\* Thread t decides to load its table into a slot: its file is not where it
\* looked, or it did not look (a stale hint). Duplicates are allowed: the
\* code allows two slots to hold one table.
Miss(t) ==
  \* The thread is starting a read and has reads left.
  /\ pc[t] = "start"
  /\ left[t] > 0
  \* It goes to claim a slot.
  /\ pc' = [pc EXCEPT ![t] = "claim"]
  \* Nothing else changes.
  /\ UNCHANGED <<phase, holders, owner, desc, alive, fileOf, next, at, seen, using, got, left>>

\* The join's CAS: it succeeds only if the slot's word is exactly the word
\* the thread saw, and then adds this thread as a reader. It compares the
\* word only, never the owner: that is the gap the recheck closes.
Cas(t) ==
  \* The thread is at its CAS, on its slot s.
  /\ pc[t] = "cas"
  /\ LET s == at[t] IN
       \* The word now equals the word it saw ...
       IF /\ phase[s] = seen[t].phase
          /\ Cardinality(holders[s]) = seen[t].count
       \* ... so the CAS wins: the thread counts as a reader, then rechecks.
       THEN /\ holders' = [holders EXCEPT ![s] = holders[s] \cup {t}]
            /\ pc' = [pc EXCEPT ![t] = "recheck"]
            /\ UNCHANGED at
       \* ... otherwise the CAS fails and the thread starts over.
       ELSE /\ pc' = [pc EXCEPT ![t] = "start"]
            /\ at' = [at EXCEPT ![t] = None]
            /\ UNCHANGED holders
  \* Nothing else changes.
  /\ UNCHANGED <<phase, owner, desc, alive, fileOf, next, seen, using, got, left>>

\* After the CAS the thread checks the owner again. Counted as a reader, the
\* slot cannot be claimed under it, so this answer is final. The bug
\* NoOwnerRecheck skips this check.
Recheck(t) ==
  \* The thread won its CAS on slot s.
  /\ pc[t] = "recheck"
  /\ LET s == at[t] IN
       \* The slot still holds its table (or the bug does not look) ...
       IF owner[s] = Want[t] \/ Mutant = "NoOwnerRecheck"
       \* ... so it reads through the slot's open file.
       THEN /\ using' = [using EXCEPT ![t] = desc[s]]
            /\ pc' = [pc EXCEPT ![t] = "read"]
            /\ UNCHANGED <<holders, at>>
       \* ... otherwise the slot was reloaded with another table: it stops
       \* counting as a reader and starts over.
       ELSE /\ holders' = [holders EXCEPT ![s] = holders[s] \ {t}]
            /\ at' = [at EXCEPT ![t] = None]
            /\ pc' = [pc EXCEPT ![t] = "start"]
            /\ UNCHANGED using
  \* Nothing else changes.
  /\ UNCHANGED <<phase, owner, desc, alive, fileOf, next, seen, got, left>>

\* Thread t claims slot s with one CAS: from empty, or from open with no
\* reader (SlotTable::try_claim). Claimed, the slot is this thread's alone.
Claim(t, s) ==
  \* The thread wants a slot.
  /\ pc[t] = "claim"
  \* This slot may be taken.
  /\ Claimable(s)
  \* The CAS moves it to "claimed".
  /\ phase' = [phase EXCEPT ![s] = "claimed"]
  \* The thread remembers it.
  /\ at' = [at EXCEPT ![t] = s]
  \* Next it closes the old file.
  /\ pc' = [pc EXCEPT ![t] = "close"]
  \* Nothing else changes.
  /\ UNCHANGED <<holders, owner, desc, alive, fileOf, next, seen, using, got, left>>

\* The bug OutsideTable: a thread that finds no slot to claim opens its file
\* anyway, outside the table, instead of waiting for a slot.
ClaimOutside(t) ==
  \* Only with the bug.
  /\ Mutant = "OutsideTable"
  \* The thread wants a slot ...
  /\ pc[t] = "claim"
  \* ... and none may be taken.
  /\ \A s \in Slots : ~Claimable(s)
  \* There is an opening number left.
  /\ next <= MaxDesc
  \* It opens its table: one more open file.
  /\ alive' = alive \cup {next}
  \* That opening is its table.
  /\ fileOf' = [fileOf EXCEPT ![next] = Want[t]]
  \* The next opening gets the next number.
  /\ next' = next + 1
  \* It reads through it, at no slot.
  /\ using' = [using EXCEPT ![t] = next]
  /\ at' = [at EXCEPT ![t] = None]
  /\ pc' = [pc EXCEPT ![t] = "read"]
  \* Nothing else changes.
  /\ UNCHANGED <<phase, holders, owner, desc, seen, got, left>>

\* The claimer closes the file its slot held, before opening its own: the
\* table never holds more than one file per slot, even for an instant.
Close(t) ==
  \* The thread claimed slot s.
  /\ pc[t] = "close"
  /\ LET s == at[t] IN
       \* The old file is closed (if there was one).
       /\ alive' = alive \ {desc[s]}
       \* The slot holds no file.
       /\ desc' = [desc EXCEPT ![s] = None]
  \* Next it opens its own.
  /\ pc' = [pc EXCEPT ![t] = "open"]
  \* Nothing else changes.
  /\ UNCHANGED <<phase, holders, owner, fileOf, next, at, seen, using, got, left>>

\* The claimer opens its table in the slot and publishes it open, counting
\* itself as the one reader (SlotTable::load).
Open(t) ==
  \* The thread closed the old file of slot s.
  /\ pc[t] = "open"
  \* There is an opening number left.
  /\ next <= MaxDesc
  /\ LET s == at[t] IN
       \* Its table is now open ...
       /\ alive' = alive \cup {next}
       \* ... as this opening ...
       /\ fileOf' = [fileOf EXCEPT ![next] = Want[t]]
       \* ... held in the slot ...
       /\ desc' = [desc EXCEPT ![s] = next]
       \* ... whose owner is now this table ...
       /\ owner' = [owner EXCEPT ![s] = Want[t]]
       \* ... and which is open, with this thread as a reader.
       /\ phase' = [phase EXCEPT ![s] = "open"]
       /\ holders' = [holders EXCEPT ![s] = holders[s] \cup {t}]
  \* The thread reads through the new opening.
  /\ using' = [using EXCEPT ![t] = next]
  \* The next opening gets the next number.
  /\ next' = next + 1
  \* Next it reads.
  /\ pc' = [pc EXCEPT ![t] = "read"]
  \* Nothing else changes.
  /\ UNCHANGED <<at, seen, got, left>>

\* The thread reads through its open file: it gets that file's table.
Read(t) ==
  \* The thread is ready to read.
  /\ pc[t] = "read"
  \* It gets the table its open file is (nothing, if it holds no file).
  /\ got' = [got EXCEPT ![t] = IF using[t] \in Descs THEN fileOf[using[t]] ELSE None]
  \* Next it leaves.
  /\ pc' = [pc EXCEPT ![t] = "leave"]
  \* Nothing else changes.
  /\ UNCHANGED <<phase, holders, owner, desc, alive, fileOf, next, at, seen, using, left>>

\* The thread stops counting as a reader (Held::drop): one decrement. A file
\* the bug opened outside the table is closed here.
Leave(t) ==
  \* The thread has read.
  /\ pc[t] = "leave"
  \* If it read through a slot, it leaves the slot's readers ...
  /\ IF at[t] # None
     THEN /\ holders' = [holders EXCEPT ![at[t]] = holders[at[t]] \ {t}]
          /\ UNCHANGED alive
     \* ... otherwise it closes its outside file.
     ELSE /\ alive' = alive \ {using[t]}
          /\ UNCHANGED holders
  \* One read fewer to do.
  /\ left' = [left EXCEPT ![t] = left[t] - 1]
  \* It is no longer at a slot or reading.
  /\ at' = [at EXCEPT ![t] = None]
  /\ using' = [using EXCEPT ![t] = None]
  \* It starts its next read, or is done.
  /\ pc' = [pc EXCEPT ![t] = IF left[t] = 1 THEN "done" ELSE "start"]
  \* Nothing else changes.
  /\ UNCHANGED <<phase, owner, desc, fileOf, next, seen, got>>

\* Every step any thread can take.
Next ==
  \* Some thread takes one of its steps.
  \E t \in Threads :
    \/ \E s \in Slots : Look(t, s)
    \/ Miss(t)
    \/ Cas(t)
    \/ Recheck(t)
    \/ \E s \in Slots : Claim(t, s)
    \/ ClaimOutside(t)
    \/ Close(t)
    \/ Open(t)
    \/ Read(t)
    \/ Leave(t)

\* The behaviours: start in Init, take Next steps.
Spec == Init /\ [][Next]_vars

\* ===========================================================================
\* THE RULES
\* ===========================================================================

\* Never more open files than slots. Rules out: every slot busy, and a
\* thread opening its table anyway, so the process holds one file more than
\* max_open_files allows. The code keeps every open file in a slot.
AtMostCap == Cardinality(alive) <= Cap

\* A file a thread is reading through is still open. Rules out: thread 1
\* mid-read on table A's file, thread 2 claims the slot and closes it, and
\* thread 1's read fails or reads a closed file. The code's claim CAS only
\* wins with no readers counted.
NeverClosedInUse ==
  \* For every thread that is reading or about to leave, its file is open.
  \A t \in Threads : pc[t] \in {"read", "leave"} => using[t] \in alive

\* A read returns the table its thread asked for. Rules out: a thread sees
\* A in the slot, the slot is reloaded with B, read and left with the same
\* state word, and the thread's CAS joins B. The recheck after the CAS
\* catches it.
ReadsOwnFile ==
  \* For every thread that has read, what it got is the table it wanted.
  \A t \in Threads : pc[t] = "leave" => got[t] = Want[t]

====
