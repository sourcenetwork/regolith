---- MODULE GroupCommit ----
\* THE STORY.
\* Many threads commit at once. Making each commit durable on its own costs one
\* fsync each, and an fsync is slow, so regolith lets the commits that arrive
\* together share one: a "commit group". One thread, the leader, takes the
\* waiting commits, writes all their records to the log with one write, syncs
\* the log once, puts their writes into the memtable, and only then makes the
\* whole group visible to readers.
\*
\* What can go wrong. Two transactions both read key 1 at value 5 and both
\* write 6. If they commit one after the other, the second sees that key 1
\* changed under it and aborts: that is the whole point of validation. In a
\* group, though, the first one's write is not in the memtable yet when the
\* second is checked (nothing is applied before the log write). A leader that
\* checks the second only against the memtable sees no change, lets both
\* commit, and an increment is lost. The fix: check each member against the
\* memtable PLUS the writes of the members accepted before it in the same
\* group. This model shows that with the fix every group decides exactly what
\* committing its members one at a time would decide, and that a leader that
\* forgets the earlier members (RED ViewOnly) loses the update.
\*
\* The check is split in two (validation outside the mutex): a transaction
\* first checks itself, on its own thread, against everything up to a
\* horizon h it samples, and the leader then checks only what landed above
\* h. A leader that trusted the early check and skipped the part above h
\* (RED TrustEarly) would miss a write that landed between the two.
\*
\* A commit made by `commit_nowait` must not wait for the fsync either, so
\* a group that needs one and holds such a member is only written by its
\* leader and left OWED: its fsync becomes a job that the first of its
\* members to poll its own queue claims with one compare-and-swap and runs
\* (sync, apply, publish, answer everyone). A blocking member, or the next
\* writer to take the pipeline, claims it the same way. Tiny example:
\* commits 1 and 3 share a group and both were made by commit_nowait. The
\* leader writes the group and returns; 3's poll claims the job and runs the
\* fsync; 1's poll finds it claimed and leaves it. The fsync runs once
\* (RED DoubleClaim shows a claim that is not one CAS running it twice), and
\* nothing in the group is visible before it (DurableBeforeVisible again).
\*
\* Three more promises are checked. A commit made durable by an fsync is
\* visible only after that fsync (RED PublishBeforeSync shows a reader seeing
\* a commit a power cut would erase). A leader commits one group and then
\* hands the pipeline to the next waiting writer, so no caller does the work
\* of an unbounded queue of others (RED DrainAll shows a leader that keeps
\* going). And every commit gets exactly one answer, even when the log write
\* or the fsync fails.
\*
\* PROVED FOR EVERY SIZE in Lean (proofs/lean/Regolith/GroupCommit.lean):
\*   group_eq_serial          checking each member against the view plus the
\*                            keys of earlier accepted members (plain writes
\*                            among them) decides as committing them one at
\*                            a time (SerialEquivalent here)
\*   early_check_split        checking up to a horizon h outside the mutex
\*                            and above h under it decides as one check
\*   early_check_cover        the same when the early check also looks past
\*                            h, at versions applied but not yet visible,
\*                            which is what the code does (Submit here)
\*   early_conflict_final     a conflict the early check finds stays one as
\*                            versions land, so it may abort at once
\*   view_only_breaks_serial  RED ViewOnly as a concrete counterexample
\*   plain_write_counts_in_group
\*                            a plain write ahead of a transaction in the
\*                            group aborts it, as it would one at a time
\* Tickets, durability before visibility and bounded turns are properties of
\* interleavings, so TLC checks them here for a few transactions.
\*
\* THE CODE THIS MODEL MIRRORS (src/engine/commit/).
\*   Transaction::begin                 Begin: the snapshot is the visible
\*                                      sequence.
\*   RegolithEngine::check_early        Submit: sample h, check up to it
\*     (early.rs)                       outside the mutex, abort at once on
\*                                      a conflict, else queue.
\*   commit_through_pipeline, lead_with LeadWith: the writer that finds the
\*     (mod.rs)                         pipeline free leads a group headed by
\*                                      its own commit.
\*   commit_ring.push, the wait loop    Push and Drain: a writer that finds it
\*                                      busy queues, and leads a group of the
\*                                      queue when it is handed the pipeline
\*                                      or finds it free.
\*   admit_from_ring                    the group: the held ticket first, then
\*                                      the ring in order, at most MaxGroup
\*                                      members (MAX_GROUP_MEMBERS).
\*   decide, validate (group.rs,        Decide: each member in group order,
\*     txn.rs)                          against the view above h plus the
\*                                      overlay of earlier members' writes.
\*   log_group, sync_group              Write and Sync: one append, one fsync.
\*   run_group                          Apply and Publish, after the fsync.
\*   run_and_complete                   Complete, or Fail for G2.
\*   defer_group, GroupSync (deferred.rs) Defer: a group with a nowait member
\*                                      that needs an fsync is left owed.
\*   Job::claim, land_pending,          ClaimOwed: a member's poll, a
\*     land_here                        blocking member or the next pipeline
\*                                      holder claims the owed group with
\*                                      one CAS; OwedSync is its fsync.
\*   hand_off (E21)                     HandOff: pop the ring's head into
\*                                      `held`, wake its writer, release.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - A batch takes one sequence per operation; here a commit takes one.
\*     Every operation of a commit sorts above every earlier commit and below
\*     every later one, which is all validation and publication read.
\*   - Identical-write elision, merges, value reads and exempt keys refine
\*     the per-key test (RepeatableRead.tla). The code runs them against a
\*     view that holds the earlier members' writes at their real sequences,
\*     so each refined test sees what it would see one at a time; the group
\*     protocol around the test is this one.
\*   - Bytes: a group is bounded by MAX_GROUP_BYTES too. Bounding by members
\*     here covers the same protocol.
\*   - Ingest, which takes a sequence under the same mutex, is
\*     IngestPublication.tla.
\*
\* CONFIGURATIONS.
\*   MC_GroupCommit_Green                  Mutant = "none": every invariant
\*                                         and AllTicketsComplete hold.
\*   MC_GroupCommit_Red_ViewOnly           SerialEquivalent fails.
\*   MC_GroupCommit_Red_PublishBeforeSync  DurableBeforeVisible fails.
\*   MC_GroupCommit_Red_DrainAll           BoundedTurn fails.
\*   MC_GroupCommit_Red_TrustEarly         SerialEquivalent fails.
\*   MC_GroupCommit_Green_ReadOnly         a transaction that only reads
\*                                         shares groups; every invariant
\*                                         and AllTicketsComplete hold.
\*   MC_GroupCommit_Green_Nowait           two of the commits are made by
\*                                         commit_nowait: their groups are
\*                                         left owed and claimed; every
\*                                         invariant and AllTicketsComplete
\*                                         hold.
\*   MC_GroupCommit_Green_Nowait_Owes      the witness: the same setup must
\*                                         break NothingOwed, so the GREEN
\*                                         run did go through owed groups.
\*   MC_GroupCommit_Red_DoubleClaim        a claim that also succeeds on a
\*                                         claimed group: SingleSync fails.

\* We use numbers, sequences (lists) and set sizes.
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  \* The commits, each a number. Each commits once.
  Txns,
  \* Which of them are plain writes (Db::put and Db::write): no snapshot, no
  \* validation, they always land. The rest are optimistic transactions.
  Plain,
  \* The keys, each a number.
  Keys,
  \* Reads[t]: the keys transaction t read and asked to have validated.
  Reads,
  \* Writes[t]: the keys t writes. Empty for a transaction that only read.
  Writes,
  \* The commits made at Immediate durability: they wait for an fsync.
  Immediate,
  \* The most members one group admits (MAX_GROUP_MEMBERS in the code).
  MaxGroup,
  \* TRUE: a group's log write or fsync may fail (the G2 path).
  Faults,
  \* The commits made by commit_nowait: they never wait for an fsync, so a
  \* group holding one leaves its fsync owed, as a job someone claims.
  Nowait,
  \* Which bug to plant: "none", "ViewOnly", "PublishBeforeSync",
  \* "DrainAll", "TrustEarly" or "DoubleClaim".
  Mutant

\* Commits and keys are plain numbers.
ASSUME Txns \subseteq Nat /\ Keys \subseteq Nat
\* Plain writes are some of the commits.
ASSUME Plain \subseteq Txns
\* Every commit names the keys it read and wrote.
ASSUME Reads \in [Txns -> SUBSET Keys] /\ Writes \in [Txns -> SUBSET Keys]
\* A plain write reads nothing and writes something (an empty batch never
\* reaches the pipeline).
ASSUME \A t \in Plain : Reads[t] = {} /\ Writes[t] # {}
\* Some commits wait for an fsync.
ASSUME Immediate \subseteq Txns
\* A group holds at least one member.
ASSUME MaxGroup \in Nat \ {0}
\* Failures are on or off.
ASSUME Faults \in BOOLEAN
\* The nowait commits are some of the commits.
ASSUME Nowait \subseteq Txns
\* The bug to plant is one we know.
ASSUME Mutant \in {"none", "ViewOnly", "PublishBeforeSync", "DrainAll", "TrustEarly",
                   "DoubleClaim"}

VARIABLES
  \* pc[t]: where commit t is. "idle" (not begun), "begun" (a transaction
  \* exists), "ready" (passed its early check, about to queue or lead),
  \* "queued" (its ticket waits in the ring or as `held`), "grouped" (in the
  \* group being committed), "done" (its caller has its answer).
  pc,
  \* snap[t]: the visible sequence transaction t began at
  \* (Transaction::snapshot_seq).
  snap,
  \* hor[t]: the horizon h its early check sampled (Early::horizon).
  hor,
  \* queue: the commit ring (commit_ring, an ArrayQueue), oldest first.
  queue,
  \* held: the ticket a leader took out of the ring to head the next group,
  \* 0 for none (Pipeline::held).
  held,
  \* leader: the commit whose thread holds the pipeline mutex, 0 for none.
  leader,
  \* turnGroups: how many groups the current leader committed in this hold
  \* of the mutex.
  turnGroups,
  \* group: the members of the group being committed, in group order
  \* (Pipeline::group).
  group,
  \* gi: the position in `group` of the next member to decide.
  gi,
  \* gview: the visible sequence when the leader took the group: the view it
  \* checks against.
  gview,
  \* gacc: the keys written by members accepted so far in this group (the
  \* overlay memtable in group.rs).
  gacc,
  \* gwal: where the log ended before this group, for the rollback on G2.
  gwal,
  \* stage: the leader's step. "idle", "deciding", "written", "applied",
  \* "published", or "handoff" (answers given, mutex not yet released).
  stage,
  \* synced: this group's fsync has run.
  synced,
  \* dec[t]: the verdict, "none", "accept" or "conflict".
  dec,
  \* seq[t]: the sequence an accepted member that writes took, 0 otherwise.
  seq,
  \* pos[t]: when the verdict was given, counting verdicts from 1; 0 before.
  pos,
  \* npos: how many verdicts have been given.
  npos,
  \* outcome[t]: what t's caller is told: "none", "commit", "conflict" or
  \* "failed".
  outcome,
  \* completions[t]: how many times t's caller was told (must end at 1).
  completions,
  \* lastSeq: the last sequence handed out (latest_seq).
  lastSeq,
  \* walEnd: the last sequence whose record is in the log.
  walEnd,
  \* durable: the last sequence an fsync made durable.
  durable,
  \* store: the versions <<key, sequence>> in the memtable.
  store,
  \* visible: the newest sequence a new snapshot sees (visible_seq).
  visible,
  \* owed: the group is written and its leader let go of the pipeline
  \* without syncing it; its fsync waits as a job (Pipeline::pending).
  owed,
  \* claimers: the commits whose threads claimed the owed group's job. One
  \* CAS lets exactly one in; the DoubleClaim bug lets a second in.
  claimers,
  \* syncedBy: the claimers that have run the owed group's fsync.
  syncedBy,
  \* syncRuns: how many times this group's fsync ran (a ghost, for
  \* SingleSync).
  syncRuns

\* Every variable, so that a step that changes none of them is a stutter.
vars == <<pc, snap, hor, queue, held, leader, turnGroups, group, gi, gview,   \* all of them,
          gacc, gwal, stage, synced, dec, seq, pos, npos, outcome,              \* listed once
          completions, lastSeq, walEnd, durable, store, visible,
          owed, claimers, syncedBy, syncRuns>>

\* The owed group's bookkeeping, so a step that leaves it alone says so once.
landing == <<owed, claimers, syncedBy, syncRuns>>

----------------------------------------------------------------------------
\* Helpers.

\* The smaller of two numbers.
Min2(a, b) == IF a <= b THEN a ELSE b

\* The keys whose newer versions abort t: the ones it read and the ones it
\* writes.
Touched(t) == Reads[t] \cup Writes[t]

\* The memtable holds a version of a key t touched with a sequence in
\* (lo, hi]: a write t's snapshot did not see, inside the window checked.
NewerIn(t, lo, hi) == \E v \in store : lo < v[2] /\ v[2] <= hi /\ v[1] \in Touched(t)

\* The memtable holds a version of a key t touched above lo, however new:
\* what the early check finds in the view it loads, which holds every applied
\* version, even one of a group that is not visible yet.
NewerAbove(t, lo) == \E v \in store : lo < v[2] /\ v[1] \in Touched(t)

\* The members of the group being committed, as a set.
Members == {group[i] : i \in 1..Len(group)}

\* The members accepted so far.
Accepted == {m \in Members : dec[m] = "accept"}

\* The accepted members that write something: only they take a sequence and
\* a log record.
Writers == {m \in Accepted : Writes[m] # {}}

\* The group needs its fsync: an accepted member that writes asked for
\* Immediate. A member that only read is no record and forces no sync.
NeedsSync == Writers \cap Immediate # {}

\* The group's fsync is left owed: it needs one, and some member (a writer
\* or not) was made by commit_nowait, which must not wait for it.
Deferred == NeedsSync /\ Members \cap Nowait # {}

\* The versions t writes, all at t's sequence.
VersionsOf(t) == {<<k, seq[t]>> : k \in Writes[t]}

\* t was accepted and its group did not fail: it committed, or is committing.
Lands(t) == dec[t] = "accept" /\ outcome[t] # "failed"

\* How many tickets wait to be admitted: the held one and the ring.
Waiting == (IF held # 0 THEN 1 ELSE 0) + Len(queue)

\* The first n waiting tickets in admission order: the held one, then the
\* ring from its head.
Take(n) == SubSeq((IF held # 0 THEN <<held>> ELSE <<>>) \o queue, 1, n)

\* What is left waiting after the first n are taken. The held ticket goes
\* first, so the ring loses n, or n - 1 when a ticket was held.
LeftQueue(n) == SubSeq(queue, (IF held # 0 THEN n ELSE n + 1), Len(queue))

----------------------------------------------------------------------------
\* Actions.

\* The start: nothing begun, queued, decided or written; the mutex is free.
Init ==
  \* Every commit is idle.
  /\ pc          = [t \in Txns |-> "idle"]
  \* No snapshot taken yet.
  /\ snap        = [t \in Txns |-> 0]
  \* No horizon sampled yet.
  /\ hor         = [t \in Txns |-> 0]
  \* The ring is empty.
  /\ queue       = <<>>
  \* No ticket is held.
  /\ held        = 0
  \* Nobody leads.
  /\ leader      = 0
  \* No group in this turn.
  /\ turnGroups  = 0
  \* No group is being committed.
  /\ group       = <<>>
  \* The decide cursor is at the start.
  /\ gi          = 1
  \* No view taken.
  /\ gview       = 0
  \* No member accepted, so no key in the overlay.
  /\ gacc        = {}
  \* The log is empty.
  /\ gwal        = 0
  \* The leader is idle.
  /\ stage       = "idle"
  \* No fsync yet.
  /\ synced      = FALSE
  \* No verdicts.
  /\ dec         = [t \in Txns |-> "none"]
  \* No sequences.
  /\ seq         = [t \in Txns |-> 0]
  \* No verdict positions.
  /\ pos         = [t \in Txns |-> 0]
  \* No verdicts counted.
  /\ npos        = 0
  \* Nobody has an answer.
  /\ outcome     = [t \in Txns |-> "none"]
  \* Nobody was told anything.
  /\ completions = [t \in Txns |-> 0]
  \* No sequence handed out.
  /\ lastSeq     = 0
  \* Nothing in the log.
  /\ walEnd      = 0
  \* Nothing durable.
  /\ durable     = 0
  \* An empty memtable.
  /\ store       = {}
  \* Nothing visible.
  /\ visible     = 0
  \* No group is owed.
  /\ owed        = FALSE
  \* Nobody claimed anything.
  /\ claimers    = {}
  \* Nobody ran an owed fsync.
  /\ syncedBy    = {}
  \* No fsync ran.
  /\ syncRuns    = 0

\* Transaction t begins (Transaction::begin): its snapshot is what is visible
\* now, and every read it makes is answered as of that moment.
Begin(t) ==
  \* Only an optimistic transaction has a snapshot.
  /\ t \notin Plain
  \* It has not begun yet.
  /\ pc[t] = "idle"
  \* Now it has.
  /\ pc'   = [pc EXCEPT ![t] = "begun"]
  \* Its snapshot is the visible sequence.
  /\ snap' = [snap EXCEPT ![t] = visible]
  \* Nothing else changes.
  /\ UNCHANGED <<hor, queue, held, leader, turnGroups, group, gi, gview, gacc,
                 gwal, stage, synced, dec, seq, pos, npos, outcome,
                 completions, lastSeq, walEnd, durable, store, visible>>
  \* The owed group is untouched.
  /\ UNCHANGED landing

\* Transaction t commits and runs its early check on its own thread, outside
\* the mutex (check_early). It samples h, the visible sequence, first. If
\* nothing was made visible since its snapshot (h = snap) it reads nothing.
\* Otherwise it loads the view, which holds every applied version, and a
\* newer version of a key it touched aborts it at once: with this plain test
\* every conflict is final, because a newer version never goes away. That
\* commit is decided now, before any group, and never queues.
Submit(t) ==
  \* The sampled horizon.
  LET h == visible
      \* The early check finds a conflict.
      lost == h > snap[t] /\ NewerAbove(t, snap[t])
  \* Only a begun transaction commits.
  IN /\ pc[t] = "begun"
     \* It remembers the horizon it checked up to.
     /\ hor' = [hor EXCEPT ![t] = h]
     /\ IF lost
          THEN \* Decided now, before any group:
               /\ pc'          = [pc EXCEPT ![t] = "done"]             \* its caller has the answer,
               /\ dec'         = [dec EXCEPT ![t] = "conflict"]        \* the verdict is a conflict,
               /\ outcome'     = [outcome EXCEPT ![t] = "conflict"]    \* which the caller is told,
               /\ completions' = [completions EXCEPT ![t] = @ + 1]     \* exactly once,
               /\ pos'         = [pos EXCEPT ![t] = npos + 1]          \* and the verdict takes the
               /\ npos'        = npos + 1                              \* next place in decision order.
          ELSE \* Clean up to here:
               /\ pc' = [pc EXCEPT ![t] = "ready"]                     \* ready to lead or to queue,
               /\ UNCHANGED <<dec, outcome, completions, pos, npos>>    \* with no verdict yet.
     \* Nothing else changes.
     /\ UNCHANGED <<snap, queue, held, leader, turnGroups, group, gi, gview,
                    gacc, gwal, stage, synced, seq, lastSeq, walEnd, durable,
                    store, visible>>
     \* The owed group is untouched.
     /\ UNCHANGED landing

\* A plain write is handed to the pipeline: no snapshot, no check.
PlainSubmit(t) ==
  \* Only a plain write.
  /\ t \in Plain
  \* It was not handed over yet.
  /\ pc[t] = "idle"
  \* It is ready to lead or queue.
  /\ pc' = [pc EXCEPT ![t] = "ready"]
  \* Nothing else changes.
  /\ UNCHANGED <<snap, hor, queue, held, leader, turnGroups, group, gi, gview,
                 gacc, gwal, stage, synced, dec, seq, pos, npos, outcome,
                 completions, lastSeq, walEnd, durable, store, visible>>
  \* The owed group is untouched.
  /\ UNCHANGED landing

\* The group a new leader takes: `members` in order. It records the view it
\* checks against, starts the decide cursor and an empty overlay, and marks
\* where the log ends, for the rollback.
StartGroup(members) ==
  /\ group'  = members           \* the members, in the order they will be decided
  /\ gi'     = 1                 \* the first member is decided first
  /\ gview'  = visible           \* the view: everything visible now
  /\ gacc'   = {}                \* nobody accepted yet, so the overlay is empty
  /\ gwal'   = walEnd            \* where the log ends, to cut back to on failure
  /\ stage'  = "deciding"        \* the leader starts deciding
  /\ synced' = FALSE             \* this group has not synced
  /\ syncRuns' = 0               \* and its fsync has run no times
  \* No group is owed when one starts (the guards make sure), so the rest
  \* of the owed bookkeeping stays empty.
  /\ UNCHANGED <<owed, claimers, syncedBy>>

\* The writer of t finds the pipeline free (try_lock succeeds) and leads a
\* group headed by its own commit, then up to MaxGroup - 1 waiting tickets,
\* the held one first (lead_with, admit_from_ring).
LeadWith(t, k) ==
  \* t is about to commit and the mutex is free.
  /\ pc[t] = "ready"            \* its commit is about to go in
  /\ leader = 0                 \* and nobody holds the mutex
  /\ ~owed                      \* and no group waits to be landed first
  \* It takes k - 1 others, as many as wait, at most the cap allows.
  /\ k \in 1..Min2(MaxGroup, 1 + Waiting)
  \* The group: its own commit, then the first waiting ones.
  /\ StartGroup(<<t>> \o Take(k - 1))
  \* Those taken leave the ring, and a held one is taken first.
  /\ queue' = IF k = 1 THEN queue ELSE LeftQueue(k - 1)       \* the ring loses the ones taken
  /\ held'  = IF k = 1 THEN held ELSE 0                       \* a held ticket is taken first
  \* Every member is now in the group.
  /\ pc'    = [u \in Txns |-> IF u = t \/ \E i \in 1..(k - 1) : Take(k - 1)[i] = u
                                THEN "grouped" ELSE pc[u]]   \* everybody else stays where they were
  \* t holds the mutex, for its first group of this turn.
  /\ leader'     = t           \* t's thread is the leader
  /\ turnGroups' = 1           \* this is the first group of its turn
  \* Nothing else changes.
  /\ UNCHANGED <<snap, hor, dec, seq, pos, npos, outcome, completions,
                 lastSeq, walEnd, durable, store, visible>>

\* The writer of t finds the pipeline busy and queues its ticket at the tail
\* of the ring (commit_ring.push), then waits.
Push(t) ==
  \* It passed its check (or is a plain write) and has not queued.
  /\ pc[t] = "ready"
  \* Its ticket goes to the tail.
  /\ queue' = Append(queue, t)
  \* It now waits.
  /\ pc'    = [pc EXCEPT ![t] = "queued"]
  \* Nothing else changes.
  /\ UNCHANGED <<snap, hor, held, leader, turnGroups, group, gi, gview, gacc,
                 gwal, stage, synced, dec, seq, pos, npos, outcome,
                 completions, lastSeq, walEnd, durable, store, visible>>
  \* The owed group is untouched.
  /\ UNCHANGED landing

\* A waiting writer finds the pipeline free (its try_drain, after a hand-off
\* woke it or its park timed out) and leads a group of the first k waiting
\* tickets, the held one first. Its own ticket may or may not be among them.
Drain(t, k) ==
  \* t's ticket waits and the mutex is free.
  /\ pc[t] = "queued"           \* t's writer is waiting
  /\ leader = 0                 \* and nobody holds the mutex
  /\ ~owed                      \* and no group waits to be landed first
  \* Something waits, and it takes as many as it may.
  /\ k \in 1..Min2(MaxGroup, Waiting)
  \* The group: the first k waiting tickets.
  /\ StartGroup(Take(k))
  \* They leave the ring and the held slot.
  /\ queue' = LeftQueue(k)      \* the ring loses the ones taken
  /\ held'  = 0                 \* the held ticket, if any, went first
  \* Every member is now in the group.
  /\ pc'    = [u \in Txns |-> IF \E i \in 1..k : Take(k)[i] = u THEN "grouped" ELSE pc[u]]
  \* t holds the mutex, for its first group of this turn.
  /\ leader'     = t           \* t's thread is the leader
  /\ turnGroups' = 1           \* this is the first group of its turn
  \* Nothing else changes.
  /\ UNCHANGED <<snap, hor, dec, seq, pos, npos, outcome, completions,
                 lastSeq, walEnd, durable, store, visible>>

\* The leader decides the next member m, in group order (decide).
\* - A plain write is not checked: it is accepted.
\* - A transaction conflicts if a version of a key it touched landed above
\*   its horizon h in the view (the check under the mutex looks only above
\*   h), or if a member accepted earlier in this group writes such a key (the
\*   overlay). Mutant ViewOnly forgets the second test; mutant TrustEarly
\*   forgets the first, trusting the early check alone.
\* An accepted member that writes takes the next sequence now, so sequences
\* follow decision order; a member that only read takes none, nor does a
\* conflicting one.
Decide ==
  \* The member being decided.
  LET m        == group[gi]
      \* It conflicts with an earlier member of the group.
      inGroup  == Mutant # "ViewOnly" /\ Touched(m) \cap gacc # {}
      \* A version above its horizon, which the early check never saw.
      above    == Mutant # "TrustEarly" /\ NewerIn(m, hor[m], gview)
      \* It conflicts at all.
      conflict == m \notin Plain /\ (above \/ inGroup)
      \* It takes a sequence.
      takes    == ~conflict /\ Writes[m] # {}
  \* The leader is deciding and a member is left.
  IN /\ stage = "deciding"      \* the leader is deciding
     /\ gi <= Len(group)        \* and a member is left to decide
     \* The verdict.
     /\ dec'     = [dec EXCEPT ![m] = IF conflict THEN "conflict" ELSE "accept"]
     \* The next sequence for an accepted writer.
     /\ seq'     = IF takes THEN [seq EXCEPT ![m] = lastSeq + 1] ELSE seq   \* m's sequence
     /\ lastSeq' = IF takes THEN lastSeq + 1 ELSE lastSeq                 \* one more handed out
     \* Its writes join the overlay the later members are checked against.
     /\ gacc'    = IF conflict THEN gacc ELSE gacc \cup Writes[m]
     \* Its place in decision order.
     /\ pos'     = [pos EXCEPT ![m] = npos + 1]    \* m's verdict is the next one given
     /\ npos'    = npos + 1                        \* and is counted
     \* On to the next member.
     /\ gi'      = gi + 1
     \* Nothing else changes.
     /\ UNCHANGED <<pc, snap, hor, queue, held, leader, turnGroups, group,
                    gview, gwal, stage, synced, outcome, completions, walEnd,
                    durable, store, visible>>
     \* The owed group is untouched.
     /\ UNCHANGED landing

\* Every member is decided: the writers' records go to the log in one append
\* (log_group). A group with no writer writes nothing.
Write ==
  \* All members decided.
  /\ stage = "deciding"          \* the leader was deciding
  /\ gi > Len(group)             \* and no member is left
  \* The log now ends at the group's last sequence.
  /\ walEnd' = IF Writers = {} THEN walEnd ELSE lastSeq
  \* The leader moves on.
  /\ stage'  = "written"
  \* Nothing else changes.
  /\ UNCHANGED <<pc, snap, hor, queue, held, leader, turnGroups, group, gi,
                 gview, gacc, gwal, synced, dec, seq, pos, npos, outcome,
                 completions, lastSeq, durable, store, visible>>
  \* The owed group is untouched.
  /\ UNCHANGED landing

\* The group's one fsync (sync_group), when a writer asked for Immediate. It
\* makes every record written so far durable. This is the leader's own sync,
\* for a group it did not leave owed.
Sync ==
  \* After the append, once.
  /\ stage \in {"written", "applied", "published"}   \* the records are in the log
  /\ ~synced                                         \* and not synced yet
  /\ NeedsSync                                       \* and somebody waits for it
  /\ ~Deferred                                       \* and the leader keeps the group
  \* Everything in the log is durable now.
  /\ durable' = walEnd           \* durable up to the end of the log
  /\ synced'  = TRUE             \* and this group's sync is done
  /\ syncRuns' = syncRuns + 1    \* the fsync ran one more time
  \* Nothing else changes.
  /\ UNCHANGED <<pc, snap, hor, queue, held, leader, turnGroups, group, gi,
                 gview, gacc, gwal, stage, dec, seq, pos, npos, outcome,
                 completions, lastSeq, walEnd, store, visible>>
  \* Nobody claimed anything.
  /\ UNCHANGED <<owed, claimers, syncedBy>>

\* The leader of a group that needs an fsync and holds a nowait member does
\* not sync it: it leaves the group owed, as a job, and lets go of the
\* pipeline, handing it on as HandOff does (defer_group). Its own commit
\* call returns now; the group becomes visible only when a claimer lands it.
Defer ==
  \* Written, not synced, and its fsync is to be claimed.
  /\ stage = "written"           \* the records are in the log
  /\ ~synced                     \* nothing synced them yet
  /\ ~owed                       \* not already left owed
  /\ Deferred                    \* and a nowait member must not wait
  \* The group is owed now.
  /\ owed' = TRUE
  \* The ring's head is taken out to be held, when nothing is.
  /\ IF held = 0 /\ queue # <<>>
       THEN /\ held'  = Head(queue)      \* the oldest waiting ticket is held,
            /\ queue' = Tail(queue)      \* out of the ring, and its writer woken
       ELSE UNCHANGED <<held, queue>>    \* or nothing waits, or a ticket is held
  \* The mutex is released and the turn is over.
  /\ leader'     = 0             \* nobody holds the mutex
  /\ turnGroups' = 0             \* the turn's count starts over
  \* Nothing else changes: the group stays written, waiting for its claimer.
  /\ UNCHANGED <<pc, snap, hor, group, gi, gview, gacc, gwal, stage, synced,
                 dec, seq, pos, npos, outcome, completions, lastSeq, walEnd,
                 durable, store, visible>>
  \* Nobody claimed it yet.
  /\ UNCHANGED <<claimers, syncedBy, syncRuns>>

\* The thread of commit t claims the owed group's job with ONE CAS
\* (Job::claim). It may do so as a member polling its own queue (a nowait
\* member), as a blocking member waiting on its own group, or as the next
\* writer to take the pipeline, which lands what is owed before anything
\* else (land_pending). Bug DoubleClaim lets the CAS succeed on a claimed
\* job too.
ClaimOwed(t) ==
  \* The group is owed.
  /\ owed
  \* t's thread can reach it: a member, or a writer about to lead.
  /\ t \in Members \/ pc[t] \in {"ready", "queued"}
  \* The CAS succeeds only if nobody claimed it (the bug: also if somebody
  \* else did).
  /\ \/ claimers = {}
     \/ Mutant = "DoubleClaim" /\ t \notin claimers
  \* t is a claimer now.
  /\ claimers' = claimers \cup {t}
  \* Nothing else changes.
  /\ UNCHANGED <<pc, snap, hor, queue, held, leader, turnGroups, group, gi,
                 gview, gacc, gwal, stage, synced, dec, seq, pos, npos, outcome,
                 completions, lastSeq, walEnd, durable, store, visible>>
  \* The rest of the bookkeeping is untouched.
  /\ UNCHANGED <<owed, syncedBy, syncRuns>>

\* The claimer t runs the owed group's fsync (GroupSync's landing, through
\* sync_group): everything in the log is durable now.
OwedSync(t) ==
  \* t claimed the owed group and has not synced it.
  /\ owed                        \* the group is owed
  /\ t \in claimers              \* t won the claim
  /\ t \notin syncedBy           \* and has not run its fsync yet
  /\ stage = "written"           \* the group is still only written
  \* Everything in the log is durable now.
  /\ durable'  = walEnd          \* durable up to the end of the log
  /\ synced'   = TRUE            \* this group's sync is done
  /\ syncRuns' = syncRuns + 1    \* the fsync ran one more time
  /\ syncedBy' = syncedBy \cup {t}   \* and t ran it
  \* Nothing else changes.
  /\ UNCHANGED <<pc, snap, hor, queue, held, leader, turnGroups, group, gi,
                 gview, gacc, gwal, stage, dec, seq, pos, npos, outcome,
                 completions, lastSeq, walEnd, store, visible>>
  \* The claim stands.
  /\ UNCHANGED <<owed, claimers>>

\* The writers' versions go into the memtable (run_group), after the fsync
\* when the group needs one. Mutant PublishBeforeSync does not wait for it.
Apply ==
  \* Written, and synced if it must be.
  /\ stage = "written"                                        \* the records are in the log
  /\ synced \/ ~NeedsSync \/ Mutant = "PublishBeforeSync"      \* and durable if they must be
  \* An owed group is applied only by the thread that claimed it.
  /\ owed => claimers # {}
  \* Every writer's versions are in the memtable.
  /\ store' = store \cup UNION {VersionsOf(m) : m \in Writers}
  \* The leader moves on.
  /\ stage' = "applied"
  \* Nothing else changes.
  /\ UNCHANGED <<pc, snap, hor, queue, held, leader, turnGroups, group, gi,
                 gview, gacc, gwal, synced, dec, seq, pos, npos, outcome,
                 completions, lastSeq, walEnd, durable, visible>>
  \* The owed group's bookkeeping is untouched.
  /\ UNCHANGED landing

\* The visible sequence moves to the group's last one (visible_seq.publish):
\* the whole group becomes visible at once.
Publish ==
  \* Applied.
  /\ stage = "applied"
  \* Readers now see the group.
  /\ visible' = IF Writers = {} THEN visible ELSE lastSeq
  \* The leader moves on.
  /\ stage'   = "published"
  \* Nothing else changes.
  /\ UNCHANGED <<pc, snap, hor, queue, held, leader, turnGroups, group, gi,
                 gview, gacc, gwal, synced, dec, seq, pos, npos, outcome,
                 completions, lastSeq, walEnd, durable, store>>
  \* The owed group's bookkeeping is untouched.
  /\ UNCHANGED landing

\* Every member's caller gets its own answer, once (run_and_complete): an
\* accepted one "commit", a conflicting one "conflict". The leader still
\* holds the mutex.
Complete ==
  \* Published, and synced if it must be.
  /\ stage = "published"         \* the group is visible
  /\ synced \/ ~NeedsSync        \* and durable if it must be
  \* Every member is done.
  /\ pc'          = [t \in Txns |-> IF t \in Members THEN "done" ELSE pc[t]]
  \* Each with its own verdict.
  /\ outcome'     = [t \in Txns |-> IF t \in Members
                                      THEN (IF dec[t] = "accept" THEN "commit" ELSE "conflict")
                                      ELSE outcome[t]]
  \* Each told once.
  /\ completions' = [t \in Txns |-> IF t \in Members THEN completions[t] + 1 ELSE completions[t]]
  \* The group is over. A leader that kept it is about to hand off; an owed
  \* group was handed off already, so the pipeline is simply free.
  /\ group'       = <<>>
  /\ stage'       = IF owed THEN "idle" ELSE "handoff"
  \* The owed job, if any, is landed: nothing is owed or claimed now.
  /\ owed'        = FALSE
  /\ claimers'    = {}
  /\ syncedBy'    = {}
  \* Nothing else changes.
  /\ UNCHANGED <<snap, hor, queue, held, leader, turnGroups, gi, gview, gacc,
                 gwal, synced, dec, seq, pos, npos, lastSeq, walEnd, durable,
                 store, visible>>
  \* The count of fsyncs stays, for SingleSync.
  /\ UNCHANGED syncRuns

\* G2: the group's append or fsync fails before anything is applied. The log
\* is cut back to where the group began, nothing is applied or published, and
\* every member's caller is told it failed, the ones the leader had decided
\* to abort included. The sequences drawn are never used.
Fail ==
  \* The append happened and no fsync succeeded yet; a group writes nothing
  \* without a writer, so it cannot fail.
  /\ Faults                      \* failures can happen in this run
  /\ stage = "written"           \* the append happened
  /\ ~synced                     \* no fsync succeeded yet
  /\ Writers # {}                \* and there were records to lose
  \* An owed group fails only in its claimer's fsync.
  /\ owed => claimers # {}
  \* The log loses the group's bytes.
  /\ walEnd'      = gwal
  \* Every member is done, and failed.
  /\ pc'          = [t \in Txns |-> IF t \in Members THEN "done" ELSE pc[t]]
  /\ outcome'     = [t \in Txns |-> IF t \in Members THEN "failed" ELSE outcome[t]]
  /\ completions' = [t \in Txns |-> IF t \in Members THEN completions[t] + 1 ELSE completions[t]]
  \* The group is over. A leader that kept it is about to hand off; an owed
  \* group was handed off already.
  /\ group'       = <<>>
  /\ stage'       = IF owed THEN "idle" ELSE "handoff"
  \* Nothing is owed or claimed any more.
  /\ owed'        = FALSE
  /\ claimers'    = {}
  /\ syncedBy'    = {}
  \* Nothing else changes.
  /\ UNCHANGED <<snap, hor, queue, held, leader, turnGroups, gi, gview, gacc,
                 gwal, synced, dec, seq, pos, npos, lastSeq, durable, store,
                 visible>>
  \* The count of fsyncs stays.
  /\ UNCHANGED syncRuns

\* The leader ends its turn (hand_off, E21). If no ticket is held and the
\* ring is not empty, the ring's head becomes the held ticket, heading the
\* next group, and its writer is woken to lead it. Then the mutex is free.
HandOff ==
  \* The group's answers are given.
  /\ stage = "handoff"
  \* The ring's head is taken out to be held, when nothing is.
  /\ IF held = 0 /\ queue # <<>>
       THEN /\ held'  = Head(queue)      \* the oldest waiting ticket is held,
            /\ queue' = Tail(queue)      \* out of the ring, and its writer woken
       ELSE UNCHANGED <<held, queue>>    \* or nothing waits, or a ticket is held already
  \* The mutex is released and the turn is over.
  /\ leader'     = 0             \* nobody holds the mutex
  /\ turnGroups' = 0             \* the turn's count starts over
  /\ stage'      = "idle"        \* the next leader may begin
  \* Nothing else changes.
  /\ UNCHANGED <<pc, snap, hor, group, gi, gview, gacc, gwal, synced, dec,
                 seq, pos, npos, outcome, completions, lastSeq, walEnd,
                 durable, store, visible>>
  \* The owed group's bookkeeping is untouched.
  /\ UNCHANGED landing

\* Mutant DrainAll: instead of handing off, the leader keeps the mutex and
\* commits the next group of waiting tickets itself, as the code did before
\* E21 (drain_locked looped until the ring was empty).
LeadAgain(k) ==
  \* Only the planted bug does this.
  /\ Mutant = "DrainAll"
  \* No group is owed (a group is owed only after a hand-off).
  /\ ~owed
  \* The previous group's answers are given and tickets still wait.
  /\ stage = "handoff"                     \* the leader would hand off now
  /\ k \in 1..Min2(MaxGroup, Waiting)      \* but takes more waiting tickets
  \* The same leader takes the next group.
  /\ StartGroup(Take(k))                   \* a new group of them
  /\ queue' = LeftQueue(k)                 \* out of the ring
  /\ held'  = 0                            \* the held ticket first
  /\ pc'    = [u \in Txns |-> IF \E i \in 1..k : Take(k)[i] = u THEN "grouped" ELSE pc[u]]
  \* One more group in this turn.
  /\ turnGroups' = turnGroups + 1
  \* Nothing else changes.
  /\ UNCHANGED <<snap, hor, leader, dec, seq, pos, npos, outcome, completions,
                 lastSeq, walEnd, durable, store, visible>>

\* Every step the system can take.
Next ==
  \/ \E t \in Txns : Begin(t) \/ Submit(t) \/ PlainSubmit(t) \/ Push(t)       \* a writer's own steps
  \/ \E t \in Txns : \E k \in 1..MaxGroup : LeadWith(t, k) \/ Drain(t, k)     \* a writer becomes leader
  \/ Decide \/ Write \/ Sync \/ Apply \/ Publish \/ Complete \/ Fail \/ HandOff \* the leader's steps
  \/ Defer                                                                    \* a group left owed
  \/ \E t \in Txns : ClaimOwed(t) \/ OwedSync(t)                              \* an owed group landed
  \/ \E k \in 1..MaxGroup : LeadAgain(k)                                      \* only the planted bug

\* Every behaviour starts in Init, takes Next steps, and never stops while a
\* step is possible (weak fairness: a writer woken to lead does lead).
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)   \* start, step, and never stall

----------------------------------------------------------------------------
\* Invariants: what must hold in every state.

\* Every variable holds what its comment says.
TypeOK ==
  /\ pc \in [Txns -> {"idle", "begun", "ready", "queued", "grouped", "done"}]   \* a known place
  /\ snap \in [Txns -> 0..lastSeq]                       \* snapshots are sequences handed out
  /\ hor \in [Txns -> 0..lastSeq]                        \* so are horizons
  /\ held \in Txns \cup {0}                              \* a ticket, or none
  /\ leader \in Txns \cup {0}                            \* a writer, or nobody
  /\ dec \in [Txns -> {"none", "accept", "conflict"}]    \* a known verdict
  /\ seq \in [Txns -> 0..lastSeq]                        \* sequences handed out, or 0
  /\ outcome \in [Txns -> {"none", "commit", "conflict", "failed"}]   \* a known answer
  /\ stage \in {"idle", "deciding", "written", "applied", "published", "handoff"}   \* a known step
  /\ store \subseteq Keys \X (1..lastSeq)                \* versions of known keys at handed-out sequences
  /\ durable <= walEnd /\ walEnd <= lastSeq /\ visible <= lastSeq   \* nothing runs ahead of what exists
  /\ owed \in BOOLEAN                                    \* a group is owed, or not
  /\ claimers \subseteq Txns /\ syncedBy \subseteq claimers   \* claimers are commits' threads

\* What committing one at a time, in decision order, decides for
\* transaction t: it aborts exactly when a commit that landed before it in
\* that order wrote a key t touched at a sequence t's snapshot does not see.
SerialVerdict(t) ==
  IF \E j \in Txns :
       /\ Lands(j)                          \* j committed
       /\ pos[j] < pos[t]                   \* before t, in decision order
       /\ seq[j] > snap[t]                  \* at a sequence t's snapshot did not see
       /\ Writes[j] \cap Touched(t) # {}    \* writing a key t read or writes
  THEN "conflict" ELSE "commit"

\* THE HEADLINE. Every transaction that was answered "commit" or "conflict"
\* got the answer committing them one at a time would give. Example ruled
\* out: transactions 1 and 2 both write key 1 from snapshot 0 and share a
\* group; both "commit" would lose the first one's write. Lean:
\* group_eq_serial.
SerialEquivalent ==
  \A t \in Txns \ Plain :                                                      \* every transaction
    outcome[t] \in {"commit", "conflict"} => outcome[t] = SerialVerdict(t)    \* answered as one at a time

\* Of two commits that landed and write, the one decided first has the
\* smaller sequence: the log and the memtable order them as decided.
SeqFollowsDecisionOrder ==
  \A i, j \in Txns :                                                             \* any two commits
    Lands(i) /\ Lands(j) /\ seq[i] > 0 /\ seq[j] > 0 /\ pos[i] < pos[j] => seq[i] < seq[j]   \* in order

\* The memtable holds exactly the versions of the commits that landed and
\* were applied: nothing from a conflicting member or a failed group.
StoreHoldsCommits ==
  LET applied == {t \in Txns : Lands(t) /\ Writes[t] # {} /\                   \* landed writers
                     (outcome[t] = "commit" \/ (t \in Members /\ stage \in {"applied", "published"}))}   \* applied already
  IN store = UNION {VersionsOf(t) : t \in applied}                             \* are exactly the memtable

\* No torn group: every landed commit at or below the visible sequence is
\* in the memtable whole, so a snapshot sees a group all or nothing.
VisibleIsApplied ==
  \A t \in Txns : Lands(t) /\ seq[t] > 0 /\ seq[t] <= visible => VersionsOf(t) \subseteq store   \* visible means applied

\* An Immediate commit is visible only once it is durable, so no reader sees
\* a commit a power cut could erase. Example ruled out: the group published
\* before its fsync, the fsync fails, and a reader already saw the write.
DurableBeforeVisible ==
  \A t \in Immediate : Lands(t) /\ seq[t] > 0 /\ seq[t] <= visible => seq[t] <= durable   \* visible means durable

\* Every caller is told at most once, and a done commit exactly once.
TicketsCompleteOnce ==
  \A t \in Txns : completions[t] <= 1 /\ (pc[t] = "done" <=> completions[t] = 1)   \* once, and when done

\* A "commit" answer is true: the commit is visible, and durable when it
\* asked for Immediate.
TicketMeansVisible ==
  \A t \in Txns : outcome[t] = "commit" =>       \* a commit answer
    /\ seq[t] <= visible                         \* is visible
    /\ (t \in Immediate => seq[t] <= durable)    \* and durable when it waited for that

\* E21: a leader commits at most one group per hold of the mutex, then hands
\* the pipeline on, so no caller does the work of an unbounded queue of
\* others. Example ruled out: a writer whose own commit is done keeps the
\* mutex and commits group after group for others.
BoundedTurn == turnGroups <= 1   \* never a second group in one turn

\* Nothing is stuck: when no step is possible, every commit has its answer.
NoStuckTicket == (~ENABLED Next) => \A t \in Txns : pc[t] = "done"   \* stopped means finished

\* An owed group's fsync runs once, however many members poll for it at
\* once: one CAS lets one claimer in. Example ruled out: commits 1 and 3
\* both polling, both claiming, and both syncing the same group.
SingleSync == syncRuns <= 1   \* never a second fsync for one group

\* A witness, not a promise: no group is ever left owed. The nowait
\* configuration must break it, which shows its GREEN run really went
\* through owed groups and their claims.
NothingOwed == ~owed

\* While a group is owed and not yet landed, the pipeline writes no other
\* group: whoever takes it lands the owed one first.
OwedBlocksNextGroup == owed => stage = "written" \/ stage = "applied" \/ stage = "published"

----------------------------------------------------------------------------
\* Liveness: every commit eventually gets its answer, even though every
\* leader stops after one group: the hand-off always leaves a writer that
\* can lead the rest.
AllTicketsComplete == <>(\A t \in Txns : pc[t] = "done")   \* eventually everyone is done

----------------------------------------------------------------------------
\* The workload the configurations use.
\* Transactions 1 and 2 write key 1, so the one decided second conflicts
\* unless its snapshot saw the first. Transaction 3 reads key 1 and writes
\* key 2. Transaction 4, when present, is a plain write of key 1 that every
\* transaction behind it touching key 1 conflicts with. Transaction 5, when
\* present, only reads key 2: it is validated and takes no sequence.
ReadsW == [t \in Txns |-> CASE t = 3 -> {1}     \* 3 read key 1
                            [] t = 5 -> {2}     \* 5 read key 2
                            [] OTHER -> {}]     \* the rest read nothing
WritesW == [t \in Txns |-> CASE t = 3 -> {2}    \* 3 writes key 2
                             [] t = 5 -> {}     \* 5 writes nothing
                             [] OTHER -> {1}]   \* the rest write key 1

====
