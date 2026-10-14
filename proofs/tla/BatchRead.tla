---- MODULE BatchRead ----
\* E6: one view per read. A batch read of several keys at one snapshot
\* sequence, while flushes move data between views.
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/BatchView.lean:
\*   batch_one_view_point_in_time   a batch resolved against the view it
\*                                  captured answers every key as of its start
\*   batch_one_view_newest          each answer is the newest version the
\*                                  snapshot may see (with read_newest from
\*                                  LsmOrder.lean)
\*   batch_one_view_absent          each absent answer is right
\*   view_per_key_breaks_batch      the RED case, as a counterexample
\* TLC checks the same invariants here over every interleaving of writes,
\* flushes and the batch's key-by-key resolution.
\*
\* THE ENGINE.
\*   RegolithEngine::multi_get_latest   src/engine/mod.rs
\*     Loads the published view, then samples the read horizon as the
\*     batch's snapshot sequence. The batch registers no snapshot.
\*   RegolithEngine::multi_get_in_view  src/engine/mod.rs
\*     Without a merge operator, resolves every key against that one view.
\*     With one, it falls back to get_with_merge per key, and
\*     get_with_merge loads the current view again for each key.
\*   Flush (rotate_memtable and the flush that follows)
\*     Writes the memtable out as an L0 file. With no registered snapshot
\*     that needs it, a version shadowed by a newer one of the same key is
\*     not written.
\*
\* THE DEFECT (Mode = "ViewPerKey"). Between two keys of the batch, a write
\* lands a newer version of a later key and a flush writes the memtable out
\* without the version the batch's snapshot needs. The later key, resolved
\* against the new view, reads absent or older.
\*
\* THE FIX (Mode = "OneView"). Every key of the batch resolves against the
\* view captured at the start. That view holds its memtable by reference, so
\* the versions the snapshot needs stay reachable through it whatever later
\* flushes write.
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - A write is one step: sequence, memtable insert and publication.
\*   - The batch captures its view and samples its snapshot in one step. In
\*     the engine a write may land between the two; the read linearizes at
\*     the view load (the argument on RegolithEngine::get_latest), so that
\*     write is not part of the batch either way.
\*   - A flush goes straight to the new view; the intermediate view holding
\*     the frozen memtable answers the same as the one before it.
\*   - The flushed files are one set of versions, newest-first order inside
\*     it being decided by sequence (LsmOrder.tla covers the L0 order).
\*
\* CONFIGURATIONS.
\*   MC_BatchRead_Green                 Mode = "OneView"
\*     BatchConsistent and BatchExact hold.
\*   MC_BatchRead_Red_ViewPerKey        BatchConsistent fails.
\*   MC_BatchRead_Red_ViewPerKey_Exact  BatchExact fails: the second view
\*                                      changes an answer, not only its source.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Keys,       \* the keys writers write, naturals
  BatchKeys,  \* the keys the batch reads, in order: a sequence over Keys
  MaxSeq,     \* the last sequence a write may take, which bounds the writes
  MaxFlush,   \* the most flushes
  Mode        \* "OneView" (the fix) or "ViewPerKey" (the defect)

ASSUME Keys \subseteq Nat /\ Keys # {}
ASSUME BatchKeys \in Seq(Keys) /\ Len(BatchKeys) > 0
ASSUME MaxSeq \in Nat /\ MaxFlush \in Nat
ASSUME Mode \in {"OneView", "ViewPerKey"}

\* The memtable ids: one per flush, plus the first.
MemIds == 0..MaxFlush

\* The batch the configurations read (a .cfg file cannot spell a sequence):
\* key 1, key 2, then key 1 again, since multi_get accepts duplicates.
ReadOneTwoOne == <<1, 2, 1>>

VARIABLES
  seq,      \* the last sequence handed out; 0 before the first write
  mems,     \* [MemIds -> set of versions <<key, sequence>>]: every memtable;
            \* a view holds one by id and sees writes that land in it later
  active,   \* the id of the memtable taking writes
  views,    \* the published views, oldest first: <<memtable id, flushed versions>>
  history,  \* every version ever written; a ghost, never thinned
  bstate,   \* the batch: "idle", "reading" or "done"
  bsnap,    \* the batch's snapshot sequence
  bview,    \* the position in views of the view the batch captured
  bnext,    \* the position in BatchKeys of the next key to resolve
  bused,    \* the positions in views of the views keys were resolved against
  bout      \* [1..Len(BatchKeys) -> Nat]: each resolved key's answer

\* Every variable, so a step that changes none of them is a stutter.
vars == <<seq, mems, active, views, history, bstate, bsnap, bview, bnext, bused, bout>>

\* The greatest element of a finite, nonempty set of naturals.
Max(S) == CHOOSE m \in S : \A n \in S : n <= m

\* The sequences of the versions of key k in a set of versions F that a
\* snapshot at s may see.
Visible(F, k, s) == {v[2] : v \in {x \in F : x[1] = k /\ x[2] <= s}}

\* The newest of those, or 0 for absent (sequences start at 1).
NewestIn(F, k, s) == IF Visible(F, k, s) = {} THEN 0 ELSE Max(Visible(F, k, s))

\* A point read of key k at snapshot s through view `view`: the memtable
\* first, then the flushed versions. The memtable is read as it is now, which
\* is how the engine's view sees its memtable.
Resolve(view, k, s) ==
  IF Visible(mems[view[1]], k, s) # {}
    THEN NewestIn(mems[view[1]], k, s)
    ELSE NewestIn(view[2], k, s)

\* What a flush writes: each key's newest version only, as when no
\* registered snapshot needs an older one.
NewestOnly(F) == {v \in F : ~\E w \in F : w[1] = v[1] /\ w[2] > v[2]}

\* The position in views of the current view: the last one published.
Current == Len(views)

\* The start: no write, one view over an empty memtable, the batch not begun.
Init ==
  /\ seq     = 0
  /\ mems    = [m \in MemIds |-> {}]
  /\ active  = 0
  /\ views   = <<<<0, {}>>>>
  /\ history = {}
  /\ bstate  = "idle"
  /\ bsnap   = 0
  /\ bview   = 0
  /\ bnext   = 1
  /\ bused   = {}
  /\ bout    = [i \in 1..Len(BatchKeys) |-> 0]

\* A write of key k: the next sequence, into the active memtable, published.
Put(k) ==
  /\ seq < MaxSeq
  /\ seq'     = seq + 1
  /\ mems'    = [mems EXCEPT ![active] = @ \cup {<<k, seq + 1>>}]
  /\ history' = history \cup {<<k, seq + 1>>}
  /\ UNCHANGED <<active, views, bstate, bsnap, bview, bnext, bused, bout>>

\* A flush: the active memtable is written out (its newest versions only)
\* and a new view publishes a fresh memtable over the flushed versions.
Flush ==
  /\ active < MaxFlush
  /\ mems[active] # {}
  /\ active' = active + 1
  /\ views'  = Append(views, <<active + 1, views[Current][2] \cup NewestOnly(mems[active])>>)
  /\ UNCHANGED <<seq, mems, history, bstate, bsnap, bview, bnext, bused, bout>>

\* multi_get_latest: the batch captures the current view and takes the
\* newest published sequence as its snapshot.
Begin ==
  /\ bstate = "idle"
  /\ bstate' = "reading"
  /\ bsnap'  = seq
  /\ bview'  = Current
  /\ UNCHANGED <<seq, mems, active, views, history, bnext, bused, bout>>

\* Resolve the next key: against the captured view (the fix), or against
\* the view current at this moment (the defect).
ResolveNext ==
  LET at == IF Mode = "OneView" THEN bview ELSE Current
      k  == BatchKeys[bnext]
  IN /\ bstate = "reading"
     /\ bout'   = [bout EXCEPT ![bnext] = Resolve(views[at], k, bsnap)]
     /\ bused'  = bused \cup {at}
     /\ bnext'  = bnext + 1
     /\ bstate' = IF bnext = Len(BatchKeys) THEN "done" ELSE "reading"
     /\ UNCHANGED <<seq, mems, active, views, history, bsnap, bview>>

\* Every step the system can take.
Next ==
  \/ \E k \in Keys : Put(k)
  \/ Flush
  \/ Begin
  \/ ResolveNext

\* Every behaviour: start in Init, then take Next steps or stutter.
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ seq \in 0..MaxSeq
  /\ active \in MemIds
  /\ Len(views) = active + 1
  /\ bstate \in {"idle", "reading", "done"}
  /\ bnext \in 1..(Len(BatchKeys) + 1)
  /\ bused \subseteq 1..Len(views)
  /\ history \subseteq Keys \X (1..MaxSeq)

\* THE HEADLINE. Every key of the batch resolves against the same view.
BatchConsistent == Cardinality(bused) <= 1

\* What that buys: every key resolved so far answers the newest version of
\* that key the batch's snapshot may see, as of the batch's start.
\* Lean: batch_one_view_point_in_time, batch_one_view_newest.
BatchExact ==
  \A i \in 1..(bnext - 1) : bout[i] = NewestIn(history, BatchKeys[i], bsnap)

====
