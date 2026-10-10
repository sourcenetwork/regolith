---- MODULE ReadViewPublishers ----
\* ===========================================================================
\* THE STORY
\* ===========================================================================
\* ReadView.tla checks the read view's cell: a reader never holds a freed
\* view, and one compare-and-swap (CAS) publication never overwrites
\* another. It treats a view as a number. This model looks inside the view,
\* at the publishers group commit and the flush off the commit path brought
\* (Phase 6 integration), and checks that each of them publishing through
\* the CAS (ReadViewCell::publish, src/engine/read_view.rs) loses no data.
\*
\* A view is three things: the active memtable writers append to, the frozen
\* memtables waiting for a flush (oldest first), and the tables of the
\* current version. Data lives in exactly those three places.
\*
\* The publishers, and the lock each one already holds, so which of them can
\* race:
\*   - a rotation seals the active memtable behind a fresh one
\*     (seal_active, and drain_memtables's seal), under the pipeline mutex;
\*   - a flush, by the compaction worker, by a writer after its commit, or
\*     by a writer inside its stall step (Flusher::flush_oldest), takes the
\*     oldest frozen memtable, installs its table (a version publish), then
\*     retires the memtable from the frozen list (a memtable publish). The
\*     three flush paths share the `flushing` exclusion, so one flush runs
\*     at a time, and it is not under the pipeline mutex;
\*   - a compaction installs its output, and an ingest installs its table
\*     (version publishes, under the version-set mutex, which every version
\*     publish holds while it publishes: VersionGuard::drop).
\* drop_all also publishes, but it holds the pipeline, the flush exclusion
\* and the compaction gate at once, so it races none of these and is left
\* out.
\*
\* So a seal can race a flush's retire, and either can race a version
\* publish. Each publisher builds its next view from the view it loaded and
\* swaps it in only if that view is still the published one; otherwise it
\* builds again on what won.
\*
\* Tiny example of what goes wrong without the CAS. The view is
\* (active 2, frozen [1], tables {1}): memtable 1 was flushed and its table
\* installed, and the flush is about to retire it. The flush builds
\* (active 2, frozen [], tables {1}). Meanwhile a rotation seals 2 behind a
\* fresh 3 and publishes (active 3, frozen [1, 2], tables {1}). If the flush
\* now stores its view without the CAS, the published view is
\* (active 2, frozen [], tables {1}): memtable 3, where writers have been
\* appending, is in no view at all, and every write in it is lost.
\*
\* What this model checks cannot happen:
\*   - a memtable's data is in no published place (NoLostMemtable);
\*   - an ingested table is not in the published version (NoLostIngest);
\*   - a memtable a flush retired comes back (RetiredStayGone), which would
\*     flush it twice and install an old table over a newer one;
\*   - the frozen list leaves seal order (FrozenInSealOrder), which a flush
\*     relies on: it installs the oldest first (LsmOrder.tla).
\*
\* WHAT IS MODELLED, and the code each piece mirrors:
\*   pub        ReadViewCell::current: [active, frozen, tables]
\*   nextMt     the id the next fresh memtable gets (MemTable::new before
\*              the publication)
\*   ingested   how many tables ingests installed; ingest n is table 100+n
\*   sPhase...  the rotation's progress inside ReadViewCell::publish: idle,
\*              or built (it loaded sBase and built sNext)
\*   fPhase...  the flush's progress: idle, picked (it took the oldest
\*              frozen memtable fTarget), installBuilt, installed,
\*              retireBuilt
\*   cPhase...  the compaction or ingest's progress: idle, built, or
\*              retry (its swap lost and it builds again)
\*   vOwner     who holds the version-set mutex: nobody, the flush's
\*              install, or a compaction or ingest
\*   retired    a ghost: every memtable a flush retired
\*
\* WHAT IS LEFT OUT, and why that loses nothing:
\*   - Readers and reclamation: ReadView.tla checks those for any content.
\*   - Keys: a memtable or a table stands for all the data it holds.
\*   - A compaction's merge: it replaces tables by one holding the same
\*     data, so the set of places data lives in does not change.
\*
\* CONFIGURATIONS (each GREEN must pass, each RED must break the one
\* invariant it names):
\*   MC_ReadViewPublishers_Green              every publisher swaps by CAS.
\*   MC_ReadViewPublishers_Red_PlainRetire    a flush's retire stores its
\*                                            view without the CAS: a seal
\*                                            racing it is lost,
\*                                            NoLostMemtable breaks.
\*   MC_ReadViewPublishers_Red_PlainVersion   a compaction's or an ingest's
\*                                            version publish stores without
\*                                            the CAS: a seal racing it is
\*                                            lost, NoLostMemtable breaks.
\*
\* Lean, proofs/lean/Regolith/ReadViewPublishers.lean, proves the same
\* rules for every number of publications.

\* Numbers, sequences and finite sets.
EXTENDS Naturals, Sequences, FiniteSets

\* The fixed inputs of a configuration.
CONSTANTS
  \* The most memtables the model creates (the first one included).
  MaxMemtables,
  \* The most tables ingests install.
  MaxIngests,
  \* The most compactions that install.
  MaxCompactions,
  \* "Green" for the real code, or the name of one planted bug.
  Mode

\* The bug names this model knows.
ASSUME Mode \in {"Green", "PlainRetire", "PlainVersion"}

\* The table id ingest n installs: well apart from memtable ids.
IngestTable(n) == 100 + n

\* The memtables in a frozen list, as a set.
Range(s) == {s[i] : i \in 1..Len(s)}

\* `s` without the element `x`, order kept (retire_memtable, by identity).
Without(s, x) == SelectSeq(s, LAMBDA y : y # x)

\* The state that changes from step to step.
VARIABLES
  \* The published view.
  pub,
  \* The id the next fresh memtable gets.
  nextMt,
  \* How many tables ingests have installed.
  ingested,
  \* How many compactions have installed.
  compacted,
  \* The rotation: "idle" or "built", the view it built from, and the one
  \* it built.
  sPhase, sBase, sNext,
  \* The flush: its step, the memtable it flushes, the view it built from,
  \* and the one it built.
  fPhase, fTarget, fBase, fNext,
  \* The compaction or ingest: "idle", "built" or "retry"; whether it is
  \* an ingest; the view it built from, and the one it built.
  cPhase, cIngest, cBase, cNext,
  \* Who holds the version-set mutex: "none", "flush" or "version".
  vOwner,
  \* Ghost: every memtable a flush retired.
  retired

\* Every variable.
vars == <<pub, nextMt, ingested, compacted, sPhase, sBase, sNext,
          fPhase, fTarget, fBase, fNext, cPhase, cIngest, cBase, cNext,
          vOwner, retired>>

\* A view with nothing in it, the starting value of the publishers' scratch.
NoView == [active |-> 0, frozen |-> <<>>, tables |-> {}]

\* The start: memtable 1 is active, nothing is frozen or in a table.
Init ==
  \* Memtable 1 takes the writes.
  /\ pub = [active |-> 1, frozen |-> <<>>, tables |-> {}]
  \* The next fresh memtable is 2.
  /\ nextMt = 2
  \* Nothing ingested or compacted yet.
  /\ ingested = 0
  /\ compacted = 0
  \* Every publisher is idle, with nothing built.
  /\ sPhase = "idle" /\ sBase = NoView /\ sNext = NoView
  /\ fPhase = "idle" /\ fTarget = 0 /\ fBase = NoView /\ fNext = NoView
  /\ cPhase = "idle" /\ cIngest = FALSE /\ cBase = NoView /\ cNext = NoView
  \* Nobody holds the version-set mutex.
  /\ vOwner = "none"
  \* Nothing has been retired.
  /\ retired = {}

\* Whether a publisher's swap goes in. The real code: only if the view it
\* built from is still the published one. A plain store always goes in.
Swaps(base, plain) == plain \/ pub = base

\* ---- The rotation (under the pipeline mutex) -----------------------------

\* The rotation loads the published view and builds the next: the active
\* memtable joins the end of the frozen list and the fresh one, made before
\* the publication, becomes active (seal_active's closure).
SealBuild ==
  \* Idle, and a fresh memtable may still be made.
  /\ sPhase = "idle"
  /\ nextMt <= MaxMemtables
  \* It built from the view published now.
  /\ sBase' = pub
  \* The fresh memtable is active; the sealed one is the newest frozen.
  /\ sNext' = [active |-> nextMt, frozen |-> Append(pub.frozen, pub.active),
               tables |-> pub.tables]
  /\ sPhase' = "built"
  \* Nothing else changes.
  /\ UNCHANGED <<pub, nextMt, ingested, compacted, fPhase, fTarget, fBase, fNext,
                 cPhase, cIngest, cBase, cNext, vOwner, retired>>

\* The rotation's compare-and-swap. In, the fresh memtable is used up;
\* out, it builds again on what won (the closure runs again).
SealSwap ==
  \* It built a view.
  /\ sPhase = "built"
  \* The rotation always swaps by CAS: no bug here touches it.
  /\ IF Swaps(sBase, FALSE)
     \* In: its view is published, and the next fresh memtable is a new one.
     THEN /\ pub' = sNext
          /\ nextMt' = nextMt + 1
     \* Out: nothing changes, and it builds again.
     ELSE UNCHANGED <<pub, nextMt>>
  \* Either way the attempt is over.
  /\ sPhase' = "idle"
  \* Nothing else changes.
  /\ UNCHANGED <<sBase, sNext, ingested, compacted, fPhase, fTarget, fBase, fNext,
                 cPhase, cIngest, cBase, cNext, vOwner, retired>>

\* ---- The flush (worker, after a commit, or in a stall step) -------------

\* The flush takes the oldest frozen memtable (flush_oldest_inner reads
\* `frozen.first()`) and writes its table, which publishes nothing.
FlushPick ==
  \* Idle, and something is frozen.
  /\ fPhase = "idle"
  /\ pub.frozen # <<>>
  \* The oldest frozen memtable.
  /\ fTarget' = Head(pub.frozen)
  /\ fPhase' = "picked"
  \* Nothing else changes.
  /\ UNCHANGED <<pub, nextMt, ingested, compacted, sPhase, sBase, sNext, fBase, fNext,
                 cPhase, cIngest, cBase, cNext, vOwner, retired>>

\* The flush installs its table: under the version-set mutex, it builds a
\* view whose version holds the new table (VersionSet::apply of AddFile,
\* then VersionGuard::drop's publication).
FlushInstallBuild ==
  \* The table is written, and the mutex is free or already the flush's.
  /\ fPhase = "picked"
  /\ vOwner \in {"none", "flush"}
  \* It holds the mutex until its swap goes in.
  /\ vOwner' = "flush"
  \* It built from the view published now, adding its table.
  /\ fBase' = pub
  /\ fNext' = [pub EXCEPT !.tables = pub.tables \cup {fTarget}]
  /\ fPhase' = "installBuilt"
  \* Nothing else changes.
  /\ UNCHANGED <<pub, nextMt, ingested, compacted, sPhase, sBase, sNext, fTarget,
                 cPhase, cIngest, cBase, cNext, retired>>

\* The install's swap: a version publish, so the PlainVersion bug stores it.
\* In: the table is published and the mutex released. Out: it builds again,
\* still holding the mutex.
FlushInstallSwap ==
  \* It built its view.
  /\ fPhase = "installBuilt"
  /\ IF Swaps(fBase, Mode = "PlainVersion")
     \* In: the version with the table is published; the mutex is free.
     THEN /\ pub' = fNext
          /\ fPhase' = "installed"
          /\ vOwner' = "none"
     \* Out: back to build, the mutex still its own.
     ELSE /\ fPhase' = "picked"
          /\ UNCHANGED <<pub, vOwner>>
  \* Nothing else changes.
  /\ UNCHANGED <<nextMt, ingested, compacted, sPhase, sBase, sNext, fTarget, fBase, fNext,
                 cPhase, cIngest, cBase, cNext, retired>>

\* The flush retires its memtable: it builds a view whose frozen list lacks
\* it, by identity (retire_memtable's closure).
FlushRetireBuild ==
  \* The table is installed.
  /\ fPhase = "installed"
  \* It built from the view published now, without its memtable.
  /\ fBase' = pub
  /\ fNext' = [pub EXCEPT !.frozen = Without(pub.frozen, fTarget)]
  /\ fPhase' = "retireBuilt"
  \* Nothing else changes.
  /\ UNCHANGED <<pub, nextMt, ingested, compacted, sPhase, sBase, sNext, fTarget,
                 cPhase, cIngest, cBase, cNext, vOwner, retired>>

\* The retire's swap: a memtable publish, so the PlainRetire bug stores it.
\* In, the flush is done; out, it builds again.
FlushRetireSwap ==
  \* It built its view.
  /\ fPhase = "retireBuilt"
  /\ IF Swaps(fBase, Mode = "PlainRetire")
     \* In: the memtable is gone from the frozen list, for good.
     THEN /\ pub' = fNext
          /\ retired' = retired \cup {fTarget}
          /\ fPhase' = "idle"
     \* Out: back to build on what won.
     ELSE /\ fPhase' = "installed"
          /\ UNCHANGED <<pub, retired>>
  \* Nothing else changes.
  /\ UNCHANGED <<nextMt, ingested, compacted, sPhase, sBase, sNext, fTarget, fBase, fNext,
                 cPhase, cIngest, cBase, cNext, vOwner>>

\* ---- Compaction and ingest (version publishes) ----------------------------

\* The view a compaction or an ingest builds from `v`: a compaction's
\* output holds the same data as its inputs, so the set of places data lives
\* in is the same; an ingest adds its table.
VersionResult(v, ingest) ==
  \* An ingest: `v` with the next ingested table added ...
  IF ingest
  THEN [v EXCEPT !.tables = v.tables \cup {IngestTable(ingested + 1)}]
  \* ... a compaction: `v` as it is.
  ELSE v

\* A compaction or an ingest starts to install: it takes the version-set
\* mutex and builds its view from the one published now.
VersionBuild ==
  \* Idle, and the mutex is free.
  /\ cPhase = "idle"
  /\ vOwner = "none"
  \* It is an ingest, if one is left, or a compaction, if one is left.
  /\ \E ingest \in BOOLEAN :
       /\ IF ingest THEN ingested < MaxIngests ELSE compacted < MaxCompactions
       /\ cIngest' = ingest
       /\ cNext' = VersionResult(pub, ingest)
  \* It holds the mutex until its swap goes in.
  /\ vOwner' = "version"
  /\ cBase' = pub
  /\ cPhase' = "built"
  \* Nothing else changes.
  /\ UNCHANGED <<pub, nextMt, ingested, compacted, sPhase, sBase, sNext,
                 fPhase, fTarget, fBase, fNext, retired>>

\* After a lost swap it builds again, from the view published now, still
\* holding the mutex.
VersionRebuild ==
  \* Its swap lost.
  /\ cPhase = "retry"
  /\ cBase' = pub
  /\ cNext' = VersionResult(pub, cIngest)
  /\ cPhase' = "built"
  \* Nothing else changes.
  /\ UNCHANGED <<pub, nextMt, ingested, compacted, sPhase, sBase, sNext,
                 fPhase, fTarget, fBase, fNext, cIngest, vOwner, retired>>

\* The version publish's swap, which the PlainVersion bug stores. In, the
\* result is published and the mutex released; out, it builds again.
VersionSwap ==
  \* It built its view.
  /\ cPhase = "built"
  /\ IF Swaps(cBase, Mode = "PlainVersion")
     \* In: published; count the ingest or the compaction.
     THEN /\ pub' = cNext
          /\ ingested' = IF cIngest THEN ingested + 1 ELSE ingested
          /\ compacted' = IF cIngest THEN compacted ELSE compacted + 1
          /\ cPhase' = "idle"
          /\ vOwner' = "none"
     \* Out: build again on what won.
     ELSE /\ cPhase' = "retry"
          /\ UNCHANGED <<pub, ingested, compacted, vOwner>>
  \* Nothing else changes.
  /\ UNCHANGED <<nextMt, sPhase, sBase, sNext, fPhase, fTarget, fBase, fNext,
                 cIngest, cBase, cNext, retired>>

\* Every step any publisher can take.
Next ==
  \* The rotation builds or swaps ...
  \/ SealBuild \/ SealSwap
  \* ... the flush picks, installs or retires ...
  \/ FlushPick \/ FlushInstallBuild \/ FlushInstallSwap \/ FlushRetireBuild \/ FlushRetireSwap
  \* ... or a compaction or an ingest builds, swaps or builds again.
  \/ VersionBuild \/ VersionSwap \/ VersionRebuild

\* Every behaviour: start in Init, then take Next steps or stutter.
Spec == Init /\ [][Next]_vars

\* ===========================================================================
\* THE RULES
\* ===========================================================================

\* Every variable holds what its comment says.
TypeOK ==
  \* The published view's active memtable is one that exists ...
  /\ pub.active \in 1..MaxMemtables
  \* ... and the counters stay in their bounds.
  /\ nextMt \in 2..(MaxMemtables + 1)
  /\ ingested \in 0..MaxIngests
  /\ compacted \in 0..MaxCompactions

\* THE HEADLINE. Every memtable ever made holds its data in a published
\* place: it is the active one, a frozen one, or its table is in the
\* version. Rules out the story: the flush's plain store publishes
\* (active 2, frozen [], tables {1}) over (active 3, frozen [1, 2]), and
\* memtable 3, with every write in it, is nowhere. Lean: no_lost_memtable.
NoLostMemtable ==
  \* Every memtable made so far ...
  \A m \in 1..(nextMt - 1) :
    \* ... is active, frozen, or in a table of the version.
    m = pub.active \/ m \in Range(pub.frozen) \/ m \in pub.tables

\* Every table an ingest installed is in the published version. Rules out
\* a version publish built before the ingest's overwriting it. Lean:
\* no_lost_ingest.
NoLostIngest ==
  \* Every ingest so far has its table in the version.
  \A n \in 1..ingested : IngestTable(n) \in pub.tables

\* A memtable a flush retired never comes back. Rules out a stale view
\* republishing a frozen list that still names it: the next flush would
\* write it again and install that old table above newer ones. Lean:
\* retired_stay_gone.
RetiredStayGone ==
  \* Every retired memtable is neither active nor frozen.
  \A m \in retired : m # pub.active /\ m \notin Range(pub.frozen)

\* The frozen list is in seal order, oldest first, which is the order
\* flushes install them in (LsmOrder.tla). Lean: frozen_sorted.
FrozenInSealOrder ==
  \* For every two places in the frozen list, the earlier one ...
  \A i \in 1..Len(pub.frozen) : \A j \in (i + 1)..Len(pub.frozen) :
    \* ... holds the memtable sealed first.
    pub.frozen[i] < pub.frozen[j]

====
