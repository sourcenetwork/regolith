---- MODULE SnapshotRegistry ----
\* 4.6 and 4.7 item 9: the lock-free snapshot registry. A reader registers
\* without a lock by announcing, sampling and confirming; a compaction
\* samples the horizon and then scans the slots. The minimum it may use
\* never exceeds a live snapshot, and every live snapshot is either in the
\* list it scanned or at or above the horizon it sampled, which is what
\* StripeCompaction.tla needs to cut stripes at every live snapshot.
\*
\* PROVED FOR EVERY SIZE in Lean, proofs/lean/Regolith/SnapshotRegistry.lean:
\*   scan_respects_live        against any interleaving, written as the
\*                             moments of each access on a horizon that only
\*                             rises: the compaction's minimum is at most the
\*                             snapshot, and the snapshot is in its list or
\*                             at or above its sampled horizon
\*   no_confirm_breaks_min     the RED NoConfirm case, as a counterexample
\* TLC checks the same invariants here over every interleaving of a few
\* readers, the writers that raise the horizon, and a compaction that runs
\* again and again.
\*
\* THE ENGINE TODAY. SnapshotRegistry::register_at
\* (src/engine/snapshot_registry.rs) samples the horizon and inserts the pin
\* under one Mutex, and compaction reads `live_seqs` under the same Mutex.
\* Plan 4.6 replaces the Mutex with the protocol below; this model is its
\* specification, written before the code.
\*
\* THE PROTOCOL (the design; names are the plan's).
\*   Reader, in its own slot:
\*     announce  read the horizon h, then publish h in the slot: two steps,
\*               a load and a store, with anything in between;
\*     sample    read the horizon again;
\*     confirm   if it is still h, the snapshot is live at h; otherwise
\*               announce the new value and sample again.
\*   Compaction:
\*     sample the horizon c, then scan the slots one at a time; the list is
\*     every value seen, and the minimum it may use is the least of c and
\*     the list.
\*   Release empties the slot.
\*
\* WHY IT HOLDS. A scan that saw the reader's final value has it in the
\* list. A scan that missed it ran before the final store, so the
\* compaction's sample ran before it too, and before the confirming sample,
\* which read h: the horizon only rises, so c <= h. Every value a slot ever
\* held is a horizon read before the final one, hence <= h.
\*
\* THE DEFECTS.
\*   Confirm = "None": the reader goes live at the value it announced,
\*     without sampling again. A compaction that sampled a higher horizon
\*     and scanned the slot before the store uses a minimum above the
\*     snapshot.
\*   Order = "ScanThenSample": the compaction scans first and samples the
\*     horizon after. A reader that registers after the scan passed its
\*     slot, while the horizon is still low, is below the minimum.
\*
\* DESIGN CHOICES where the plan leaves room (recorded in the report):
\*   - "Announce, sample, confirm" is read as: announce the horizon seen,
\*     sample it again, confirm the two agree, else re-announce. The slot
\*     then holds exactly the snapshot's sequence, which stripes need (a
\*     lower bound in the slot would cut a stripe at the wrong place).
\*   - Memory ordering is sequentially consistent here; the loads and
\*     stores need SeqCst (a store followed by a load on each side), which
\*     loom checks, not TLA+.
\*
\* CONFIGURATIONS.
\*   MC_SnapshotRegistry_Green                  MinBelowLive, LiveCovered
\*                                              and LiveSlotExact hold
\*   MC_SnapshotRegistry_Red_NoConfirm          MinBelowLive fails
\*   MC_SnapshotRegistry_Red_ScanThenSample     MinBelowLive fails

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
  Readers,  \* reader ids, model values; each registers once, and the
            \* readers are interchangeable
  MaxSeq,   \* the highest the horizon may rise: bounds the writers
  Confirm,  \* "Recheck" (the fix) or "None" (the defect)
  Order     \* "SampleThenScan" (the fix) or "ScanThenSample" (the defect)

ASSUME MaxSeq \in Nat
ASSUME Confirm \in {"Recheck", "None"}
ASSUME Order \in {"SampleThenScan", "ScanThenSample"}

\* An empty slot. Sequences are >= 0.
Empty == -1

VARIABLES
  horizon,  \* the visible sequence a snapshot reads at; only rises
  slot,     \* [Readers -> Int] each reader's published value, or Empty
  rphase,   \* [Readers -> {"idle","read","announced","live","done"}]
  rtmp,     \* [Readers -> Nat] the horizon the reader last read
  snapR,    \* [Readers -> Nat] the live snapshot's sequence
  cphase,   \* the compaction: "idle", "scanning", "sampling" or "using"
  c,        \* the horizon the compaction sampled
  scanned,  \* the readers whose slot the current scan has read
  vals,     \* the values the current scan saw: the list
  m         \* the minimum the compaction uses

\* Every variable, so a step that changes none of them is a stutter.
vars == <<horizon, slot, rphase, rtmp, snapR, cphase, c, scanned, vals, m>>

\* The least element of a finite, nonempty set of integers.
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

\* Renaming the readers changes nothing the invariants look at, so TLC
\* checks one state of each set of states that differ only by a renaming.
ReaderSymmetry == Permutations(Readers)

\* The start: horizon 0, empty slots, no registration, no compaction.
Init ==
  /\ horizon = 0
  /\ slot    = [r \in Readers |-> Empty]
  /\ rphase  = [r \in Readers |-> "idle"]
  /\ rtmp    = [r \in Readers |-> 0]
  /\ snapR   = [r \in Readers |-> 0]
  /\ cphase  = "idle"
  /\ c       = 0
  /\ scanned = {}
  /\ vals    = {}
  /\ m       = 0

\* A commit publishes: the horizon rises by one.
Advance ==
  /\ horizon < MaxSeq
  /\ horizon' = horizon + 1
  /\ UNCHANGED <<slot, rphase, rtmp, snapR, cphase, c, scanned, vals, m>>

\* Announce, first half: the reader reads the horizon.
AnnounceRead(r) ==
  /\ rphase[r] = "idle"
  /\ rtmp'   = [rtmp EXCEPT ![r] = horizon]
  /\ rphase' = [rphase EXCEPT ![r] = "read"]
  /\ UNCHANGED <<horizon, slot, snapR, cphase, c, scanned, vals, m>>

\* Announce, second half: the reader publishes what it read. The defect
\* (Confirm = "None") goes live at that value here.
AnnouncePublish(r) ==
  /\ rphase[r] = "read"
  /\ slot' = [slot EXCEPT ![r] = rtmp[r]]
  /\ IF Confirm = "None"
       THEN /\ rphase' = [rphase EXCEPT ![r] = "live"]
            /\ snapR'  = [snapR EXCEPT ![r] = rtmp[r]]
       ELSE /\ rphase' = [rphase EXCEPT ![r] = "announced"]
            /\ UNCHANGED snapR
  /\ UNCHANGED <<horizon, rtmp, cphase, c, scanned, vals, m>>

\* Sample and confirm: the reader reads the horizon again. If it is still
\* the value announced, the snapshot is live there. Otherwise the new value
\* is announced next (back to the publish step), and sampled again.
SampleConfirm(r) ==
  /\ rphase[r] = "announced"
  /\ IF horizon = rtmp[r]
       THEN /\ rphase' = [rphase EXCEPT ![r] = "live"]
            /\ snapR'  = [snapR EXCEPT ![r] = rtmp[r]]
            /\ UNCHANGED rtmp
       ELSE /\ rphase' = [rphase EXCEPT ![r] = "read"]
            /\ rtmp'   = [rtmp EXCEPT ![r] = horizon]
            /\ UNCHANGED snapR
  /\ UNCHANGED <<horizon, slot, cphase, c, scanned, vals, m>>

\* The reader releases its snapshot: its slot empties.
Release(r) ==
  /\ rphase[r] = "live"
  /\ slot'   = [slot EXCEPT ![r] = Empty]
  /\ rphase' = [rphase EXCEPT ![r] = "done"]
  /\ UNCHANGED <<horizon, rtmp, snapR, cphase, c, scanned, vals, m>>

\* The compaction samples the horizon. The fix does this before it scans;
\* the defect after.
CSample ==
  /\ \/ Order = "SampleThenScan" /\ cphase = "idle"
     \/ Order = "ScanThenSample" /\ cphase = "sampling"
  /\ c'      = horizon
  /\ cphase' = IF Order = "SampleThenScan" THEN "scanning" ELSE "using"
  /\ m'      = IF Order = "SampleThenScan" THEN m ELSE Min({horizon} \cup vals)
  /\ UNCHANGED <<horizon, slot, rphase, rtmp, snapR, scanned, vals>>

\* The compaction reads one slot it has not read in this scan, and adds
\* its value to the list when the slot is not empty.
CScan(r) ==
  /\ \/ Order = "SampleThenScan" /\ cphase = "scanning"
     \/ Order = "ScanThenSample" /\ cphase \in {"idle", "scanning"}
  /\ r \notin scanned
  /\ scanned' = scanned \cup {r}
  /\ vals'    = IF slot[r] = Empty THEN vals ELSE vals \cup {slot[r]}
  /\ cphase'  = "scanning"
  /\ UNCHANGED <<horizon, slot, rphase, rtmp, snapR, c, m>>

\* The scan has read every slot. The fix now has its minimum; the defect
\* still has to sample the horizon.
CScanDone ==
  /\ cphase = "scanning"
  /\ scanned = Readers
  /\ cphase' = IF Order = "SampleThenScan" THEN "using" ELSE "sampling"
  /\ m'      = IF Order = "SampleThenScan" THEN Min({c} \cup vals) ELSE m
  /\ UNCHANGED <<horizon, slot, rphase, rtmp, snapR, c, scanned, vals>>

\* The compaction finishes and a later one may start.
CFinish ==
  /\ cphase = "using"
  /\ cphase'  = "idle"
  /\ c'       = 0
  /\ scanned' = {}
  /\ vals'    = {}
  /\ m'       = 0
  /\ UNCHANGED <<horizon, slot, rphase, rtmp, snapR>>

\* Every step the system can take.
Next ==
  \/ Advance
  \/ \E r \in Readers : AnnounceRead(r) \/ AnnouncePublish(r) \/ SampleConfirm(r) \/ Release(r)
  \/ CSample
  \/ \E r \in Readers : CScan(r)
  \/ CScanDone
  \/ CFinish

\* Every behaviour: start in Init, then take Next steps or stutter.
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Invariants.

\* Every variable holds what its comment says.
TypeOK ==
  /\ horizon \in 0..MaxSeq
  /\ slot \in [Readers -> {Empty} \cup (0..MaxSeq)]
  /\ rphase \in [Readers -> {"idle", "read", "announced", "live", "done"}]
  /\ rtmp \in [Readers -> 0..MaxSeq]
  /\ snapR \in [Readers -> 0..MaxSeq]
  /\ cphase \in {"idle", "scanning", "sampling", "using"}
  /\ scanned \subseteq Readers
  /\ vals \subseteq 0..MaxSeq

\* The readers holding a live snapshot.
Live == {r \in Readers : rphase[r] = "live"}

\* THE HEADLINE. The minimum a compaction uses never exceeds a live
\* snapshot, whenever that snapshot became live. Lean: scan_respects_live.
MinBelowLive == cphase = "using" => \A r \in Live : m <= snapR[r]

\* What stripes need: every live snapshot is in the scanned list, so a
\* stripe ends at it, or at or above the sampled horizon, so it reads the
\* top stripe of inputs fixed before the sample. Lean: scan_respects_live.
LiveCovered == cphase = "using" => \A r \in Live : snapR[r] \in vals \/ c <= snapR[r]

\* A live snapshot's slot holds exactly its sequence.
LiveSlotExact == \A r \in Live : slot[r] = snapR[r]

====
