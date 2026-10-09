-------------------------- MODULE LegacyRangeRead --------------------------
EXTENDS Naturals, Sequences, TLC

\* Demotion keeps shallow point sources ahead of deeper ones. A legacy
\* ingest's widened tombstone can nevertheless be newer than a shallow
\* point, or an unflushed point replayed from the WAL. LsmOrder abstracts
\* range tombstones away; this model checks that missing part of E14.
CONSTANTS MaxSeq, PreScan
VARIABLES pointSeq, tombSeq, snap, checked
vars == <<pointSeq, tombSeq, snap, checked>>

Init == /\ pointSeq \in 1..MaxSeq
        /\ tombSeq \in 0..MaxSeq
        /\ tombSeq # pointSeq
        /\ snap \in 0..MaxSeq
        /\ checked = FALSE
Next == \/ /\ ~checked
           /\ checked' = TRUE
           /\ UNCHANGED <<pointSeq, tombSeq, snap>>
        \/ /\ checked
           /\ UNCHANGED vars

VisiblePoint == IF pointSeq <= snap THEN pointSeq ELSE 0
VisibleTomb == IF tombSeq <= snap THEN tombSeq ELSE 0

\* The first point is in the shallow source; the tombstone is in a
\* demoted deeper file that point-source order visits later. Without
\* the pre-scan, resolving the point returns before seeing the delete.
Read == IF PreScan /\ VisibleTomb >= VisiblePoint
        THEN 0 ELSE VisiblePoint
Reference == IF VisibleTomb >= VisiblePoint THEN 0 ELSE VisiblePoint
ReadNewest == ~checked \/ Read = Reference
Spec == Init /\ [][Next]_vars
=============================================================================
