---- MODULE BatchMergeFold ----
\* Two atomic commits append operands. A snapshot between them must keep
\* its value. Folding [+1,+2] into one operand may save work, but reversing
\* their order, dropping a declined pair, or rewriting the previous commit
\* must fail. Values are sequences so order, not only sums, is observable.
\* Correspondence: Transaction::drain_for_commit settles one transaction;
\* write_buffer::fold_merges folds only that transaction's same-key operands;
\* commit publication and snapshot visibility remain CommitPipeline.tla.
\* Each operand also names its touched parts, as MergeOperator requires.
\* Correspondence (source lines at this change):
\* original: the unfolded reference stream, checked by transaction_merge_folding.rs.
\* stored, Commit: transaction.rs:2105, Transaction::drain_for_commit owns the drained writes.
\* Fold: transaction/write_buffer.rs:213, fold_merges; merge_call.rs:28 dispatches the callback.
\* INV_Reads: the callback's exactness law, proved for every surrounding list in BatchMergeFold.lean.
\* INV_Parts: options.rs:465, MergeOperator::touches; this is a caller contract, not a new check.
\* INV_Size: fold_merges checks both original operands and the combined encoding against the limit.
\* reads, Snapshot: existing CommitPipeline and SnapshotRegistry models; this change edits neither.
\* Cross-key, iterator and storage-source ordering remain the existing read/commit model boundaries.
EXTENDS Naturals, Sequences, FiniteSets
CONSTANT Bug, Limit
VARIABLES original, stored, reads
vars == <<original, stored, reads>> \* The reference commits, stored commits, and pinned reads.
Op(n) == [value |-> <<n>>, parts |-> {n}, bytes |-> 2] \* A tiny caller-supplied operand.
Batch == <<Op(1), Op(2)>> \* Every commit has two ordered writes of one key.
Join(a, b) == [value |-> a.value \o b.value,
              parts |-> IF Bug = "Parts" THEN a.parts ELSE a.parts \cup b.parts,
              bytes |-> 3] \* A combined encoding saves one byte, but might exceed Limit.
RECURSIVE Value(_)
Value(ops) == IF Len(ops) = 0 THEN <<>> ELSE Head(ops).value \o Value(Tail(ops)) \* Oldest first.
RECURSIVE Parts(_)
Parts(ops) == IF Len(ops) = 0 THEN {} ELSE Head(ops).parts \cup Parts(Tail(ops)) \* Touch union.
RECURSIVE Flatten(_)
Flatten(commits) == IF Len(commits) = 0 THEN <<>> ELSE Head(commits) \o Flatten(Tail(commits)) \* Visible prefix.
Fold(accepted) ==
    IF ~accepted THEN
        IF Bug = "Declined" THEN <<Batch[1]>> ELSE Batch \* A declined callback keeps both writes.
    ELSE IF Join(Batch[1], Batch[2]).bytes > Limit /\ Bug # "Size" THEN Batch \* Preserve valid inputs.
    ELSE IF Bug = "Order" THEN <<Join(Batch[2], Batch[1])>> \* The order mutant reverses writes.
    ELSE <<Join(Batch[1], Batch[2])>> \* The normal exact partial merge.
Init == /\ original = <<>> /\ stored = <<>> /\ reads = {} \* No commit or pinned snapshot yet.
Commit(accepted) ==
    /\ Len(original) < 2 \* Two commits expose an older snapshot boundary.
    /\ original' = Append(original, Batch) \* The reference never folds.
    /\ stored' = IF Bug = "Boundary" /\ Len(stored) = 1
                 THEN <<stored[1] \o Fold(accepted), <<>>>> \* The mutant rewrites the old commit.
                 ELSE Append(stored, Fold(accepted)) \* Only the new commit changes.
    /\ UNCHANGED reads \* Existing snapshots stay pinned.
Snapshot ==
    /\ reads' = reads \cup {Len(original)} \* Pin the current commit boundary.
    /\ UNCHANGED <<original, stored>> \* Registration changes no data.
Next == (\E accepted \in BOOLEAN : Commit(accepted)) \/ Snapshot \* Callback may accept or decline.
INV_Reads ==
    \A n \in reads \cup {Len(original)} :
        Value(Flatten(SubSeq(stored, 1, n))) =
        Value(Flatten(SubSeq(original, 1, n))) \* Latest and every pinned read agree.
INV_Parts ==
    \A n \in 1..Len(original) : Parts(stored[n]) = Parts(original[n]) \* No touched part disappears.
INV_Size ==
    \A n \in 1..Len(stored) : \A i \in 1..Len(stored[n]) :
        stored[n][i].bytes <= Limit \* Folding never makes a valid operand oversized.
Spec == Init /\ [][Next]_vars \* Publication is atomic; existing models cover its implementation.
====
