-- The root of the Regolith proof library: importing it builds every module.
-- Each module's header names the TLA+ model and invariant it backs.

-- E1: the read order returns the newest visible version, and compacting a
-- closed L0 input set keeps that. Backs `proofs/tla/LsmOrder.tla`.
import Regolith.LsmOrder
-- E6: a batch read resolved against one view answers as of one point in
-- time. Backs `proofs/tla/BatchRead.tla`.
import Regolith.BatchView
-- E8: a visible sequence that never passes a pending slot gives repeatable
-- snapshots. Backs `proofs/tla/IngestPublication.tla`.
import Regolith.Publication
-- E2: syncing the sealed log before the next log takes a record makes
-- recovery a gap-free prefix. Backs `proofs/tla/WalRotation.tla`.
import Regolith.WalRecovery
-- Plan 3.6: commit-ordered append numbers appends densely from 1, once per
-- once key, in commit order, and a snapshot sees exactly rows 1..H. Backs
-- `proofs/tla/CommitOrderedAppend.tla` and `CommitOrderedAppendCrash.tla`.
import Regolith.Append
-- Plan 3.7: conflict-free allocation reserves ranges that never overlap,
-- only grow, and survive crashes. Backs `proofs/tla/Allocate.tla`.
import Regolith.Allocate
