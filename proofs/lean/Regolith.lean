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
-- 4.8, E5: reducing a key's versions per snapshot stripe, with an exact
-- partial_merge, changes no read at a live snapshot or at the head. Backs
-- `proofs/tla/StripeCompaction.tla`.
import Regolith.Stripes
-- 4.6: lock-free registration (announce, sample, confirm) keeps the
-- compaction's minimum at or below every live snapshot. Backs
-- `proofs/tla/SnapshotRegistry.tla`.
import Regolith.SnapshotRegistry
-- WalRecovery.lean also holds format 2 replay (4.2), backing
-- `proofs/tla/WalRecovery.tla`; LsmOrder.lean also holds flush order,
-- ingest placement, overlap demotion (E14) and binary search.
-- E10: a group commit decides every member as committing them one at a
-- time would. Backs `proofs/tla/GroupCommit.tla`.
import Regolith.GroupCommit
-- 4.7: deciding in ring order gives dense sequences in ring order, and a
-- reader at the published horizon sees exactly the published commits.
-- Backs `proofs/tla/CommitPipeline.tla`.
import Regolith.Pipeline
-- Plan 3.3: an exact partial_merge folds to full_merge in any grouping, and
-- the touches law. Backs `proofs/tla/RepeatableRead.tla`.
import Regolith.MergeOperator
-- Plan 3.1 to 3.15: every key class's commit rule accepts only histories
-- equal to the serial one in commit order, up to the class's relaxation.
-- Backs `proofs/tla/RepeatableRead.tla`.
import Regolith.Validation
-- Each key class's relaxation stated exactly, and the RED counterexamples.
-- Backs `proofs/tla/RepeatableRead.tla`.
import Regolith.Relaxations
-- regolith::sync's locks after D49: barging with a bypass bound gives
-- mutual exclusion, at most BOUND lost races per waiter, an exclusive owed
-- handoff and no stranded head. Backs `proofs/tla/Sync.tla` and the write
-- side of `SyncRwLock.tla`.
import Regolith.Sync
-- regolith::sync::Notify: the FIFO waiter queue with handoff before wake
-- gives FIFO service and no lost wakeup, cancellation included. Backs
-- `proofs/tla/SyncNotify.tla` and the waiter lists of `SyncLatch.tla` and
-- `SyncOnce.tla`.
import Regolith.SyncFifo
-- 3.16: every transaction callback runs exactly once, of its attempt's
-- outcome, in the stated order, and attempts are isolated. Backs
-- `proofs/tla/TxnCallbacks.tla`.
import Regolith.Callbacks
