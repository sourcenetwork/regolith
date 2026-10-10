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
-- 4.6: per-thread slots with counted entries (announce, sample, confirm;
-- copies join, releases go where the pin was recorded) keep the
-- compaction's minimum at or below every live snapshot and every count
-- exact. Backs `proofs/tla/SnapshotRegistry.tla`.
import Regolith.SnapshotRegistry
-- 4.6: per-thread statistics shards sum to every increment, and a read
-- concurrent with adds is bounded and never goes backwards. Backs
-- `proofs/tla/ShardedStats.tla`.
import Regolith.ShardedStats
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
-- E29, E30: the open accepts every crash state of the manifest, keeps every
-- synced batch, and replays no version above a newer table. Backs
-- `proofs/tla/ManifestRecovery.tla`.
import Regolith.ManifestRecovery
-- D48: an ingest that survives a crash keeps every commit ordered before it.
-- Backs `proofs/tla/IngestDurability.tla`.
import Regolith.IngestDurability
-- E27: retiring a tombstone no deeper run meets and no live snapshot is below
-- changes no snapshot's read. Backs `proofs/tla/TombstoneRetirement.tla`.
import Regolith.TombstoneRetirement
-- 4.10, D53: per-thread I/O queues. A unit is claimed by one CAS and runs
-- once, every registered queue is told exactly once and no other is, a
-- request sits on its own queue, an idle owner is woken and a busy one
-- never, and one thread finishes everything. Backs
-- `proofs/tla/NonBlocking.tla`.
import Regolith.IoQueue
-- 4.12, D45: a sealed manifest batch keeps its checksum, checked before any
-- key, so a torn batch and a wrong or missing key are never confused.
-- Backs `proofs/tla/ManifestSeal.tla`. (The sealed log stamp is in
-- WalRecovery.lean.)
import Regolith.ManifestSeal
-- 4.12, D57: a backup of an encrypted database seals its metadata; a
-- restore checks every key before its first write, copies exactly what the
-- tag covers and writes a sealed MANIFEST last. Backs
-- `proofs/tla/BackupSeal.tla`.
import Regolith.BackupSeal
-- 4.6, Phase 7b: the wait-free read view. A reader never holds a freed
-- view nor one older than what was published when its load began, and the
-- compare-and-swap publication loses no publication. Backs
-- `proofs/tla/ReadView.tla`.
import Regolith.ReadView
-- 4.6, Phase 7 integration: every publisher of the read view (a rotation, a
-- flush's install and retire on every flush path, a compaction, an ingest)
-- publishes by compare-and-swap, so no memtable or table is lost and no
-- retired memtable comes back. Backs `proofs/tla/ReadViewPublishers.tla`.
import Regolith.ReadViewPublishers
-- 4.6, Phase 7b: the lock-free CLOCK block cache. The hand evicts only a
-- block nobody holds and no landing names, counts stay exact, and the
-- two-level reservation keeps the byte bound. Backs
-- `proofs/tla/ClockCache.tla`.
import Regolith.ClockCache
-- 4.6, Phase 7b: a memtable's append-only range-tombstone log. Readers see
-- a whole prefix of the appends, including every one a snapshot they took
-- includes. Backs `proofs/tla/TombstoneLog.tla`.
import Regolith.TombstoneLog
-- 4.6, Phase 7c1: the open-file slot table under max_open_files. Never
-- more open files than slots, never a file closed under a reader, and a
-- read returns its own table. Backs `proofs/tla/OpenFileTable.tla`.
import Regolith.OpenFileTable
-- D60: a queue unit's reopen under max_open_files never waits for a slot,
-- and a parked one is never forgotten: its message is there, or a WANTED
-- busy slot or a wake on its way will bring it. The model and NeverWaits;
-- the invariant proof of RetryNeverLost; the four RED counterexamples.
-- Backs the D60 rows of `proofs/tla/OpenFileTable.tla`.
import Regolith.OpenFileNoWait
import Regolith.OpenFileNoWaitProof
import Regolith.OpenFileNoWaitRed
-- 4.6, Phase 7c1: column families created and dropped in the ordered step.
-- No write lands after its family's tombstone or before its birth, and a
-- family's life only moves forward. Backs `proofs/tla/CfRegistry.tla`.
import Regolith.CfRegistry
-- 4.6, Phase 7c1: the env file maps. A positional read gets its own
-- offset's bytes, and an in-memory read sees every append that finished
-- before it began. Backs `proofs/tla/EnvFiles.tla`.
import Regolith.EnvFiles
