

default:
    @just --list

# Everything CI enforces on every push, in the order it fails fastest.
gate: fmt lint doc test deny

fmt:
    cargo fmt --all -- --check

fmt-fix:
    cargo fmt --all

lint:
    cargo clippy --workspace --all-targets -- -D warnings

doc:
    RUSTDOCFLAGS="-D warnings" cargo doc --workspace --no-deps

# nextest, not `cargo test`: each test gets its own process, so a
# wedged test fails on the profile's slow-timeout instead of holding the
# whole binary. See `.config/nextest.toml`.

test:
    cargo nextest run --workspace
    cargo test --workspace --doc

deny:
    cargo deny check

msrv:
    cargo "+$(grep -m1 '^rust-version' Cargo.toml | cut -d'"' -f2)" check --workspace

# The summary line CI annotates a build with.
# Through nextest, like the gate: one process per test, so a wedged
# test fails on the profile's slow-timeout instead of holding the whole
# instrumented run open until the job's ceiling.
cov-summary:
    # The `ci` profile, not the default: instrumented code runs several
    # times slower, and the default profile's 60s slow-timeout turns the
    # heavier soaks into timeouts that say nothing about the code.
    cargo llvm-cov nextest --summary-only --workspace --profile ci --ignore-filename-regex '(^|/)tools/'

# The browsable HTML report, for reading locally.
cov:
    cargo llvm-cov --workspace --html --ignore-filename-regex '(^|/)tools/'
    @echo "report: target/llvm-cov/html/index.html"

# ── suites CI runs as their own jobs, split by mechanism ─────

test-fault:
    cargo test --test fault_smoke

# The `#[ignore]`d fault tests: each spawns child processes and simulates a
# power cut. Measured at well under a second each, but kept out of the
# default run so `cargo test` stays quick.

test-fault-slow:
    cargo nextest run --test fault_smoke

# The `#[ignore]`d resource-exhaustion and extremes tests: six-figure key
# counts, a 64 MiB value, megabyte keys, a six-level cascade, and a real
# ENOSPC on a tmpfs mounted in a private user namespace. About 21 s in
# total on a debug build. `--test-threads=1` is required, not cosmetic:
# each test resets the kernel's peak-RSS counter to report its own memory
# high-water mark, and a concurrent test would inflate that number.

test-crash:
    cargo test --test crash_recovery

# Handle lifecycle: open, close, reopen under changed Options, locking,
# and every misuse of a closed or read-only handle. Measured at 0.4s, so
# every test in the file also runs in the default `cargo test`; nothing
# here is `#[ignore]`d.

test-power:
    cargo test --test power_loss -- --skip crash_child --nocapture

# Process-crash recovery: kill -9 at every point in the write path. Every
# test in the file is in the default run already; this recipe just runs the
# file on its own. Measured at 0.6s, spawning 41 child processes.

test-corruption-slow:
    cargo nextest run --test corruption_exhaustive

# The power-loss durability tests, with output shown so the measured cost of
# the default DurabilityMode::Eventual is visible. Every test here spawns a
# child process, crashes it at a byte-exact point and simulates a power cut.
# Measured at 0.6s in total, so it also runs in the default `cargo test`.

test-durability-slow:
    cargo nextest run --test proptest_durability

# Every ignored test in the workspace, including the scheduled stress runs.

test-extremes:
    cargo nextest run --test resource_limits --no-capture --test-threads 1

# The `#[ignore]`d durability property test: 128 randomized operation
# sequences, each run in a child process that is killed part way through
# and then power-cut by discarding every byte it never fsynced. Measured
# at 1.1 s. Needs the LD_PRELOAD fault shim, so it is Linux only.

test-lifecycle:
    cargo test --test lifecycle -- --skip crash_child

# MVCC and concurrency invariants: snapshot stability under concurrent
# writers and compaction, WriteBatch atomicity seen by concurrent readers,
# monotonic reads, version integrity across delete/compact/reopen, and
# iterators pinned across compactions that unlink their files. Measured at
# 0.5s, so every test in the fast set also runs in the default `cargo test`.

test-slow:
    cargo nextest run --workspace --release --no-capture

# Rebuild the LD_PRELOAD fault shim from scratch by dropping its cache.

fault-shim-clean:
    rm -rf target/tmp/regolith-fault

# The `#[ignore]`d exhaustive corruption sweeps: every byte offset and
# every single-bit flip of a WAL, an SSTable and a MANIFEST. 14,265
# trials, measured at 1.2s of wall time.

mvcc:
    cargo test --test mvcc_invariants -- --skip crash_child

# The `#[ignore]`d full-scale MVCC soaks: 120,000 writes racing a snapshot
# that pins every version of them, 30,000 WriteBatch generations checked by
# four readers, 1.9M monotonic point reads, and the focused gate for the
# user-thread `compact_range` read race. Measured at 13.8s + 9.3s + 4.5s +
# 26s on a debug build.
#
# This recipe is RED today, and that is the point: the focused gate finds a
# real read-path defect. See the doc comment on
# `a_user_thread_compact_range_never_makes_a_read_travel_backwards`.

mvcc-slow:
    cargo nextest run --test mvcc_invariants --no-capture

set shell := ["bash", "-uc"]

gains_dir := justfile_directory() / "../regolithgains"

label     := env_var_or_default("LABEL", "wip")

py        := env_var_or_default("REGOLITHGAINS_PY", "python3")

# NOTE: the commit sha is resolved INSIDE the recipe, never as a top-level
# `sha := `git ...`` assignment. just evaluates those eagerly at parse time, so a
# top-level backtick makes every `just --list` fail outside a git checkout.

# ---------- the gate ----------

fuzz target time="300":
    cargo +nightly fuzz run {{target}} -- -max_total_time={{time}}

# ---------- benchmark gating ----------

# Exit 1 when the host is too busy to trust a measurement. A dependency, not advice.

loadguard:
    {{py}} {{gains_dir}}/loadguard.py

# ---------- benchmarks ----------

# Capture the reference baseline. Run ONCE, before any stack code lands.

bench-baseline: loadguard
    cargo bench --bench point_read --bench write_durable --bench write_buffered \
                --bench scan --bench batch --bench transaction \
                --bench large_value -- --save-baseline pre

# Compare against the `pre` baseline. This is what a PR pastes into its body.

bench: loadguard
    cargo bench -- --baseline pre

# The sweep the CI perf artifact is built from: every family, into the
# JSON Lines file `collect` assembles a run file out of.
bench-collect: loadguard
    cargo bench --bench point_read --bench write_durable --bench write_buffered \
                --bench scan --bench batch --bench transaction \
                --bench large_value --bench memory --bench size

bench-one name: loadguard
    cargo bench --bench {{name}} -- --baseline pre

# RSS soak. Default 360s; pass seconds and an Options variant tag.

soak secs="360" wb="64" cache="64" shard_bits="6" tag="default": loadguard
    cargo bench --bench soak -- {{secs}} {{wb}} {{cache}} {{shard_bits}} {{tag}}

# The two soak variants compared. Deterministic: no loadguard needed.

soak-pair:
    just soak 360 64 64 6 default
    just soak 360 64 64 0 cache-budgeted

# Binary size, native and both wasm targets, against the budget.

size:
    cargo bench --bench size

# The memory table in the README: every profile, on both hosts, one
# workload. The wasm column is the reproducible one because linear
# memory only ever grows; RSS moves between runs.

wasm-budget puts="20000":
    #!/usr/bin/env bash
    set -euo pipefail
    cargo build --release --example embedded_profile --target wasm32-wasip1
    for profile in embedded wasm default; do
        echo "== $profile, x86_64 Linux =="
        d=$(mktemp -d)
        cargo run --release --quiet --example embedded_profile -- "$d" "$profile" {{puts}}
        rm -rf "$d"
        echo "== $profile, wasm32-wasip1 under wasmtime =="
        d=$(mktemp -d)
        wasmtime run --dir="$d::/data" \
            target/wasm32-wasip1/release/examples/embedded_profile.wasm \
            /data "$profile" {{puts}}
        rm -rf "$d"
    done

# Point memory probes.

mem:
    cargo bench --bench memory

# The MVCC regression probes. Must stay at zero violations.

ycsb workload="a" records="1000000" ops="1000000": loadguard
    cargo run --release -p regolith-ycsb -- \
        --workload {{workload}} --records {{records}} --operations {{ops}}

ycsb-all: loadguard
    for w in a b c d e f; do just ycsb $w; done

stress secs="600":
    cargo run --release -p regolith-stress -- --duration {{secs}}

# ---------- model checking ----------

# Loom model checks for the arena memtable, read horizon and version
# handoffs. `--cfg loom` swaps the primitives in `src/engine/sync.rs`
# for loom's instrumented ones; without it the whole target compiles
# away, so an ordinary `cargo test` neither builds loom nor runs these.
#
# | recipe        | models | profile | measured |
# |---------------|--------|---------|----------|
# | `loom`        | 16     | release | 21.6s    |
# | `loom-debug`  | 17     | debug   | 16.0s    |
# | `loom-all`    | both   | both    | ~38s     |
#
# Re-measured on a host at load average 105-140 on 36 threads (a shared,
# heavily loaded machine), so these are not comparable to a quiet-host
# baseline; they are the wall time `cargo test`'s own summary line
# reported for the test binary, excluding compilation.
#
# The debug run carries one extra calibration: the skip list's
# single-writer guard (S2) is a `debug_assert`, so the model proving it
# fires is compiled out of a release build. The arena's single-writer
# guard (A8) is debug-only the same way, but its own calibration runs in
# both profiles with a different expected panic message per profile (a
# debug build trips the guard, a release build trips loom's tracked
# cell), so it does not add to the debug-only gap the way S2's does.
# Seven of the models are `should_panic` calibrations that deliberately
# get the ordering wrong; they are what make the passes mean anything.

loom:
    RUSTFLAGS="--cfg loom" cargo test --release --test loom_memtable

loom-debug:
    RUSTFLAGS="--cfg loom" cargo test --test loom_memtable

loom-all: loom loom-debug

# The read-view chaos workload at full size: 6 instances x 2 rounds x 400
# versions. Measured at over 20 minutes wall and 4h of CPU unoptimized,
# which is why `cargo test` runs a smaller default and this recipe
# carries the full one. Release, because debug is where the cost is.
#
# Sized to finish, not to be maximal. Cost is roughly
# instances x rounds x versions x compaction passes, and the compaction
# passes each rewrite a database that grows with the version count, so
# raising `versions` raises the run time faster than linearly: 400 does
# not complete inside seven minutes, 120 completes in seconds. What the
# workload is hunting is overlap between a compaction and a read, and
# the overlap count is already in the thousands per instance here.

chaos instances="4" rounds="2" versions="120" min_rounds="20":
    REGOLITH_CHAOS_INSTANCES={{instances}} REGOLITH_CHAOS_ROUNDS={{rounds}} \
    REGOLITH_CHAOS_VERSIONS={{versions}} REGOLITH_CHAOS_MIN_ROUNDS={{min_rounds}} \
        cargo test --release --test read_view_chaos_workload -- --nocapture

# TLA+ model of what commit validation covers at each isolation level,
# checked against the Merkle-DAG CRDT workload `RepeatableRead` exists for: appends to a
# Merkle DAG whose head set is derived from keys, the sweep that reclaims
# it, and a write derived from a definition read; and against DefraLevel's
# relaxations: merges into a counter, scans that stay inside or leave a
# commutative prefix, and content-addressed keys.
# `proofs/tla/RepeatableRead.tla` carries the model; each configuration below
# runs with the verdict it must produce, and a RED row names the invariant it
# must break. A GREEN model that reports an error, or a
# RED one that does not break exactly its invariant, fails the recipe: the RED
# rows are what make the GREEN ones mean anything, and a RED row that fails
# for some other reason shows nothing.
# The storage-engine models follow, each backed by a Lean proof in
# `proofs/lean` that holds for every size where TLC checks a few:
# `LsmOrder.tla` (E1, compact_range picks a closed L0 input set),
# `BatchRead.tla` (E6, one view per batch read), `IngestPublication.tla`
# (E8, the visible sequence never passes a pending slot) and
# `WalRotation.tla` (E2, a rotation syncs the sealed log first).
# Each row prints the distinct states TLC explored and its wall time.
# TLC is fetched on first use, pinned by checksum in `proofs/tla/tools/tlc`.
tla:
    #!/usr/bin/env bash
    set -uo pipefail
    cd proofs/tla
    fail=0
    # The module the next rows check; each block below sets it.
    spec=RepeatableRead
    check() {
        local cfg="$1" expect="$2" inv="${3:-}" out broke verdict states took
        out=$(./tools/tlc -metadir "states/$cfg" -config "$cfg.cfg" "$spec.tla" 2>&1)
        # TLC words a broken invariant two ways: "is violated." when the search reaches a bad
        # state, and "is violated by the initial state:" when the very first state is already
        # bad. Both name the invariant, and both count.
        broke=$(sed -n -e 's/^Error: Invariant \(.*\) is violated\.$/\1/p' \
                       -e 's/^Error: Invariant \(.*\) is violated by the initial state:$/\1/p' <<<"$out" | head -1)
        states=$(sed -n 's/^.* states generated, \([0-9,]*\) distinct states found.*$/\1/p' <<<"$out" | tail -1)
        took=$(sed -n 's/^Finished in \(.*\) at (.*$/\1/p' <<<"$out" | tail -1)
        if grep -q "No error has been found" <<<"$out"; then
            verdict=GREEN
        elif [ -n "$broke" ] && [ "$broke" = "$inv" ]; then
            verdict=RED
        elif [ -n "$broke" ]; then
            verdict="RED on $broke"
        else
            verdict=BROKEN
            echo "$out" | tail -20
        fi
        printf '  %-48s %-6s %9s states %8s  (expected %s)\n' \
            "$cfg" "$verdict" "${states:-?}" "${took:-?}" "$expect${inv:+ on $inv}"
        if [ "$verdict" != "$expect" ]; then fail=1; fi
    }
    check MC_RepeatableRead_Green                      GREEN
    check MC_RepeatableRead_Red_Serializable           RED INV_AppendsCommit
    check MC_RepeatableRead_Red_SnapshotIsolation      RED INV_NoStaleDefinition
    check MC_RepeatableRead_Red_ReadCommitted          RED INV_NoStaleDefinition
    check MC_DefraLevel_Green_Heads                    GREEN
    check MC_DefraLevel_Green_Counters                 GREEN
    check MC_DefraLevel_Green_Migrations               GREEN
    check MC_DefraLevel_Red_RepeatableRead_Merges      RED INV_DuplicateMergesCommit
    check MC_DefraLevel_Red_NoPolicy                   RED INV_DuplicateMergesCommit
    check MC_DefraLevel_Red_BlocksOrdinary             RED INV_DuplicateMergesCommit
    check MC_DefraLevel_Red_RepeatableRead_Counters    RED INV_IncrementsCommitUnlessReplaced
    check MC_DefraLevel_Red_ReadMergeBlind             RED INV_ReceiptsExact
    check MC_DefraLevel_Red_PutMergeBlind              RED INV_CounterExact
    check MC_DefraLevel_Red_PutMergeElides             RED INV_CounterExact
    check MC_DefraLevel_Red_MergeIgnoresReplacement    RED INV_CounterExact
    check MC_DefraLevel_Red_RangeDeleteNotReplacement  RED INV_CounterExact
    check MC_DefraLevel_Red_PolicyIgnoresRange         RED INV_NoStaleDefinition
    check MC_DefraLevel_Red_DefinitionContentAddressed RED INV_NoStaleDefinition
    # DefraLevel's key classes and mechanisms (plan 3.1 to 3.15). Lean:
    # Regolith/Validation.lean, all_classes_serial; Regolith/Relaxations.lean;
    # Regolith/MergeOperator.lean.
    check MC_DefraLevel_Green_ContentAddressed         GREEN
    check MC_DefraLevel_Red_CaDeleteExempt             RED INV_NoDanglingReference
    check MC_DefraLevel_Red_PresenceReadFull           RED INV_LinksCommit
    check MC_DefraLevel_Red_PresenceUnchecked          RED INV_HoldsCurrent
    check MC_DefraLevel_Green_Parts                    GREEN
    check MC_DefraLevel_Red_PartsIgnorePut             RED INV_PartsCurrent
    check MC_DefraLevel_Red_PartsIgnoreTouch           RED INV_PartsCurrent
    check MC_DefraLevel_Red_PartsNoAbsentFallback      RED INV_PartsCurrent
    check MC_DefraLevel_Red_PartsNoPutFallback         RED INV_PartsCurrent
    check MC_DefraLevel_Red_PartsNamesOther            RED INV_PartsCurrent
    check MC_DefraLevel_Red_Parts_RepeatableRead       RED INV_PartsRelaxed
    check MC_DefraLevel_Green_ValueReads               GREEN
    check MC_DefraLevel_Red_SeqOnlyValidation          RED INV_IdenticalRewritesCommit
    check MC_DefraLevel_Green_WriteFree                GREEN
    check MC_DefraLevel_Red_WriteFreePessimistic       RED INV_WriteFreeConsistent
    check MC_DefraLevel_Green_Log                      GREEN
    check MC_DefraLevel_Red_OwnAppendVisible           RED INV_NoPhantomAppend
    check MC_DefraLevel_Red_DecideOnLogRead            RED INV_LogDecisionsCurrent
    check MC_DefraLevel_Green_MergeBeforeScan          GREEN
    check MC_DefraLevel_Red_MergeBeforeScanReadsBase   RED INV_TallyMergesCommit
    check MC_DefraLevel_Green_OwnWrites                GREEN
    check MC_DefraLevel_Red_PutsBeforeMerges           RED INV_ReadYourOwnWrites
    check MC_DefraLevel_Red_OwnMergesInvisible         RED INV_ReadYourOwnWrites
    check MC_DefraLevel_Green_ValidatedScan            GREEN
    check MC_DefraLevel_Red_PlainScanDecides           RED INV_ScanDecisionsCurrent
    check MC_DefraLevel_Red_ReasonNewestWrite          RED INV_ReasonsExact
    # E1. Lean: Regolith/LsmOrder.lean, compact_range_reads_newest.
    spec=LsmOrder
    check MC_LsmOrder_Green                            GREEN
    check MC_LsmOrder_Red_Intersect                    RED ReadNewest
    # Flush order, ingest placement, overlap demotion (E14, D13), binary
    # search. Lean: Regolith/LsmOrder.lean, install_oldest_same_order,
    # ingest_ordered, demote_reads_newest, level_read_bsearch.
    check MC_LsmOrder_Green_Flush                      GREEN
    check MC_LsmOrder_Red_FlushAnyOrder                RED ReadNewest
    check MC_LsmOrder_Green_Ingest                     GREEN
    check MC_LsmOrder_Red_IngestIgnoresUpper           RED ReadNewest
    check MC_LsmOrder_Green_Demote                     GREEN
    check MC_LsmOrder_Red_DemoteLevelOnly              RED ReadNewest
    check MC_LsmOrder_Red_NoDemotion                   RED ReadNewest
    # E6. Lean: Regolith/BatchView.lean, batch_one_view_newest.
    spec=BatchRead
    check MC_BatchRead_Green                           GREEN
    check MC_BatchRead_Red_ViewPerKey                  RED BatchConsistent
    check MC_BatchRead_Red_ViewPerKey_Exact            RED BatchExact
    # E8. Lean: Regolith/Publication.lean, repeatable_snapshot.
    spec=IngestPublication
    check MC_IngestPublication_Green                   GREEN
    check MC_IngestPublication_Red_CommitPassesSlot    RED RepeatableSnapshot
    check MC_IngestPublication_Red_IngestPublishesEarly RED RepeatableSnapshot
    # E2. Lean: Regolith/WalRecovery.lean, reachable_recovers_prefix.
    spec=WalRotation
    check MC_WalRotation_Green                         GREEN
    check MC_WalRotation_Red_NoSync                    RED RecoversPrefix
    check MC_WalRotation_Red_NoSync_Gap                RED NoGap
    # Plan 3.6, commit-ordered append (supersedes defradb.rs #1911). Each
    # Teeth row is GREEN: its mutant breaks nothing but its RED's invariant.
    # Lean: Regolith/Append.lean, dense_from_one, unique_positions,
    # at_most_once, commit_order, snapshot_sees_prefix.
    spec=CommitOrderedAppend
    check MC_CommitOrderedAppend_Green_Writers                 GREEN
    check MC_CommitOrderedAppend_Green_Groups                  GREEN
    check MC_CommitOrderedAppend_Green_Faults                  GREEN
    check MC_CommitOrderedAppend_Green_Pipeline                GREEN
    check MC_CommitOrderedAppend_Red_Counter                   RED INV_NoDisjointConflict
    check MC_CommitOrderedAppend_Red_Detached                  RED INV_OneCommitPerWrite
    check MC_CommitOrderedAppend_Red_DetachedOrder             RED INV_CommitOrder
    check MC_CommitOrderedAppend_Red_DetachedNumbering         RED INV_NumberedAtCommit
    check MC_CommitOrderedAppend_Red_LatestBound               RED INV_NoSkip
    check MC_CommitOrderedAppend_Red_Stamps                    RED INV_Dense
    check MC_CommitOrderedAppend_Red_ViewOnlyHead              RED INV_UniqueCursors
    check MC_CommitOrderedAppend_Red_OnceFromView              RED INV_AtMostOnce
    check MC_CommitOrderedAppend_Red_AssignBeforeValidation    RED INV_Dense
    check MC_CommitOrderedAppend_Red_HeadCache                 RED INV_Dense
    check MC_CommitOrderedAppend_Red_PublishedView             RED INV_UniqueCursors
    check MC_CommitOrderedAppend_Teeth_Counter                 GREEN
    check MC_CommitOrderedAppend_Teeth_Detached                GREEN
    check MC_CommitOrderedAppend_Teeth_LatestBound             GREEN
    check MC_CommitOrderedAppend_Teeth_Stamps                  GREEN
    check MC_CommitOrderedAppend_Teeth_ViewOnlyHead            GREEN
    check MC_CommitOrderedAppend_Teeth_OnceFromView            GREEN
    check MC_CommitOrderedAppend_Teeth_AssignBeforeValidation  GREEN
    check MC_CommitOrderedAppend_Teeth_HeadCache               GREEN
    check MC_CommitOrderedAppend_Teeth_PublishedView           GREEN
    # Plan 3.6 across crashes, per durability mode. Green_Eventual is also
    # the RED's teeth. Lean: Regolith/Append.lean, snapshot_sees_prefix;
    # Regolith/WalRecovery.lean, recovers_prefix.
    spec=CommitOrderedAppendCrash
    check MC_CommitOrderedAppendCrash_Green_Immediate          GREEN
    check MC_CommitOrderedAppendCrash_Green_Eventual           GREEN
    check MC_CommitOrderedAppendCrash_Red_EventualExternal     RED INV_ExternalStable
    # Plan 3.7, conflict-free allocation. Lean: Regolith/Allocate.lean,
    # ranges_disjoint, ranges_grow, uses_allocated, alloc_fresh.
    spec=Allocate
    check MC_Allocate_Green_Immediate                          GREEN
    check MC_Allocate_Green_Eventual                           GREEN
    check MC_Allocate_Red_InTxn                                RED INV_NeverConflicts
    check MC_Allocate_Red_LogAfterUse                          RED INV_UseDurable
    check MC_Allocate_Red_LogAfterUse_Reuse                    RED INV_UsesUnique
    check MC_Allocate_Teeth_InTxn                              GREEN
    check MC_Allocate_Teeth_LogAfterUse                        GREEN
    # 4.2, E3: WAL format 2 replay. Lean: Regolith/WalRecovery.lean,
    # recovers_prefix2.
    spec=WalRecovery
    check MC_WalRecovery_Green_Immediate               GREEN
    check MC_WalRecovery_Green_Eventual                GREEN
    check MC_WalRecovery_Green_Residual                GREEN
    check MC_WalRecovery_Green_Aead                    GREEN
    check MC_WalRecovery_Red_DropBelowP                RED NoProvenLoss
    check MC_WalRecovery_Red_RefuseAboveP              RED RecoveryOpens
    check MC_WalRecovery_Red_Format1                   RED RecoveryOpens
    check MC_WalRecovery_Red_CloseWithoutSync          RED RecoveryOpens
    check MC_WalRecovery_Red_NoTruncate                RED RecoveryOpens
    check MC_WalRecovery_Red_StampNotSealed            RED AckedSurvive
    # 4.8, E5: compaction per snapshot stripe. Lean: Regolith/Stripes.lean,
    # reduce_reads.
    spec=StripeCompaction
    check MC_StripeCompaction_Green                    GREEN
    check MC_StripeCompaction_Green_Filter             GREEN
    check MC_StripeCompaction_Green_Inexact            GREEN
    check MC_StripeCompaction_Red_CaptureEarly         RED SnapshotReadsKept
    check MC_StripeCompaction_Red_InexactFold          RED HeadKept
    check MC_StripeCompaction_Red_IgnoreStripes        RED SnapshotReadsKept
    # 4.6: the lock-free snapshot registry. Lean:
    # Regolith/SnapshotRegistry.lean, scan_respects_live.
    spec=SnapshotRegistry
    check MC_SnapshotRegistry_Green                    GREEN
    check MC_SnapshotRegistry_Red_NoConfirm            RED MinBelowLive
    check MC_SnapshotRegistry_Red_ScanThenSample       RED MinBelowLive
    # E10, group commit. Lean: Regolith/GroupCommit.lean, group_eq_serial.
    spec=GroupCommit
    check MC_GroupCommit_Green                         GREEN
    check MC_GroupCommit_Red_ViewOnly                  RED SerialEquivalent
    check MC_GroupCommit_Red_PublishBeforeSync         RED DurableBeforeVisible
    # 4.7, the lock-free commit pipeline. Lean: Regolith/Pipeline.lean,
    # seqs_dense and reader_sees_published.
    spec=CommitPipeline
    check MC_CommitPipeline_Green                      GREEN
    check MC_CommitPipeline_Red_OutOfOrder             RED ReadersSeePrefix
    check MC_CommitPipeline_Red_AbortHole              RED NoHole
    check MC_CommitPipeline_Red_NoHelping              RED NoLiveThreadBlocked
    check MC_CommitPipeline_Red_SyncPastGap            RED DurableImpliesWritten
    check MC_CommitPipeline_Red_ValidatePublished      RED NoLostUpdate
    # R13, non-blocking calls: tickets, poll_io, io_pending, CacheOnly reads.
    # TLC only; wakeups are interleavings with no law over sizes to prove.
    spec=NonBlocking
    check MC_NonBlocking_Green_Pool                    GREEN
    check MC_NonBlocking_Green_Single                  GREEN
    check MC_NonBlocking_Red_LostWakeup                RED NoLostWakeup
    check MC_NonBlocking_Red_SilentSelfIo              RED IoPendingFires
    # regolith::sync's locks after D49: barging with bounded bypass, for
    # Mutex, Semaphore and ReentrantMutex. Lean: Regolith/Sync.lean,
    # mutual_exclusion, bounded_bypass, owed_exclusive.
    spec=Sync
    check MC_Sync_Green_Mutex                          GREEN
    check MC_Sync_Green_Semaphore                      GREEN
    check MC_Sync_Green_Reentrant                      GREEN
    check MC_Sync_Green_ReentrantLive                  GREEN
    check MC_Sync_Red_UnboundedBarging                 RED BoundedBypass
    check MC_Sync_Red_ReleaseNoWake                    RED NoLostWakeup
    check MC_Sync_Red_LoseQueuePosition                RED BoundedBypass
    check MC_Sync_Red_CancelNoPassOn                   RED CancelPassesOn
    check MC_Sync_Red_NoRecheck                        RED NoLostWakeup
    check MC_Sync_Red_IgnoreOwed                       RED HandoffExclusive
    check MC_Sync_Red_NoDepth                          RED ReentrancyDepth
    # regolith::sync::Notify, which keeps FIFO handoff. Lean:
    # Regolith/SyncFifo.lean, fifo_served, no_stranded_waiter.
    spec=SyncNotify
    check MC_SyncNotify_Green                          GREEN
    check MC_SyncNotify_Red_WakeBeforeHandoff          RED NoLostWakeup
    check MC_SyncNotify_Red_CancelNoPassOn             RED CancelPassesOn
    check MC_SyncNotify_Red_NoRecheck                  RED NoLostWakeup
    check MC_SyncNotify_Red_NoGenCheck                 RED NoLostWakeup
    # regolith::sync::RwLock and ReentrantRwLock after D49, with D50's
    # upgradable read.
    spec=SyncRwLock
    check MC_SyncRwLock_Green_Plain                    GREEN
    check MC_SyncRwLock_Green_WriterLive               GREEN
    check MC_SyncRwLock_Green_ReaderLive               GREEN
    check MC_SyncRwLock_Green_Reentrant                GREEN
    check MC_SyncRwLock_Green_ReentrantLive            GREEN
    check MC_SyncRwLock_Red_UnboundedBarging           RED BoundedBypass
    check MC_SyncRwLock_Red_AnyReaderUpgrade           RED NoUpgradeDeadlock
    check MC_SyncRwLock_Red_UpgradeNoHoldBack          RED UpgradeHoldsBack
    check MC_SyncRwLock_Red_OwnerUnaware               RED NoSelfDeadlock
    # regolith::sync::Event, Latch and Barrier.
    spec=SyncLatch
    check MC_SyncLatch_Green_Event                     GREEN
    check MC_SyncLatch_Green_Latch                     GREEN
    check MC_SyncLatch_Green_Barrier                   GREEN
    check MC_SyncLatch_Red_NoRecheck                   RED NoLostWakeup
    check MC_SyncLatch_Red_CountCheck                  RED NoLostWakeup
    # regolith::sync::OnceCell and Lazy: exactly one value is published.
    spec=SyncOnce
    check MC_SyncOnce_Green                            GREEN
    check MC_SyncOnce_Red_CancelNoReset                RED NoLostWakeup
    check MC_SyncOnce_Red_PlainStore                   RED PublishedOnce
    check MC_SyncOnce_Red_NoRecheck                    RED NoLostWakeup
    check MC_SyncOnce_Red_ReparkStale                  RED NoLostWakeup
    # Transaction callbacks (3.16). Lean: Regolith/Callbacks.lean,
    # exactly_once, order, attempts_isolated.
    spec=TxnCallbacks
    check MC_TxnCallbacks_Green_Immediate              GREEN
    check MC_TxnCallbacks_Green_Eventual               GREEN
    check MC_TxnCallbacks_Red_CommitBeforeDurable      RED CommitAfterDurable
    check MC_TxnCallbacks_Red_SkipCallbackWrites       RED NoLostUpdate
    check MC_TxnCallbacks_Red_CallbacksSurvive         RED AttemptIsolation
    check MC_TxnCallbacks_Red_HelperNoClaim            RED AtMostOnce
    check MC_TxnCallbacks_Red_CloseNoClaim             RED AtMostOnce
    rm -rf states ./*_TTrace_*.tla ./*_TTrace_*.bin
    exit $fail

# `proofs/lean` is a Lake project named Regolith, plain Lean 4 core with no
# dependencies, so it builds offline. Each module proves for every size what
# a TLA+ model above checks for a few, and names that model in its header.
# The build treats every warning as an error, so a proof left open fails it;
# the grep refuses the placeholder words outright; and `Audit.lean` fails
# unless every Regolith declaration rests on Lean's three standard
# assumptions alone. elan provides the toolchain `lean-toolchain` pins.
# Build and audit the Lean proofs in proofs/lean.
lean:
    #!/usr/bin/env bash
    set -euo pipefail
    export PATH="$HOME/.elan/bin:$PATH"
    cd proofs/lean
    lake build
    if grep -rnwE --include='*.lean' --exclude-dir=.lake 'sorry|admit|axiom' .; then
        echo "error: proofs/lean holds sorry, admit or axiom; every proof must be complete" >&2
        exit 1
    fi
    lake env lean Audit.lean

# Every formal check: the TLA+ models and the Lean proofs.
proofs: tla lean

# ---------- consistency ----------

# Where the Elle recipes write histories and scratch databases, and which
# elle-cli jar they run. Both are absolute paths. The output goes under the
# harness's gitignored target/ rather than /tmp, which can be full or absent;
# set ELLE_OUT to move it. The jar defaults to where CI downloads it; set
# ELLE_CLI to run one kept elsewhere.
elle_out := env_var_or_default("ELLE_OUT", justfile_directory() / "harness/elle/target/elle-out")
elle_cli := env_var_or_default("ELLE_CLI", justfile_directory() / "harness/elle/elle-cli.jar")

# Elle consistency checking. `model` is the workload (list-append or
# rw-register); `level` is the consistency model to check it against.
#
# The two are separate axes and elle-cli spells both `--model`-ish, which
# is easy to get wrong: passing an isolation level as --model throws
# "No matching clause". Hence the explicit --consistency-models here.
elle model="list-append" level="snapshot-isolation" isolation="snapshot-isolation":
    mkdir -p "{{elle_out}}"
    cargo run --release --manifest-path harness/elle/Cargo.toml --bin elle-gen -- \
        --model {{model}} --isolation {{isolation}} \
        --threads 8 --txns 50 --keys 4 \
        --out "{{elle_out}}/regolith-history.json" --dir "{{elle_out}}/regolith-elle-db"
    java -jar "{{elle_cli}}" --model {{model}} --cycle-search-timeout 60000 \
        --consistency-models {{level}} "{{elle_out}}/regolith-history.json"

# The same, with the fault injection the harness supports.
elle-fault model="list-append" level="snapshot-isolation":
    mkdir -p "{{elle_out}}"
    cargo run --release --manifest-path harness/elle/Cargo.toml --bin elle-gen -- \
        --model {{model}} --isolation snapshot-isolation --faults all \
        --threads 8 --txns 50 --keys 4 \
        --out "{{elle_out}}/regolith-history-fault.json" --dir "{{elle_out}}/regolith-elle-fault-db"
    java -jar "{{elle_cli}}" --model {{model}} --cycle-search-timeout 60000 \
        --consistency-models {{level}} "{{elle_out}}/regolith-history-fault.json"

# Every level regolith claims, checked in one go.
#
# Each line prints elle-cli's verdict and whether elle-gen's built-in check
# passed; anything other than `true` with a passing built-in check fails the
# recipe. `:unknown` means elle-cli gave up a cycle search, so the per-SCC
# timeout below is raised to keep a slow runner from reporting a valid
# history as `:unknown`.
elle-matrix:
    #!/usr/bin/env bash
    set -uo pipefail
    out="{{elle_out}}"
    mkdir -p "$out"
    cd harness/elle
    fail=0
    cargo build --release --bin elle-gen
    cargo test --release || fail=1
    check() {
        local name="$1" model="$2" level="$3"; shift 3
        local built_in=pass
        if ! ./target/release/elle-gen --model "$model" "$@" \
            --out "$out/elle-$name.json" --dir "$out/elle-db-$name" >/dev/null; then
            built_in=fail
            fail=1
        fi
        # elle-cli prints "<path>\t<true|false|:unknown>"; take the last
        # field and strip surrounding whitespace, so a stray tab cannot read
        # as a failure on a history that actually passed.
        local v
        v=$(java -jar "{{elle_cli}}" --model "$model" --cycle-search-timeout 60000 \
            --consistency-models "$level" "$out/elle-$name.json" \
            | tail -1 | awk '{print $NF}')
        printf '  %-42s %s (built-in check: %s)\n' "$name [$level]" "$v" "$built_in"
        if [ "$v" != "true" ]; then fail=1; fi
    }
    # Optimistic transactions at snapshot isolation, checked at snapshot
    # isolation: a false here is a defect.
    check optimistic-si       list-append snapshot-isolation --isolation snapshot-isolation --threads 8 --txns 50 --keys 4 --seed 4
    check optimistic-rw       rw-register snapshot-isolation --isolation snapshot-isolation --threads 8 --txns 50 --keys 4 --seed 5
    # Pessimistic transactions are checked at the level they request: these
    # rows run regolith's ReadCommitted level. Their plans include a read-only
    # get_for_update, the one read that level leaves unvalidated and
    # SnapshotIsolation validates.
    check pessimistic-rc      list-append read-committed     --isolation read-committed --threads 8 --txns 50 --keys 4 --seed 2
    check pessimistic-hotkey  list-append read-committed     --isolation read-committed --threads 8 --txns 50 --keys 1 --seed 1
    # Serializable validates the whole read set, so the strongest model
    # Elle offers must hold.
    check serializable        list-append strict-serializable --isolation serializable --threads 8 --txns 60 --keys 4 --seed 11
    check serializable-rw     rw-register strict-serializable --isolation serializable --threads 8 --txns 60 --keys 4 --seed 12
    # RepeatableRead validates every point read: Adya's PL-2.99, which is
    # what Elle's repeatable-read model checks. These workloads read through
    # `get` only, so the same histories also hold the strongest model.
    check repeatable-read     list-append repeatable-read    --isolation repeatable-read --threads 8 --txns 60 --keys 4 --seed 13
    check repeatable-read-rw  rw-register repeatable-read    --isolation repeatable-read --threads 8 --txns 60 --keys 4 --seed 14
    check repeatable-read-ss  list-append strict-serializable --isolation repeatable-read --threads 8 --txns 60 --keys 4 --seed 15
    # DefraLevel without a classifier validates point reads as RepeatableRead
    # and lets blind merges to one key all commit; the TLA+ model (proofs/tla,
    # MC_DefraLevel_*) proves those relaxations. list-append appends the
    # transaction has not read are merge operands, applied in commit order, so
    # a point workload is serializable in commit order and the strongest model
    # must hold. There is no snapshot-isolation row: two blind merges to one
    # key both commit, which first-committer-wins forbids.
    check defra-level         list-append strict-serializable --isolation defra-level --threads 8 --txns 60 --keys 4 --seed 16
    check defra-level-rw      rw-register strict-serializable --isolation defra-level --threads 8 --txns 60 --keys 4 --seed 17
    exit $fail

# ---------- portability ----------

# Full wasm32-wasip1 lifecycle under wasmtime. Non-zero on the first wrong byte.

wasm records="5000" sustained="20000":
    #!/usr/bin/env bash
    set -euo pipefail
    # open, put, get, delete, batch, scan, snapshot, iterate, compact,
    # close, REOPEN, read back - then `--sustained` writes past the L0
    # stop trigger with a 32 KiB memtable and no explicit compaction,
    # which is the case that wedges when nothing compacts on the
    # calling thread.
    cargo build --release -p regolith-wasm-probe --target wasm32-wasip1
    # Both shipped profiles a wasm module can open with, on the real
    # target: `embedded` runs with no block cache, `wasm` with one.
    for profile in embedded wasm; do
        echo "== profile $profile =="
        d=$(mktemp -d)
        wasmtime run --dir="$d::/data" \
            target/wasm32-wasip1/release/regolith-wasm-probe.wasm -- \
            --profile "$profile" --records {{records}} --sustained {{sustained}} \
            --probe-host --report-memory
        rm -rf "$d"
    done

# The same lifecycle natively, to tell a regolith bug apart from a wasm one.

wasm-native records="5000" sustained="20000":
    #!/usr/bin/env bash
    set -euo pipefail
    for profile in embedded wasm; do
        echo "== profile $profile =="
        cargo run --release -p regolith-wasm-probe -- \
            --profile "$profile" --records {{records}} --sustained {{sustained}} \
            --probe-host --report-memory
    done

# The OPFS contract against a real browser. `wasm-pack test` cannot
# drive these: it appends `--tests`, which builds every target in
# `tests/`, and all but the three `wasm_opfs*` files are native-only.
# The runner is named per target instead, so only the named test
# binaries are built.
wasm-browser:
    #!/usr/bin/env bash
    set -euo pipefail
    export CARGO_TARGET_WASM32_UNKNOWN_UNKNOWN_RUNNER=wasm-bindgen-test-runner
    # wasm-bindgen's default per-test budget is 20s, which a headless
    # browser on a shared runner can exceed on a test that mounts OPFS
    # and writes through real sync access handles. Exceeding it kills
    # the whole driver, so nine passing tests report as one failure with
    # no attribution.
    export WASM_BINDGEN_TEST_TIMEOUT=180
    for suite in wasm_opfs wasm_opfs_main wasm_opfs_memory; do
        echo "== $suite =="
        cargo test --target wasm32-unknown-unknown --test "$suite"
    done

embedded:
    cargo bench --bench memory -- --profile embedded

# ---------- the gains figures ----------

# Collect every family into ONE run file and re-render. A PR runs this, then pastes.

gains: loadguard
    #!/usr/bin/env bash
    set -euo pipefail
    sha=$(git rev-parse --short HEAD)
    cargo bench -- --baseline pre --save-baseline "$sha"
    cargo bench --bench collect -- \
        --out {{gains_dir}}/runs/"$sha"-{{label}}.json \
        --commit "$sha" --label {{label}}
    just gains-render

gains-render:
    {{py}} {{gains_dir}}/render.py
    {{py}} {{gains_dir}}/render_rss.py

gains-diff base current:
    {{py}} {{gains_dir}}/render.py --baseline {{base}} --current {{current}}
    {{py}} {{gains_dir}}/render_rss.py --baseline {{base}} --current {{current}}

gains-list:
    {{py}} {{gains_dir}}/runs.py --list
