

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
# Both profiles run the same nineteen models: the memtable takes writes
# from any thread, so there is no single-writer guard left for a debug
# build to trip. Seven of the models are `should_panic` calibrations that
# deliberately get the ordering wrong; they are what make the passes mean
# anything.

# Loom is bounded. Every recipe below builds its models first and then runs
# them under a hard limit of 10 minutes (15 for the nightly twins): a run
# that hits it fails. A model is sized to finish in under a minute and a
# recipe in under five, by its scenario and by an explicit preemption bound
# in its builder, never by `LOOM_MAX_DURATION`, which stops the search and
# lets the test pass. A model that is shrunk says so in its comment.
loom:
    RUSTFLAGS="--cfg loom" cargo test --release --test loom_memtable --no-run
    RUSTFLAGS="--cfg loom" timeout 10m cargo test --release --test loom_memtable

loom-debug:
    RUSTFLAGS="--cfg loom" cargo test --test loom_memtable --no-run
    RUSTFLAGS="--cfg loom" timeout 10m cargo test --test loom_memtable

# Loom models for `regolith::sync`: every primitive's wait protocol,
# with five calibrations that must fail. Release only: the larger models
# explore 0.1 to 0.4 million interleavings each (about four minutes in
# all), which a debug build multiplies several times over.
loom-sync:
    RUSTFLAGS="--cfg loom" cargo test --release --test loom_sync --no-run
    RUSTFLAGS="--cfg loom" timeout 10m cargo test --release --test loom_sync

# The five sync models whose three threads all contend for one lock or
# semaphore, at preemption bound 2 instead of the bound 1 `loom-sync`
# runs them at: their `#[ignore]`d twins, or the one `model` names. Each
# twin runs a smaller scenario of its own, because the shared one does not
# finish at bound 2 in any useful time (43 to 79 minutes a model, and never
# for the upgradable read). They take 2 s to 6 minutes each, so the nightly
# CI run carries them, one job per model.
loom-sync-deep model="":
    RUSTFLAGS="--cfg loom" cargo test --release --test loom_sync --no-run
    RUSTFLAGS="--cfg loom" timeout 15m cargo test --release --test loom_sync -- --ignored {{model}}

# Loom models for the per-thread I/O queues (D53): the unit claim, the
# completion pushed to every waiting queue, the idle waker, a read's wait,
# and close meeting a miss under way, with five calibrations that must
# fail. Release only, like
# `loom-sync`: the wait model explores close to 0.8 million interleavings.
loom-io:
    RUSTFLAGS="--cfg loom" cargo test --release --test loom_io_queue --no-run
    RUSTFLAGS="--cfg loom" timeout 10m cargo test --release --test loom_io_queue

# Loom models for the snapshot registry's per-thread slots: the slot and
# thread-number claims, a moved pin's release, announce-sample-confirm and
# the drain wake, with four calibrations that must fail. Release only.
loom-snapshots:
    RUSTFLAGS="--cfg loom" cargo test --release --test loom_snapshots --no-run
    RUSTFLAGS="--cfg loom" timeout 10m cargo test --release --test loom_snapshots

# Loom models for the per-core read path (Phase 7b): the read view's
# compare-and-swap publication, its reclamation and its freshness; the
# block cache's pin check, racing hands and byte bound; and the range-
# tombstone log's prefix publication, run against the real log. Each has
# a calibration that must fail.
loom-view:
    RUSTFLAGS="--cfg loom" cargo test --release --test loom_read_view --no-run
    RUSTFLAGS="--cfg loom" timeout 10m cargo test --release --test loom_read_view

loom-cache:
    RUSTFLAGS="--cfg loom" cargo test --release --test loom_block_cache --no-run
    RUSTFLAGS="--cfg loom" timeout 10m cargo test --release --test loom_block_cache

loom-tombstones:
    RUSTFLAGS="--cfg loom" cargo test --release --test loom_range_tombstones --no-run
    RUSTFLAGS="--cfg loom" timeout 10m cargo test --release --test loom_range_tombstones

# Loom models for the open-file slot table (acquire, evict, release, drain,
# and D60's park of a reopen that may not wait and the wake of a freed slot)
# and the column-family registry (create, drop and use racing in the
# ordered step), with five calibrations that must fail. Release, like
# `loom-io`.
loom-tables:
    RUSTFLAGS="--cfg loom" cargo test --release --test loom_tables --no-run
    RUSTFLAGS="--cfg loom" timeout 10m cargo test --release --test loom_tables

# Loom models for the lock-free commit pipeline (plan 4.7) and the version
# store's step: reserve and void, a cell's next lap, the pin, deciding with
# helping, the watermark claim, publication, a rollback meeting a decision
# under way, the step's sections, and parking (a queue's poll never waits:
# a job its holder parks, a job parked for the step, a rollback parked for
# a write in flight, the wake of a parked job against its landing and
# against the claim of the thread that parks it), with thirteen
# calibrations that must fail. Twenty-seven models, each bounded by a ring
# of two cells, two or three threads and an explicit preemption bound;
# measured at 1.3s in all, the largest at 4,214 interleavings. The limit is
# a hard one: a run that reaches it has failed.
loom-pipeline:
    RUSTFLAGS="--cfg loom" cargo test --release --test loom_pipeline --no-run
    RUSTFLAGS="--cfg loom" timeout 5m cargo test --release --test loom_pipeline

# Loom models for the pessimistic lock table (plan 4.6, 4.10): one holder
# per key, the bypass bound, a wait delivered to its own queue, the table's
# use count, and close meeting a wait being queued, with five calibrations
# that must fail. Release only; the ten run in under ten seconds.
loom-locks:
    RUSTFLAGS="--cfg loom" cargo test --release --test loom_locks --no-run
    RUSTFLAGS="--cfg loom" timeout 10m cargo test --release --test loom_locks

# Loom models for the compaction gate (E28) and for a job that parks on its
# queue instead of waiting for the gate, with three calibrations that must
# fail: a job that skips the gate, the old writer-preferring gate, and a
# parked job with no way back to its queue. Release only, like `loom-sync`.
loom-gate:
    RUSTFLAGS="--cfg loom" cargo test --release --test loom_gate --no-run
    RUSTFLAGS="--cfg loom" timeout 10m cargo test --release --test loom_gate

loom-all: loom loom-debug loom-sync loom-io loom-snapshots loom-view loom-cache loom-tombstones loom-tables loom-locks loom-gate loom-pipeline

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
#
# The suite is bounded. Every row runs on ONE TLC worker under a hard limit
# of 120 seconds: a row that hits it is reported as TIMED OUT and fails the
# recipe, it never passes. A configuration is sized to finish in under 60
# seconds on one worker; one that does not is shrunk (its `.cfg` says what
# was shrunk and what the smaller instance still covers), because the Lean
# proof covers every size and TLC only has to show a small instance's
# interleavings. Time a new row before adding it.
#
# As many rows run side by side as the machine has cores, each in a JVM
# sized for its one worker, and their lines are printed in the order below
# once all are done. With one worker a RED row stops at the shallowest
# broken invariant, the same on every run.
# Check every TLA+ row.
tla:
    #!/usr/bin/env bash
    set -uo pipefail
    cd proofs/tla
    # Fetched once, before the rows run side by side.
    ./tools/tlc --fetch-only >/dev/null || exit 1
    results=$(mktemp -d)
    trap 'rm -rf "$results"' EXIT
    # The cores this run may use (`nproc` counts those it is confined to).
    side=$(nproc 2>/dev/null || getconf _NPROCESSORS_ONLN)
    row=0
    # The module the next rows check; each block below sets it.
    spec=RepeatableRead
    # One row, started in the background: its line goes to a file named by
    # its number, and a `.fail` file beside it marks a wrong verdict.
    check() {
        row=$((row + 1))
        while [ "$(jobs -rp | wc -l)" -ge "$side" ]; do wait -n; done
        run_row "$(printf '%04d' "$row")" "$spec" "$@" > "$results/$(printf '%04d' "$row").out" 2>&1 &
    }
    run_row() {
        local n="$1" spec="$2" cfg="$3" expect="$4" inv="${5:-}" out code broke verdict states took
        # A serial collector and two compiler threads: what one worker on
        # one core uses. A temporary directory of its own, because TLC
        # unpacks its standard modules into it and two rows must not share
        # the files; the row's states go there too.
        mkdir -p "$results/tmp.$n"
        out=$(TLC_JVM_FLAGS="-XX:+UseSerialGC -XX:CICompilerCount=2 -Djava.io.tmpdir=$results/tmp.$n" \
              timeout 120 ./tools/tlc -workers 1 -metadir "$results/tmp.$n/states" -config "$cfg.cfg" "$spec.tla" 2>&1)
        code=$?
        # TLC words a broken invariant two ways: "is violated." when the search reaches a bad
        # state, and "is violated by the initial state:" when the very first state is already
        # bad. Both name the invariant, and both count.
        broke=$(sed -n -e 's/^Error: Invariant \(.*\) is violated\.$/\1/p' \
                       -e 's/^Error: Invariant \(.*\) is violated by the initial state:$/\1/p' <<<"$out" | head -1)
        # A broken promise about whole runs (a PROPERTY) is reported without its name. A row that
        # plants a bug against one names exactly one PROPERTY in its configuration, so that is the
        # one that broke.
        if [ -z "$broke" ] && grep -q '^Error: Temporal properties were violated\.$' <<<"$out"; then
            broke=$(sed -n 's/^PROPERTY \(.*\)$/\1/p' "$cfg.cfg" | head -1)
        fi
        states=$(sed -n 's/^.* states generated, \([0-9,]*\) distinct states found.*$/\1/p' <<<"$out" | tail -1)
        took=$(sed -n 's/^Finished in \(.*\) at (.*$/\1/p' <<<"$out" | tail -1)
        if [ "$code" -eq 124 ]; then
            # The hard limit: a failure, whatever the row was meant to show.
            verdict="TIMED OUT"
            took="over 120s"
        elif grep -q "No error has been found" <<<"$out"; then
            verdict=GREEN
        elif [ -n "$broke" ] && [ "$broke" = "$inv" ]; then
            verdict=RED
        elif [ -n "$broke" ]; then
            verdict="RED on $broke"
        else
            verdict=BROKEN
            echo "$out" | tail -20
        fi
        printf '  %-48s %-9s %9s states %9s  (expected %s)\n' \
            "$cfg" "$verdict" "${states:-?}" "${took:-?}" "$expect${inv:+ on $inv}"
        if [ "$verdict" != "$expect" ]; then touch "$results/$n.fail"; fi
    }
    check MC_RepeatableRead_Green                      GREEN
    check MC_RepeatableRead_Green_Live                 GREEN
    check MC_RepeatableRead_Red_Serializable           RED INV_AppendsCommit
    check MC_RepeatableRead_Red_SnapshotIsolation      RED INV_NoStaleDefinition
    check MC_RepeatableRead_Red_ReadCommitted          RED INV_NoStaleDefinition
    check MC_DefraLevel_Green_Heads                    GREEN
    check MC_DefraLevel_Green_Counters                 GREEN
    check MC_DefraLevel_Green_Counters_Clear           GREEN
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
    check MC_DefraLevel_Green_Parts_Rewriter           GREEN
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
    # E31, a flush's table and its memtable's retirement are one publication.
    # Lean: Regolith/LsmOrder.lean, flush_keeps_sources_disjoint,
    # split_install_holds_a_memtable_twice.
    check MC_LsmOrder_Red_SplitRetire                  RED NoDoubleSource
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
    # E38: a universal merge takes L0 files that lie next to one another.
    # Lean: Regolith/LsmOrder.lean, merge_window_reads_newest,
    # merge_gapped_breaks_reads.
    check MC_LsmOrder_Green_L0Merge                    GREEN
    check MC_LsmOrder_Red_L0MergeGap                   RED ReadNewest
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
    # D48: an ingest syncs the log before its manifest record. Lean:
    # Regolith/IngestDurability.lean, surviving_ingest_keeps_prefix.
    spec=IngestDurability
    check MC_IngestDurability_Green                    GREEN
    check MC_IngestDurability_Red_NoLogSync            RED GapFreePrefix
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
    check MC_WalRecovery_Red_StampUnsynced             RED RecoveryOpens
    # E29, E30: the manifest's torn end and the logs a flush retires, on a
    # sealed manifest and with flushes on several threads. Lean:
    # Regolith/ManifestRecovery.lean, crash_never_proves, replay_keeps_synced,
    # replay_never_above_newer_table, crash_never_proves_opened,
    # oldest_first_keeps_every_log.
    spec=ManifestRecovery
    check MC_ManifestRecovery_Green                    GREEN
    check MC_ManifestRecovery_Green_Refuses            RED NeverRefusesRot
    check MC_ManifestRecovery_Red_OldGuard             RED RecoveryOpens
    check MC_ManifestRecovery_Red_NoSyncBeforeNext     RED RecoveryOpens
    check MC_ManifestRecovery_Red_UnlinkBeforeSync     RED AckedSurvive
    check MC_ManifestRecovery_Red_RetireBeforeTable    RED AckedSurvive
    check MC_ManifestRecovery_Red_NoMinWalId           RED ReadsNewest
    check MC_ManifestRecovery_Red_IgnoreProof          RED RotSafe
    check MC_ManifestRecovery_Green_Sealed             GREEN
    check MC_ManifestRecovery_Red_JudgeCiphertext      RED RecoveryOpens
    check MC_ManifestRecovery_Green_Frozen2            GREEN
    check MC_ManifestRecovery_Red_NewestFirst          RED AckedSurvive
    # 4.12, D45: a sealed manifest batch keeps its checksum, checked before
    # any key. Lean: Regolith/ManifestSeal.lean, replay_opens_with_right_keys,
    # open_ends_only_at_a_torn_batch.
    spec=ManifestSeal
    check MC_ManifestSeal_Green                        GREEN
    check MC_ManifestSeal_Red_TagOnlyStop              RED OnlyTornEnds
    check MC_ManifestSeal_Red_TagOnlyRefuse            RED RecoveryOpens
    # 4.12, D57: a backup of an encrypted database seals its metadata, and a
    # restore checks every key before its first write; the listing names
    # every backup, a page of ids at a time, and a delete or purge sweeps
    # the pool a batch at a time, reading each listing as its walk of meta/
    # reaches it, and removes every unlisted table and no listed one. Lean:
    # Regolith/BackupSeal.lean, entitled_restore_is_faithful,
    # refusal_writes_nothing, collect_keeps_listed, last_write_holds_all,
    # listing_names_every_backup, purge_keeps_the_newest, collect_stream_eq,
    # stream_holds_one_batch, sweep_eq, sweep_removes_every_unlisted,
    # list_pages_all.
    spec=BackupSeal
    check MC_BackupSeal_Green                          GREEN
    check MC_BackupSeal_Green_Attack                   GREEN
    check MC_BackupSeal_Green_Stream                   GREEN
    check MC_BackupSeal_Green_Sweep                    GREEN
    check MC_BackupSeal_Green_SweepTwoTables           GREEN
    check MC_BackupSeal_Red_StreamSkips                RED ListedRestores
    check MC_BackupSeal_Red_SweepSkips                 RED SweepRemovesEveryUnlisted
    check MC_BackupSeal_Red_PlainMeta                  RED SealedMetadata
    check MC_BackupSeal_Red_PlainRestore               RED SealedMetadata
    check MC_BackupSeal_Red_OpenUnderCurrent           RED RightKeysRestore
    check MC_BackupSeal_Red_ListingUnbound             RED FaithfulRestore
    check MC_BackupSeal_Red_IdUnbound                  RED FaithfulRestore
    check MC_BackupSeal_Red_ManifestFirst              RED FaithfulRestore
    check MC_BackupSeal_Red_OverDatabase               RED FaithfulRestore
    check MC_BackupSeal_Red_CheckAfterCopy             RED RefusalWritesNothing
    check MC_BackupSeal_Red_GcSkipsSealed              RED ListedRestores
    check MC_BackupSeal_Red_GcSkipsUnreadable          RED ListedRestores
    check MC_BackupSeal_Red_MetaFirst                  RED ListedRestores
    check MC_BackupSeal_Red_ListSkipsUnreadable        RED ListingNamesEvery
    check MC_BackupSeal_Red_ListNeedsKey               RED ListingNamesEvery
    # 4.8, E5: compaction per snapshot stripe. Lean: Regolith/Stripes.lean,
    # reduce_reads.
    spec=StripeCompaction
    check MC_StripeCompaction_Green                    GREEN
    check MC_StripeCompaction_Green_Filter             GREEN
    check MC_StripeCompaction_Green_Inexact            GREEN
    check MC_StripeCompaction_Red_CaptureEarly         RED SnapshotReadsKept
    check MC_StripeCompaction_Red_InexactFold          RED HeadKept
    check MC_StripeCompaction_Red_IgnoreStripes        RED SnapshotReadsKept
    # E27: a pass retires a range tombstone below its range and every
    # snapshot. Green_Retires is the witness that the fix retires at all.
    # Lean: Regolith/TombstoneRetirement.lean, retire_keeps_reads.
    spec=TombstoneRetirement
    check MC_TombstoneRetirement_Green                 GREEN
    check MC_TombstoneRetirement_Green_Retires         RED NothingRetired
    check MC_TombstoneRetirement_Red_IgnoreSnapshots   RED SnapshotReadsKept
    check MC_TombstoneRetirement_Red_IgnoreDeeper      RED SnapshotReadsKept
    # 4.6, D54: the snapshot registry on per-thread slots with counted
    # entries, moved handles, copies and shared slots. Lean:
    # Regolith/SnapshotRegistry.lean, scan_respects_live,
    # clone_respects_live, pins_exact.
    spec=SnapshotRegistry
    check MC_SnapshotRegistry_Green                    GREEN
    check MC_SnapshotRegistry_Green_ThreeHandles       GREEN
    check MC_SnapshotRegistry_Red_NoConfirm            RED MinBelowLive
    check MC_SnapshotRegistry_Red_ScanThenSample       RED MinBelowLive
    check MC_SnapshotRegistry_Red_ReleaseHere          RED LiveCovered
    check MC_SnapshotRegistry_Red_CloneFresh           RED LiveCovered
    check MC_SnapshotRegistry_Red_PlainClaim           RED MinBelowLive
    check MC_SnapshotRegistry_Red_JoinNoRecheck        RED LiveEntryExact
    # E15: waiting for the last snapshot. With threads, the release that
    # drains the last pin wakes the waiter; on a target with one thread the
    # call reports what is still pinned and never waits. Lean:
    # Regolith/SnapshotWait.lean, no_lost_wake, one_thread_never_waits.
    spec=SnapshotWait
    check MC_SnapshotWait_Green                        GREEN
    check MC_SnapshotWait_Green_NoThreads              GREEN
    check MC_SnapshotWait_Red_WaitAnyway               RED NeverWaitsAlone
    check MC_SnapshotWait_Red_FutureAfterWatch         RED NoLostWake
    check MC_SnapshotWait_Red_ReadThenMark             RED NoLostWake
    # 4.6, D54: per-thread statistics shards. Lean: Regolith/ShardedStats.lean,
    # total_after_adds, read_between, reads_monotone.
    spec=ShardedStats
    check MC_ShardedStats_Green                        GREEN
    check MC_ShardedStats_Red_LostUpdate               RED QuiescentExact
    check MC_ShardedStats_Red_PartialRead              RED ReadBetween
    # E10, group commit. Lean: Regolith/GroupCommit.lean, group_eq_serial.
    spec=GroupCommit
    check MC_GroupCommit_Green                         GREEN
    check MC_GroupCommit_Green_Live                    GREEN
    check MC_GroupCommit_Green_LivePlain               GREEN
    check MC_GroupCommit_Green_ReadOnly                GREEN
    check MC_GroupCommit_Red_ViewOnly                  RED SerialEquivalent
    check MC_GroupCommit_Red_TrustEarly                RED SerialEquivalent
    check MC_GroupCommit_Red_PublishBeforeSync         RED DurableBeforeVisible
    # E21, the bounded leader: one group per turn, then hand off.
    check MC_GroupCommit_Red_DrainAll                  RED BoundedTurn
    # D53, the group fsync as a claimable job for commit_nowait members.
    # Green_Nowait_Owes is the witness that the GREEN run leaves groups owed.
    # Lean: Regolith/IoQueue.lean, group_sync_once, group_visible_after_sync.
    check MC_GroupCommit_Green_Nowait                  GREEN
    check MC_GroupCommit_Green_NowaitLive              GREEN
    check MC_GroupCommit_Green_Nowait_Owes             RED NothingOwed
    check MC_GroupCommit_Red_DoubleClaim               RED SingleSync
    # 4.7, the lock-free commit pipeline as built: helping, voiding, the
    # check in two parts (early, then in ring order), the round (one claim
    # on the log's device step), the rollback of a failed log, ordered
    # units and rotation through the ring. A Green row whose name ends in
    # Discards, Stale, Rotates, Voids, Helps or Aborts is a witness: the
    # GREEN run beside it with one false claim added, which must break, so
    # the GREEN run is known to reach the case. Lean:
    # Regolith/Pipeline.lean, seqs_dense, reader_sees_published,
    # rollback_as_if_never_decided, rollback_keeps_published,
    # sync_covers_only_written; Regolith/PipelineHelping.lean,
    # first_unfinished_can_step, helper_alone_finishes, helping_is_bounded;
    # Regolith/GroupCommit.lean, group_eq_serial, early_check_split.
    spec=CommitPipeline
    check MC_CommitPipeline_Green                           GREEN
    check MC_CommitPipeline_Green_Stop                      GREEN
    check MC_CommitPipeline_Green_Live                      GREEN
    check MC_CommitPipeline_Green_LiveIngest                GREEN
    check MC_CommitPipeline_Green_LiveApart                 GREEN
    check MC_CommitPipeline_Green_LiveThree_Head1           GREEN
    check MC_CommitPipeline_Green_LiveThree_Head2           GREEN
    check MC_CommitPipeline_Green_LiveThree_Head3           GREEN
    check MC_CommitPipeline_Green_Rollback                  GREEN
    check MC_CommitPipeline_Green_Rollback_Discards         RED NothingThrownOut
    check MC_CommitPipeline_Green_Rollback_Stale            RED NoStaleVerdict
    check MC_CommitPipeline_Green_Rollback_Three            GREEN
    check MC_CommitPipeline_Green_Rotation                  GREEN
    check MC_CommitPipeline_Green_Rotation_Rotates          RED NeverRotated
    check MC_CommitPipeline_Green_Rotation_Three            GREEN
    check MC_CommitPipeline_Green_Unit_Rollback             GREEN
    check MC_CommitPipeline_Green_Live_Voids                RED NothingVoided
    check MC_CommitPipeline_Green_Live_Helps                RED StoppedStaysUnfinished
    check MC_CommitPipeline_Green_Early                     GREEN
    check MC_CommitPipeline_Green_Early_Aborts              RED NoEarlyAbort
    check MC_CommitPipeline_Green_ReadOnly                  GREEN
    check MC_CommitPipeline_Green_Plain                     GREEN
    check MC_CommitPipeline_Red_OutOfOrder                  RED ReadersSeePrefix
    check MC_CommitPipeline_Red_AbortHole                   RED NoHole
    check MC_CommitPipeline_Red_NoHelping                   RED NoLiveThreadBlocked
    check MC_CommitPipeline_Red_SyncPastGap                 RED DurableImpliesWritten
    check MC_CommitPipeline_Red_ValidatePublished           RED NoLostUpdate
    check MC_CommitPipeline_Red_VoidNotCas                  RED OwnerSeesItsFate
    check MC_CommitPipeline_Red_TwoSyncs                    RED OneRound
    check MC_CommitPipeline_Red_TwoSyncs_Durable            RED DurableWithinDecided
    check MC_CommitPipeline_Red_FrontierFirst               RED PublishedIsVisible
    check MC_CommitPipeline_Red_UnitNoDrain                 RED DurableImpliesWritten
    check MC_CommitPipeline_Red_UnitNoDrain_SealedLog       RED InFlightInCurrentLog
    check MC_CommitPipeline_Red_UnitNoDrain_Unit            RED DurableImpliesWritten
    check MC_CommitPipeline_Red_SettleAnyEpoch              RED NoHole
    check MC_CommitPipeline_Red_SettleAnyEpoch_Abort        RED AbortsHaveCause
    check MC_CommitPipeline_Red_KeepMemtable                RED MemtableOnlyLive
    check MC_CommitPipeline_Red_NoEpochGate                 RED RecordsAreLive
    check MC_CommitPipeline_Red_PassBeforeApply             RED AppliedBeforePassed
    check MC_CommitPipeline_Red_PassBeforeApply_LostUpdate  RED NoLostUpdate
    check MC_CommitPipeline_Red_RollbackForgets             RED PublishedPrefix
    check MC_CommitPipeline_Red_RollbackForgets_Ack         RED NoFalseAck
    check MC_CommitPipeline_Red_NoFreeze                    RED NoHole
    check MC_CommitPipeline_Red_TrustEarly                  RED NoLostUpdate
    check MC_CommitPipeline_Red_PublishBeforeSync           RED DurableBeforeVisible
    check MC_CommitPipeline_Red_DecideAnyOrder              RED DecidedIsPrefix
    check MC_CommitPipeline_Red_DecideAnyOrder_Order        RED SeqInRingOrder
    check MC_CommitPipeline_Red_StopHoldsClaim              RED NoLiveThreadBlocked
    # R13 and D53, non-blocking reads on per-thread I/O queues: single-flight
    # units claimed by one CAS, completions only on the asking queue, idle
    # wakeups. Lean: Regolith/IoQueue.lean, claim_once, told_at_most_once,
    # every_waiter_told, no_lost_idle_wakeup, busy_never_woken,
    # single_thread_finishes.
    spec=NonBlocking
    check MC_NonBlocking_Green_Pool                    GREEN
    check MC_NonBlocking_Green_PoolLive                GREEN
    check MC_NonBlocking_Green_Jobs                    GREEN
    check MC_NonBlocking_Green_JobsLive                GREEN
    check MC_NonBlocking_Green_Single                  GREEN
    check MC_NonBlocking_Green_SingleLive              GREEN
    check MC_NonBlocking_Red_WrongQueue                RED OwnQueue
    check MC_NonBlocking_Red_LostIdleWakeup            RED NoLostIdleWakeup
    check MC_NonBlocking_Red_DoubleRun                 RED SingleRun
    check MC_NonBlocking_Red_SelfIoNowhere             RED NoOrphanUnit
    check MC_NonBlocking_Red_BusyWoken                 RED BusyNeverWoken
    # D53, the commit side's units: a group's fsync claimed by one member's
    # poll and told to every member's own queue, and a stall's passive unit
    # landed by its clearer or by a writer's second look. Lean:
    # Regolith/IoQueue.lean, group_sync_once, group_visible_after_sync,
    # ticket_ready_only_at_own_poll, stall_lands_when_clear.
    check MC_NonBlocking_Green_Commit                  GREEN
    check MC_NonBlocking_Green_Stall                   GREEN
    check MC_NonBlocking_Red_DoubleSync                RED SingleRun
    check MC_NonBlocking_Red_PublishAtWrite            RED VisibleAfterSync
    check MC_NonBlocking_Red_DeliverOnLander           RED DeliveredOnOwnPoll
    check MC_NonBlocking_Red_NoRecheck                 RED StallLandsWhenClear
    # Phase 7 integration: with no worker and inline compaction on, no
    # stopped writer waits on a relief nobody runs. Every piece of progress
    # lands the stall's unit (relief handed back), a contended writer reads
    # the progress count again once registered, and a foreground job that
    # held the gate relieves the stop. Lean: Regolith/StallRelief.lean,
    # no_stranded_wait, no_relief_strands_a_waiter,
    # no_hand_back_strands_a_waiter, no_recheck_strands_a_waiter.
    spec=StallRelief
    check MC_StallRelief_Green                         GREEN
    check MC_StallRelief_Red_NoRelief                  RED NoStrandedWait
    check MC_StallRelief_Red_NoHandBack                RED NoStrandedWait
    check MC_StallRelief_Red_NoRecheck                 RED NoStrandedWait
    # E35: an engine that latches clears no stop, so the latch lands the
    # stall's unit (its flag stored first, read again by a writer once
    # registered), and a rotation that flushed at the memtable cap counts
    # its progress whether its seal went through or failed. Lean:
    # no_wait_once_latched, no_latch_land_strands_a_waiter,
    # no_latch_recheck_strands_a_waiter, no_rotate_refresh_strands_a_waiter.
    check MC_StallRelief_Green_Failures                GREEN
    check MC_StallRelief_Red_NoLatchLand               RED NoWaitOnceLatched
    check MC_StallRelief_Red_NoLatchRecheck            RED NoWaitOnceLatched
    check MC_StallRelief_Red_NoRotateRefresh           RED NoStrandedWait
    # E36: a write stopped while its relief's failure is recorded is told
    # that failure, so recording one lands the stall's unit (stored first,
    # read again by a writer once registered, while a stop still holds), and
    # a write that was already waiting is told the same. Lean:
    # no_wait_once_failing, no_fail_land_strands_a_waiter,
    # no_fail_recheck_strands_a_waiter.
    check MC_StallRelief_Green_ReliefFails             GREEN
    check MC_StallRelief_Red_NoFailLand                RED NoWaitOnceFailing
    check MC_StallRelief_Red_NoFailRecheck             RED NoWaitOnceFailing
    # E16: with no worker, a write that owes a step of background work runs
    # exactly one, and L0 stays at its compaction trigger (at the stop
    # trigger when every write seals). Lean: Regolith/OwedStep.lean,
    # write_one_step, l0_bounded, l0_bounded_by_stop.
    spec=OwedStep
    check MC_OwedStep_Green                            GREEN
    check MC_OwedStep_Green_TinyMemtable               GREEN
    check MC_OwedStep_Red_FlushOwesNothing             RED L0Bounded
    check MC_OwedStep_Red_StepUntilIdle                RED OneStepPerWrite
    # regolith::sync's locks after D49: barging with bounded bypass, for
    # Mutex, Semaphore and ReentrantMutex, one step per atomic instruction
    # of src/sync. Lean: Regolith/Sync.lean, mutual_exclusion,
    # bounded_bypass, owed_at_bound, owed_exclusive.
    spec=Sync
    check MC_Sync_Green_Mutex                          GREEN
    check MC_Sync_Green_MutexBarger                    GREEN
    check MC_Sync_Green_MutexBoth                      GREEN
    check MC_Sync_Green_MutexLive                      GREEN
    check MC_Sync_Green_Semaphore                      GREEN
    check MC_Sync_Green_BigRequest                     GREEN
    check MC_Sync_Green_SemaphoreLive                  GREEN
    check MC_Sync_Green_Reentrant                      GREEN
    check MC_Sync_Green_ReentrantLive                  GREEN
    check MC_Sync_Red_UnboundedBarging                 RED BoundedBypass
    check MC_Sync_Red_ReleaseNoWake                    RED NoLostWakeup
    check MC_Sync_Red_LoseQueuePosition                RED BoundedBypass
    check MC_Sync_Red_CancelNoPassOn                   RED CancelPassesOn
    check MC_Sync_Red_NoRecheck                        RED NoLostWakeup
    check MC_Sync_Red_NoDirty                          RED NoLostWakeup
    check MC_Sync_Red_LowerPendingMarker               RED EveryWaiterServed
    check MC_Sync_Red_IgnoreOwed                       RED HandoffExclusive
    check MC_Sync_Red_NoDepth                          RED ReentrancyDepth
    # E32, what a drain costs its thread: one pass, and one more for each
    # waiter operation, or release with a node queued, that lands on it.
    # Green_PassesGrow is the witness that the passes do grow with those
    # (lock-free, not wait-free): FewPasses is no promise and must fail.
    check MC_Sync_Red_ReleaseDirties                   RED DrainBounded
    check MC_Sync_Red_ExitIgnoresRequest               RED NoLostWakeup
    check MC_Sync_Green_PassesGrow                     RED FewPasses
    # regolith::sync::Notify, which keeps FIFO handoff. Lean:
    # Regolith/SyncFifo.lean, fifo_served, no_stranded_waiter.
    spec=SyncNotify
    check MC_SyncNotify_Green                          GREEN
    check MC_SyncNotify_Green_Live                     GREEN
    check MC_SyncNotify_Red_WakeBeforeHandoff          RED NoLostWakeup
    check MC_SyncNotify_Red_CancelNoPassOn             RED CancelPassesOn
    check MC_SyncNotify_Red_NoRecheck                  RED NoLostWakeup
    check MC_SyncNotify_Red_NoGenCheck                 RED NoLostWakeup
    # regolith::sync::RwLock and ReentrantRwLock after D49, with D50's
    # upgradable read, one step of src/sync/raw_rwlock.rs at a time on the
    # queue of Sync.tla. Lean: Regolith/Sync.lean for the exclusive side.
    spec=SyncRwLock
    check MC_SyncRwLock_Green_Plain                    GREEN
    check MC_SyncRwLock_Green_WriterLive               GREEN
    check MC_SyncRwLock_Green_ReaderLive               GREEN
    check MC_SyncRwLock_Green_Upgrade                  GREEN
    check MC_SyncRwLock_Green_UpgradeLive              GREEN
    check MC_SyncRwLock_Green_Reentrant                GREEN
    check MC_SyncRwLock_Green_ReentrantLive            GREEN
    check MC_SyncRwLock_Red_UnboundedBarging           RED BoundedBypass
    check MC_SyncRwLock_Red_AnyReaderUpgrade           RED NoUpgradeDeadlock
    check MC_SyncRwLock_Red_UpgradeNoHoldBack          RED UpgradeHoldsBack
    check MC_SyncRwLock_Red_OwnerUnaware               RED NoSelfDeadlock
    # E33: a dropped upgrade while the reader leaves and the next task takes
    # the upgradable read. The RED is the step the fix removed: the pass
    # reads UPGRADING and takes the write for the node in its slot.
    check MC_SyncRwLock_Green_UpgradeDropped           GREEN
    check MC_SyncRwLock_Red_PassTakesWrite             RED GuardsCounted
    # The compaction gate (4.6, E28): a pass shares it, a job holds it
    # alone, no waiter is passed over more than Bound times either way, the
    # worker takes turns between jobs and passes, and a job parked on its
    # queue is always woken. The old gate's rule is Red_OldGate. Lean:
    # Regolith/CompactionGate.lean, mutual_exclusion, bounded_bypass,
    # owed_only_gets_nearer, worker_takes_turns, parked_job_keeps_its_wake.
    spec=CompactionGate
    check MC_CompactionGate_Green                      GREEN
    check MC_CompactionGate_Green_All                  GREEN
    check MC_CompactionGate_Green_Queue                GREEN
    check MC_CompactionGate_Green_Passes               GREEN
    check MC_CompactionGate_Green_Live                 GREEN
    check MC_CompactionGate_Green_LiveServed           GREEN
    check MC_CompactionGate_Red_OldGate                RED BoundedBypass
    check MC_CompactionGate_Red_NoHandoff              RED BoundedBypass
    check MC_CompactionGate_Red_DrainJobs              RED WorkerTakesTurns
    check MC_CompactionGate_Red_WakeDropped            RED NoLostWake
    check MC_CompactionGate_Red_StaleWaker             RED NoLostWake
    check MC_CompactionGate_Red_SkipGate               RED MutualExclusion
    # regolith::sync::Event, Latch and Barrier.
    spec=SyncLatch
    check MC_SyncLatch_Green_Event                     GREEN
    check MC_SyncLatch_Green_Latch                     GREEN
    check MC_SyncLatch_Green_Barrier                   GREEN
    check MC_SyncLatch_Red_NoRecheck                   RED NoLostWakeup
    check MC_SyncLatch_Red_CountCheck                  RED NoLostWakeup
    # regolith::sync::OnceCell and Lazy: one pointer published by one
    # compare-and-swap, and a one-permit semaphore for the initializers'
    # turns, which a publisher opens wide.
    spec=SyncOnce
    check MC_SyncOnce_Green                            GREEN
    check MC_SyncOnce_Red_PlainStore                   RED PublishedOnce
    check MC_SyncOnce_Red_LoserKeepsOwn                RED ReadersAgree
    check MC_SyncOnce_Red_CancelNoReset                RED NoLostWakeup
    check MC_SyncOnce_Red_PublishNoOpen                RED NoLostWakeup
    # Transaction callbacks (3.16), told on the committing thread (D53), in
    # both forms of commit: the blocking commit `transact` calls, and
    # commit_nowait, whose pending ticket is resolved from its commit group
    # at delivery. Lean: Regolith/Callbacks.lean, exactly_once, order,
    # attempts_isolated, delivered_once, delivered_on_queue_thread,
    # resolved_after_landing, resolved_once_on_queue_thread.
    spec=TxnCallbacks
    check MC_TxnCallbacks_Green_Immediate              GREEN
    check MC_TxnCallbacks_Green_Blocking               GREEN
    check MC_TxnCallbacks_Green_Nowait                 GREEN
    check MC_TxnCallbacks_Green_Eventual               GREEN
    check MC_TxnCallbacks_Red_CommitBeforeDurable      RED CommitAfterDurable
    check MC_TxnCallbacks_Red_SkipCallbackWrites       RED NoLostUpdate
    check MC_TxnCallbacks_Red_CallbacksSurvive         RED AttemptIsolation
    check MC_TxnCallbacks_Red_DeliverNoClaim           RED AtMostOnce
    check MC_TxnCallbacks_Red_HelperDelivers           RED OnCommittingThread
    check MC_TxnCallbacks_Red_CloseNoClaim             RED AtMostOnce
    # 4.6, Phase 7b: the wait-free read view (D54). Lean:
    # Regolith/ReadView.lean, reachable_safe and cas_chain.
    spec=ReadView
    check MC_ReadView_Green                            GREEN
    check MC_ReadView_Red_FreeEarly                    RED NoFreedRead
    check MC_ReadView_Red_StaleLoad                    RED FreshLoad
    check MC_ReadView_Red_PlainStore                   RED ChainOfPublications
    # Phase 7 integration: the read view's publishers as group commit and the
    # flush off the commit path left them, every one by compare-and-swap.
    # A flush installs its table and retires its memtable in one publication.
    # Lean: Regolith/ReadViewPublishers.lean, no_lost_memtable,
    # retired_stay_gone, flush_keeps_sources_disjoint,
    # split_install_holds_a_memtable_twice, plain_retire_loses_a_seal,
    # plain_version_loses_a_seal.
    spec=ReadViewPublishers
    check MC_ReadViewPublishers_Green                  GREEN
    check MC_ReadViewPublishers_Red_SplitRetire        RED NoDoubleSource
    check MC_ReadViewPublishers_Red_PlainRetire        RED NoLostMemtable
    check MC_ReadViewPublishers_Red_PlainVersion       RED NoLostMemtable
    # 4.6, Phase 7b: the lock-free CLOCK block cache. Lean:
    # Regolith/ClockCache.lean, evict_only_unpinned, reachable_safe,
    # two_level_bounded and used_exact.
    spec=ClockCache
    check MC_ClockCache_Green                          GREEN
    check MC_ClockCache_Red_IgnorePins                 RED NoFreedPin
    check MC_ClockCache_Red_Unbounded                  RED ByteBound
    check MC_ClockCache_Red_LandingUnheld              RED LandedReadable
    # 4.6, Phase 7b and 4.7: a memtable's append-only range-tombstone log,
    # appended to by whichever threads apply commits. Green_Twice is the
    # witness that the GREEN run appends one tombstone twice. Lean:
    # Regolith/TombstoneLog.lean, one_slot_each, ready_whole and
    # published_seen.
    spec=TombstoneLog
    check MC_TombstoneLog_Green               GREEN
    check MC_TombstoneLog_Green_Readers       GREEN
    check MC_TombstoneLog_Green_Twice         RED NeverTwice
    check MC_TombstoneLog_Red_ReadyFirst      RED ReadWhole
    check MC_TombstoneLog_Red_HorizonFirst    RED PublishedSeen
    check MC_TombstoneLog_Red_LoadStore       RED OneSlotEach
    check MC_TombstoneLog_Red_LoadStore_Lost  RED PublishedSeen
    # 4.6, Phase 7c1: the open-file slot table under max_open_files. Lean:
    # Regolith/OpenFileTable.lean, open_le_cap, never_closes_in_use,
    # reads_own_file.
    spec=OpenFileTable
    check MC_OpenFileTable_Green                       GREEN
    check MC_OpenFileTable_Green_TwoSlots              GREEN
    check MC_OpenFileTable_Red_IgnoreReaders           RED NeverClosedInUse
    check MC_OpenFileTable_Red_NoOwnerRecheck          RED ReadsOwnFile
    check MC_OpenFileTable_Red_OutsideTable            RED AtMostCap
    # D60: a queue unit's reopen never waits for a slot, and a parked one is
    # never forgotten. Lean: Regolith/OpenFileNoWait.lean, never_waits;
    # Regolith/OpenFileNoWaitProof.lean, retry_never_lost; the REDs in
    # Regolith/OpenFileNoWaitRed.lean.
    check MC_OpenFileTable_Green_NoWait                GREEN
    check MC_OpenFileTable_Green_NoWaitTwoSlots        GREEN
    check MC_OpenFileTable_Red_Waits                   RED NeverWaits
    check MC_OpenFileTable_Red_MarkFirst               RED RetryNeverLost
    check MC_OpenFileTable_Red_PublishDropsWanted      RED RetryNeverLost
    check MC_OpenFileTable_Red_WakeNeedsParked         RED RetryNeverLost
    # 4.6, Phase 7c1: column-family create, drop and use, fenced in the
    # ordered step. Lean: Regolith/CfRegistry.lean, no_write_after_drop,
    # no_write_before_birth, life_in_order.
    spec=CfRegistry
    check MC_CfRegistry_Green                          GREEN
    check MC_CfRegistry_Red_FenceOutside               RED NoWriteAfterDrop
    check MC_CfRegistry_Red_RetireLate                 RED NoWriteAfterDrop
    check MC_CfRegistry_Red_ReuseId                    RED LifeInOrder
    # Phase 7 integration: the fence on every group-commit path (the
    # leader's own request, a queued ticket, the hand-off's held ticket, a
    # transaction member, an ingest's install). Lean: group_no_write_after_drop,
    # fenced_at_hand_off_lands_after_drop.
    check MC_CfRegistry_Red_FenceAtHandOff             RED NoWriteAfterDrop
    check MC_CfRegistry_Red_TxnUnfenced                RED NoWriteAfterDrop
    # 4.6, Phase 7c1: the env file maps, positional reads and lock-free
    # in-memory files. Lean: Regolith/EnvFiles.lean, positional_reads_own,
    # current_holds_finished, read_sees_finished.
    spec=EnvFiles
    check MC_EnvFiles_Green                            GREEN
    check MC_EnvFiles_Green_ThreeWriters               GREEN
    check MC_EnvFiles_Red_SharedCursor                 RED ReadsOwnBytes
    check MC_EnvFiles_Red_NoFreeze                     RED CurrentHoldsFinished
    check MC_EnvFiles_Red_StaleFrozen                  RED CurrentHoldsFinished
    # A table renamed aside while its handles reopen it: the Env's rename adds
    # the new name before it drops the old, and a reopen that found nothing
    # loads the names again. Lean: Regolith/EnvFilesRename.lean,
    # open_finds_file, and the REDs remove_first_loses and no_reload_loses.
    check MC_EnvFiles_Green_Rename                     GREEN
    check MC_EnvFiles_Red_RemoveFirst                  RED OpenFindsFile
    check MC_EnvFiles_Red_NoReload                     RED OpenFindsFile
    # The pessimistic lock table (plan 4.6, 4.10): one holder per key, no
    # lost wake-up, bounded bypass, a wait delivered to its own queue, and a
    # lock released when its commit lands. Lean: Regolith/LockTable.lean,
    # mutual_exclusion, retired_unused, no_stranded_front, handed_is_told,
    # bounded_bypass, note_on_own_queue, ready_by_own_queue,
    # isolation_at_landing.
    spec=LockTable
    check MC_LockTable_Green_Try                       GREEN
    check MC_LockTable_Green_Bound2                    GREEN
    check MC_LockTable_Green_Blocking                  GREEN
    check MC_LockTable_Green_Nowait                    GREEN
    check MC_LockTable_Green_Cancel                    GREEN
    check MC_LockTable_Green_Table                     GREEN
    check MC_LockTable_Green_Mixed                     GREEN
    check MC_LockTable_Green_MixedLive                 GREEN
    check MC_LockTable_Green_Four                      GREEN
    check MC_LockTable_Red_RetireNoCas                 RED MutualExclusion
    check MC_LockTable_Red_NoRecheck                   RED NoStrandedFront
    check MC_LockTable_Red_ReleaseNoWake               RED NoStrandedFront
    check MC_LockTable_Red_CancelNoPassOn              RED NoStrandedFront
    check MC_LockTable_Red_NoteAfterPoll               RED WokenIsTold
    check MC_LockTable_Red_UnboundedBarging            RED BoundedBypass
    check MC_LockTable_Red_WrongQueue                  RED OwnQueue
    check MC_LockTable_Red_CompleteOnWaker             RED OwnQueue
    check MC_LockTable_Red_ReleaseAtWrite              RED IsolationAtLanding
    check MC_LockTable_Red_ReleaseAtDelivery           RED HeldOnlyWhileNeeded
    wait
    rm -rf ./*_TTrace_*.tla ./*_TTrace_*.bin
    cat "$results"/*.out
    failed=$(find "$results" -name '*.fail' | wc -l)
    echo "  $row rows, $failed with the wrong verdict"
    [ "$failed" -eq 0 ]

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

# Every line of a TLA+ model, a TLC configuration and a Lean proof carries a
# plain-words comment directly above it, written for a reader who knows
# neither the language nor the code; `proofs/check-comments.sh` states the
# rule and fails on any line without one. The commit-pipeline models
# (CommitPipeline, GroupCommit, NonBlocking, and Pipeline.lean and
# IoQueue.lean) are left out: they are being rewritten on the commit-pipeline
# branch, and they join this check by deleting the `--except` below.
# Fail when a proof line has no comment above it.
proofs-comments:
    proofs/check-comments.sh --except '/(MC_)?(CommitPipeline|GroupCommit|NonBlocking)[_.]|/(Pipeline|IoQueue|GroupCommit)\.lean$'

# Every formal check: the TLA+ models, the Lean proofs, and their comments.
proofs: tla lean proofs-comments

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
        cargo run --release -p regolith-wasm-probe --bin regolith-wasm-probe -- \
            --profile "$profile" --records {{records}} --sustained {{sustained}} \
            --probe-host --report-memory
    done

# The OPFS contract against a real browser. `wasm-pack test` cannot
# drive these: it appends `--tests`, which builds every target in
# `tests/`, and all but the three `wasm_opfs*` files are native-only.
# The runner is named per target instead, so only the named test
# binaries are built.
#
# Needs `wasm-bindgen-test-runner` from the `wasm-bindgen-cli` release that
# Cargo.lock pins for `wasm-bindgen`, to the patch: the two share an
# unstable schema, and a runner of another version refuses the test binary
# with a schema error after the whole build. The recipe checks that first
# and says what to install.
wasm-browser:
    #!/usr/bin/env bash
    set -euo pipefail
    pinned=$(awk '/^name = "wasm-bindgen"$/ { found = 1; next } found && /^version = / { gsub(/"/, "", $3); print $3; exit }' Cargo.lock)
    if ! command -v wasm-bindgen-test-runner >/dev/null 2>&1; then
        echo "error: wasm-bindgen-test-runner is not on PATH; install it with: cargo install wasm-bindgen-cli --version $pinned --locked" >&2
        exit 1
    fi
    have=$(wasm-bindgen --version 2>/dev/null | awk '{ print $2 }')
    if [ "$have" != "$pinned" ]; then
        echo "error: wasm-bindgen-cli is ${have:-not installed} but Cargo.lock pins wasm-bindgen $pinned, and the two must match exactly; install it with: cargo install wasm-bindgen-cli --version $pinned --locked" >&2
        exit 1
    fi
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
