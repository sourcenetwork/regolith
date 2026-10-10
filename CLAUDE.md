# Development Principles

## 0. What Regolith Is

**regolith** (crate: `regolith`; the version is in `Cargo.toml`) is a pure Rust, embedded LSM-tree key-value store built from scratch. The architecture follows the LevelDB design (memtable → WAL → leveled SSTables → background compaction); the public API is shaped to slot into common embedded-KV abstraction layers so consuming applications can swap regolith in alongside other backends through the same trait.

Early-stage. The public API (`Db`, `Snapshot`, `WriteBatch`, `Options`) is small and stable-shaped, but breakage is allowed pre-1.0.

### Design goals

- **Pure Rust, no FFI**: no C/C++ toolchain, no `bindgen`, no linker surprises in the library or checked-in workspace tools
- **LSM-tree**: write-optimized with level-based background compaction
- **MVCC**: point-in-time consistent reads via global sequence numbers
- **Crash recovery**: WAL whose records carry the offset the last sync made durable, so replay tells a crash from damage
- **Concurrent reads**: no read takes a lock. A read loads the published view wait-free (`src/engine/read_view.rs`, a kovan `Atom`), walks the arena-backed skip list memtable (`src/engine/skiplist/`) and its append-only range-tombstone log, and uses a lock-free CLOCK block cache
- **No async runtime required**: compaction runs on background worker threads (`Options::max_background_compactions`), or inline on a target that has none

---

## 1. Information Hygiene

This codebase is designed for **AI-human pair programming**. Every structural choice optimizes for **rapid context acquisition**.

**Context clarity is oxygen for productive collaboration.**

## 2. Temporal Boundaries

| Zone        | Contains                | Lives in                        |
| ----------- | ----------------------- | ------------------------------- |
| **Past**    | How we got here         | Git history, closed issues/PRs  |
| **Present** | What the code does now  | Working tree                    |
| **Future**  | What we might do next   | GitHub issues                   |

**No commented-out code. No TODO comments (create issues instead). No speculative docs.**

## 3. No Documentation Files

Only allowed: `README.md`, `CLAUDE.md`, `Cargo.toml`, `LICENSE-*`.

No `ROADMAP.md`, `DEVELOPMENT.md`, `docs/` directories, or planning documents.

## 4. File Organization

**One concept per file. Small files over large files for new code.**

### Module Map

Workspace layout:

```text
src/                    # Publishable regolith library crate
tests/                  # Public-API integration, corruption, concurrency, and property tests
tests/auto_traits.rs    # Compile-time Send and Sync assertions for the public handles
tools/regolith-bench/       # Pure-Rust benchmark CLI
tools/regolith-stress/      # Pure-Rust stress CLI
tools/regolith-ycsb/        # Pure-Rust YCSB-style workload CLI
tools/regolith-wasm-probe/  # Pure-Rust wasm probe
fuzz/                   # cargo-fuzz harnesses, outside the normal workspace
```

Library modules:

```text
src/
├── lib.rs              # Public API: Db, Snapshot, WriteBatch, column families, re-exports
├── allocate.rs         # Conflict-free allocation of u64 ranges: Db::allocate
├── backup.rs           # BackupEngine: backups, metadata sealed through the KeyProvider (D57), restore
├── backup/             # format.rs: the .backup metadata, plain (version 3) and sealed (version 4)
├── checkpoint.rs       # Hardlinked checkpoint creation
├── column_family.rs    # Column-family handles, descriptors, and the lock-free registry
├── conflict.rs         # Conflict reasons: Conflict, Access, WriteKind
├── encryption.rs       # Encryption at rest: KeyProvider, KeyId, KeyMaterial
├── error.rs            # Error enum, Result alias
├── event_listener.rs   # Flush/compaction event callbacks
├── io_queue.rs         # Non-blocking reads: ReadMode, QueueId, IoBudget, IoProgress
├── io_queue/           # queue.rs (IoQueue: poll, idle_waker), wait.rs (IoWait, WouldBlock)
├── iter.rs             # Public iterator wrappers
├── log_layout.rs       # LogLayout: the key layout of a commit-ordered log
├── options.rs          # Options, tuning enums, MergeOperator, CompactionFilter
├── options/            # Options builder methods (builder.rs) and getters (getters.rs)
├── per_thread.rs       # A small number per thread (bounded pool, given back on exit) for per-core shards
├── perf_context.rs     # Per-operation performance counters
├── portability.rs      # Atomics shim and the portability tier map
├── rate_limiter.rs     # Token-bucket rate limiter
├── slice.rs            # DbSlice: zero-copy value handle
├── sst_file_writer.rs  # External SSTable writer API
├── statistics.rs       # Tickers and histograms, sharded per thread, summed when read
├── stream_writer.rs    # StreamingWriter: bounded-memory write stream
├── tailing.rs          # Tailing iterator API
├── testing.rs          # `testing` feature: property checks a caller runs against its own trait implementations
├── transaction.rs      # Optimistic and pessimistic transactions, isolation levels
├── transaction/        # policy.rs (KeyClassifier, key classes), txn_options.rs (TxnOptions),
│                       # scan_range.rs (scan stretches), write_buffer.rs (buffered puts, deletes, merges)
├── ttl.rs              # TTL database wrapper
├── sync/               # Public regolith::sync: async locks, semaphore, notify, event, latch, barrier, once cell
│   ├── queue.rs        # Wait queue and drain role every primitive builds on
│   ├── contend.rs      # The acquire every lock-like primitive shares: barging with bounded bypass (D49)
│   ├── waiter.rs       # Waiter nodes, their free list, the wake list
│   └── internal.rs     # The engine's private std/loom atomics, Mutex, RwLock, Condvar and Gate
├── txn_buffer.rs       # Concurrent write and read-set buffer of one transaction
├── env/                # Env trait and backends: StdEnv, MemEnv, WASI, OPFS; db_lock.rs
│   ├── mem_file.rs     # Lock-free in-memory file behind MemEnv and the OPFS mirror
│   └── open_file_limit/ # max_open_files: lock-free slot table (slots.rs), rename-aside removal
└── engine/
    ├── mod.rs          # RegolithEngine orchestration, read paths, rotation, recovery
    ├── commit/         # Group commit pipeline: ring, bounded leader, transaction members decided in
    │                   # group order (group.rs, txn.rs), the check up to a horizon (early.rs), stall signal,
    │                   # the column-family fence in the ordered step (families.rs)
    ├── flush.rs        # Writing a frozen memtable to L0, shared with the compaction workers
    ├── background_step.rs # Flushes off the commit path; the bounded step a write owes with no worker
    ├── stall_state.rs  # Write-stall thresholds and the level writers cache
    ├── compaction.rs   # Level/FIFO/universal compaction planning and worker loop
    ├── compaction/     # Per-snapshot-stripe folding of versions and merge chains
    ├── manifest.rs     # VersionSet, VersionEdit log, level tracking
    ├── manifest/       # Sealed manifests (sealed.rs), the judge of a torn tail (tail.rs, E29), tests
    ├── log_retirement.rs # Retiring flushed logs: min_wal_id in the table's batch, failed removals
    │                   # reported and retried (E30)
    ├── ingest.rs       # External-table ingest without a rewrite: per-file sequence (D48, E8)
    ├── open_transactions.rs # The open transactions close aborts
    ├── read_rule.rs    # How a commit judges one read against later commits
    ├── memtable.rs     # Arena-backed skip list memtable plus its range tombstones
    ├── memtable/       # Key walks, probe tests, and tombstones.rs: the append-only, lock-free range-tombstone log
    ├── skiplist/       # Insert-only concurrent skip list over the arena
    ├── sstable.rs      # SSTable reader/writer, footer, index block
    ├── sstable/        # SSTable key walks, size limits, sealed tables (V7, V8)
    ├── wal.rs          # Write-ahead log writer (format 2), CLOSE, format 1 reading rules
    ├── wal_frame.rs    # WAL format 2: stamp, group record frame, the scan past damage
    ├── wal_replay.rs   # Streaming reader over one WAL file: the O < P rule
    ├── wal_v1.rs       # Format 1 of the WAL, as 0.1.x wrote it, for replay
    ├── wal_seal.rs     # Sealed WAL: the stamp sealed and durable at creation, sealed records
    ├── seal.rs         # AES-256-GCM-SIV frames and the keyring over a KeyProvider
    ├── recovery.rs     # Replaying the WALs at open, the dropped-tail report, the rewrite
    ├── arena.rs        # Bump allocator for one memtable
    ├── block.rs        # Data blocks: prefix compression, restart points, varint
    ├── block_cache.rs  # Sharded lock-free CLOCK cache for decompressed SSTable blocks: pins, byte bound
    ├── block_cache/    # ring.rs: the lock-free CLOCK ring of slot words; tests.rs
    ├── callback.rs     # Catching a panic in caller code inside a commit or a background step
    ├── bloom.rs        # Bloom filter (double-hashed xxh3)
    ├── checksum.rs     # Checksum helpers
    ├── filter_block.rs # SSTable filter region: user-key and prefix bloom filters
    ├── index_block.rs  # Decoded SSTable index blocks
    ├── internal_key.rs # MVCC internal key encoding
    ├── io/             # CacheOnly misses: unit table, the close gate (mod.rs), single-flight units
    │                   # (unit.rs), per-queue inbox and landings (shared.rs), the mode scope (scope.rs),
    │                   # stack.rs, atomic_waker.rs
    ├── loom_model/     # Loom models of the engine's lock-free protocols (--cfg loom)
    ├── lookup_key.rs   # Inline-first internal key used by every read path
    ├── iterator.rs     # Engine iterator merge logic
    ├── range_tombstone.rs # Range-delete tombstone encoding
    ├── read_view.rs    # The published set of memtables and version a reader loads, wait-free (kovan Atom)
    ├── reclaim.rs      # Prompt kovan reclamation for retired views and tombstone indexes
    ├── read_horizon.rs # Newest sequence whose data is durable and applied
    ├── snapshot_registry.rs # Live snapshot sequences on per-thread slots: announce, sample, confirm
    ├── snapshot_registry/   # chain.rs: a slot's chunks of counted entries; unit, model and property tests
    ├── source_walk.rs  # Newest-first walk over a view's sources for one key
    ├── background_health.rs # Whether flush or compaction is failing, and why
    ├── compaction_backoff.rs # Retry pacing for a failing compaction worker
    ├── disk_check.rs   # Open-time warning when the filesystem is nearly full
    ├── orphan_sweep.rs # Removal of SSTables the manifest does not reference
    └── pending_outputs.rs # Compaction outputs not yet offered to the manifest
```

### Public API surface

`lib.rs` is the public surface. Core types include `Db`, `Snapshot`,
`WriteBatch`, `Options`, `WriteOptions`, `Iter`, `TailingIter`, `Error`,
and `Result`. Extension surfaces such as column families, transactions,
TTL, backups, checkpoints, external SST ingestion, statistics, event
listeners, merge operators, compaction filters, and rate limiting are
also re-exported from `lib.rs`. `regolith::sync` is a public module of
its own: runtime-free async primitives (barging with bounded bypass,
cancellation-safe, no system call but kovan's `sched_yield`) plus
kovan's channels, map, queues and `Atom`. Anything not re-exported is
internal.

### File Size Guidelines

- Under 200 lines: Fine
- 200 to 400 lines: Check if doing one thing
- Over 400 lines: Consider splitting

Several core engine files are intentionally larger today because they
still carry early-stage API and storage-engine code together. Treat that
as refactoring debt: split them only behind focused issues or while
touching a cohesive area with tests, and keep new modules small.

## 5. Naming Conventions

| Thing         | Convention           | Example              |
| ------------- | -------------------- | -------------------- |
| Files/Modules | snake_case           | `block_cache.rs`     |
| Types         | PascalCase           | `WriteBatch`         |
| Functions     | snake_case           | `flush_memtable()`   |
| Constants     | SCREAMING_SNAKE_CASE | `BLOCK_FOOTER_SIZE`  |

## 6. Comments Policy

**Minimal comments. Code should be self-documenting.**

✅ Comment: Non-obvious WHY, safety invariants, on-disk format descriptions, public API docs (`///`)

❌ Don't: What the code does, TODO/FIXME, commented-out code, change history

## 7. Architecture at a Glance

**Write path:** `put`/`delete`/`write` → append to WAL → insert into active memtable → when memtable is full, swap to immutable and flush to an L0 SSTable → background compaction merges L0→L1 and promotes levels (each 10× larger than the last).

**Read path:** active memtable → frozen memtables → L0 SSTables (bloom filter pre-check, overlap possible) → L1..L6 (sorted, non-overlapping, binary search). The first hit wins.

**MVCC:** every write increments a global sequence number. `snapshot()` captures the current seq; reads through a `Snapshot` ignore any key whose seq is greater. This is how point-in-time isolation works without locks on the read path.

**Durability:** `DurabilityMode::Immediate` fsyncs the WAL per write; `Eventual` (default) leaves it to the OS.

## 8. Git Worktree Workflow

```bash
git worktree add ../regolith-foo -b feat/foo    # Work on feature foo
git worktree add ../regolith-bar -b feat/bar    # Work on feature bar
git worktree remove ../regolith-foo             # Clean up
```

Each worktree is isolated, no branch-switching overhead.

## Build Dependencies

- **Rust** 1.90+ (edition 2024) for the library build (see `rust-version` in `Cargo.toml`); CI runs tests and tools on stable Rust.

That's it for the checked-in workspace. No `protoc`, no `cbindgen`, no C/C++ toolchain, no system libraries. Workspace tool dependencies must also parse and build on the MSRV toolchain because CI runs `cargo check --workspace` on Rust 1.90. Tools that need foreign libraries, bindgen-based comparison backends, or newer toolchains should live outside this workspace so the main CI path remains pure Rust.

## Common Commands

```bash
cargo test --workspace                         # Run library, integration, and tool tests
cargo clippy --workspace --all-targets -- -D warnings # Lint all workspace targets (matches CI)
cargo fmt --all -- --check                     # Format check (matches CI)
cargo fmt                                      # Apply formatting
cargo build --release                          # Optimized build (LTO, strip)
```

Use inline `#[cfg(test)]` tests for module-local invariants and `tests/`
for public-API integration, corruption, concurrency, parity, and property
tests. Keep fuzz harnesses under `fuzz/`; they are not part of the normal
workspace test run.

## Before Committing

1. `cargo test --workspace` passes
2. `cargo clippy --workspace --all-targets -- -D warnings` clean
3. `cargo fmt --all -- --check` clean
4. `cargo deny check` clean: surfaces RUSTSEC advisories, license violations, and duplicate crates against the allow-list in `deny.toml`

These are the local gates mirrored in CI (`.github/workflows/ci.yml`).
CI also builds docs with `cargo doc --workspace --no-deps`, checks the
library and tools on the MSRV toolchain with `cargo check --workspace`,
and runs scheduled ignored stress tests.

CI also publishes a coverage summary via `cargo llvm-cov --summary-only` on every push; run it locally with `cargo llvm-cov` (HTML report lands in `target/llvm-cov/html/`) when a change touches a file whose coverage you care about. No hard gate yet; the baseline at the time of writing is ~93% regions / ~91% lines.

## Goal

**A new contributor should be able to read this file, skim `src/lib.rs`, and start making productive changes to the engine within an hour.**

Fast context acquisition → Confident changes → Productive iteration.
