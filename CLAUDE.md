# Development Principles

## 0. What Regolith Is

**regolith** (crate: `regolith`; the version is in `Cargo.toml`) is a pure Rust, embedded LSM-tree key-value store built from scratch. The architecture follows the LevelDB design (memtable → WAL → leveled SSTables → background compaction); the public API is shaped to slot into common embedded-KV abstraction layers so consuming applications can swap regolith in alongside other backends through the same trait.

Early-stage. The public API (`Db`, `Snapshot`, `WriteBatch`, `Options`) is small and stable-shaped, but breakage is allowed pre-1.0.

### Design goals

- **Pure Rust, no FFI**: no C/C++ toolchain, no `bindgen`, no linker surprises in the library or checked-in workspace tools
- **LSM-tree**: write-optimized with level-based background compaction
- **MVCC**: point-in-time consistent reads via global sequence numbers
- **Crash recovery**: WAL whose records carry the offset the last sync made durable, so replay tells a crash from damage
- **Concurrent reads**: an arena-backed skip list memtable (`src/engine/skiplist/`) that readers walk without a lock until a range delete lands in it; a block-cache hit is lock-free
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
├── backup.rs           # BackupEngine and restore flow
├── checkpoint.rs       # Hardlinked checkpoint creation
├── column_family.rs    # Column-family handles and descriptors
├── conflict.rs         # Conflict reasons: Conflict, Access, WriteKind
├── error.rs            # Error enum, Result alias
├── event_listener.rs   # Flush/compaction event callbacks
├── iter.rs             # Public iterator wrappers
├── options.rs          # Options, tuning enums, MergeOperator, CompactionFilter
├── options/            # Options builder methods (builder.rs) and getters (getters.rs)
├── perf_context.rs     # Per-operation performance counters
├── portability.rs      # Atomics shim and the portability tier map
├── rate_limiter.rs     # Token-bucket rate limiter
├── slice.rs            # DbSlice: zero-copy value handle
├── sst_file_writer.rs  # External SSTable writer API
├── statistics.rs       # Tickers, histograms, and properties
├── stream_writer.rs    # StreamingWriter: bounded-memory write stream
├── sync.rs             # Std-backed Mutex, RwLock, Condvar and Gate, swapped for loom's under --cfg loom
├── tailing.rs          # Tailing iterator API
├── testing.rs          # `testing` feature: property checks a caller runs against its own trait implementations
├── transaction.rs      # Optimistic and pessimistic transactions, isolation levels
├── transaction/        # policy.rs (KeyClassifier, key classes), txn_options.rs (TxnOptions),
│                       # scan_range.rs (scan stretches), write_buffer.rs (buffered puts, deletes, merges)
├── ttl.rs              # TTL database wrapper
├── sync/               # Public regolith::sync: async locks, semaphore, notify, event, latch, barrier, once cell
│   ├── queue.rs        # Wait queue and drain role every primitive builds on
│   ├── waiter.rs       # Waiter nodes, their free list, the wake list
│   └── internal.rs     # The engine's private std/loom atomics and locks
├── txn_buffer.rs       # Concurrent write and read-set buffer of one transaction
├── env/                # Env trait and backends: StdEnv, MemEnv, WASI, OPFS; db_lock.rs, open_file_limit.rs
└── engine/
    ├── mod.rs          # RegolithEngine orchestration, read paths, rotation, recovery
    ├── commit/         # Group commit pipeline: ring, leader, conflict check, stall signal
    ├── compaction.rs   # Level/FIFO/universal compaction planning and worker loop
    ├── compaction/     # Per-snapshot-stripe folding of versions and merge chains
    ├── manifest.rs     # VersionSet, VersionEdit log, level tracking
    ├── manifest/       # Manifest tests
    ├── memtable.rs     # Arena-backed skip list memtable plus its range tombstones
    ├── skiplist/       # Insert-only concurrent skip list over the arena
    ├── sstable.rs      # SSTable reader/writer, footer, index block
    ├── sstable/        # SSTable key walks and size limits
    ├── wal.rs          # Write-ahead log writer (format 2), CLOSE, format 1 reading rules
    ├── wal_frame.rs    # WAL format 2: stamp, group record frame, the scan past damage
    ├── wal_replay.rs   # Streaming reader over one WAL file: the O < P rule
    ├── recovery.rs     # Replaying the WALs at open, the dropped-tail report, the rewrite
    ├── arena.rs        # Bump allocator for one memtable
    ├── block.rs        # Data blocks: prefix compression, restart points, varint
    ├── block_cache.rs  # Sharded CLOCK cache for decompressed SSTable blocks
    ├── callback.rs     # Catching a panic in caller code inside a commit and naming its trait
    ├── bloom.rs        # Bloom filter (double-hashed xxh3)
    ├── checksum.rs     # Checksum helpers
    ├── filter_block.rs # SSTable filter region: user-key and prefix bloom filters
    ├── index_block.rs  # Decoded SSTable index blocks
    ├── internal_key.rs # MVCC internal key encoding
    ├── lookup_key.rs   # Inline-first internal key used by every read path
    ├── iterator.rs     # Engine iterator merge logic
    ├── range_tombstone.rs # Range-delete tombstone encoding
    ├── read_view.rs    # The published set of memtables and version a reader loads
    ├── read_horizon.rs # Newest sequence whose data is durable and applied
    ├── snapshot_registry.rs # Active snapshot sequence tracking
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
