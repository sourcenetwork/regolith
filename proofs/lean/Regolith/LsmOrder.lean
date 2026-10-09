/-!
# LsmOrder: the read order of the LSM tree, the L0 closure rule, one view per batch, flush order, ingest placement, overlap demotion, binary search

This file backs two TLA+ models in `proofs/tla`:

* `LsmOrder.tla`, invariant `ReadNewest` (configurations `MC_LsmOrder_Green`
  and `MC_LsmOrder_Red_Intersect`). Defect E1: `compact_range` at L0 must
  pick a closed input set. The same model's flush order, ingest placement,
  overlap demotion (E14, D13) and binary search configurations
  (`MC_LsmOrder_*_Flush*`, `*_Ingest*`, `*_Demote*`, `*_NoDemotion`, and
  the invariant `BisectIsScan`) are backed by items 7 to 10 below.
* `BatchRead.tla`, invariants `BatchConsistent` and `BatchExact`
  (configurations `MC_BatchRead_*`). Defect E6: a batch read resolves every
  key against one view.

TLC checks those models for a few keys and versions. The theorems here hold
for every number of keys, versions, L0 files and batch keys.

What is proved, in plain words:

1. `read_newest`: a read asks the sources in read order (the memtable, then
   the L0 files newest first, then L1) and the first source that holds a
   version of the key the snapshot may see answers. That answer is the
   newest such version anywhere, provided every source is newer than every
   source after it (`Ordered`).
2. `put_ordered` and `flush_ordered`: a write and a flush keep the sources
   ordered.
3. `compact_closed_preserves_order` and `compact_closed_preserves_reads`:
   moving a closed set of L0 files into L1 keeps the sources ordered and
   changes no read.
4. `pickL0_closed`, `pickL0_covers` and `compact_range_reads_newest`: the
   closure picker returns a closed set that contains every L0 file meeting
   the range, so `compact_range` changes no read.
5. `intersect_only_breaks_reads`: picking only the L0 files that meet the
   range can make a read return an older version. This is the RED
   configuration, as a concrete counterexample.
6. `batch_one_view_point_in_time` and `view_per_key_breaks_batch`: a batch
   resolved against the view it began with answers every key as of one
   point in time; a batch that loads a view per key can answer a key from a
   view a flush has already thinned.
7. `install_oldest_same_order`, `install_oldest_all` and
   `install_oldest_all_reads`: installing the oldest frozen memtables, one by
   one, as the newest L0 files (every flush off the commit path, E9,
   whichever thread runs it) leaves the read order and every read as it was;
   `install_newer_breaks_reads` is the RED case of installing a newer one
   first.
8. `ingest_ordered`: an ingested file, newer than everything, placed where
   no source read before it shares a key, keeps the sources ordered;
   `ingest_below_holder_breaks_reads` is the RED case.
9. `demote_reads_newest`: demoting every level from L1 down to an
   overlapping one to the end of L0, in age order, keeps the read order and
   every read; `noShared_level_ordered` says the overlapping level's tables
   are ordered in any order; `demote_level_only_breaks_reads` is the RED
   case of demoting the overlapping level alone.
10. `bsearch_eq_scan` and `level_read_bsearch`: on a level in key order
   whose tables do not overlap, binary search finds the table a linear scan
   finds, and reads what a linear read of the level reads.

How to read the Lean: `def` defines a function or a property, `theorem`
states a fact and its proof follows `:= by`. Lines starting with `--` are
comments. Inside a proof, each step is commented with what it establishes.
-/

namespace Regolith.LsmOrder

/-! ## The objects -/

/-
Keys and sequence numbers are both natural numbers (`Nat`).

* A user key is a `Nat`. The engine compares user keys bytewise; only their
  order matters here, so a natural number stands for one. Variables named
  `k`, `lo`, `hi` and lists named `hull` hold keys.
* A sequence number is a `Nat`. Every write takes a fresh, larger one, so a
  larger sequence means a newer version. Variables named `s`, `t`, `v`, `w`
  and `snap` hold sequences; `snap` is the snapshot a read is taken at.

They are kept as plain `Nat` rather than named aliases so that Lean's
arithmetic decision procedure (`omega`) sees them as numbers.
-/

/-- One version of a key: the pair `(key, sequence it was written at)`. -/
abbrev Version := Nat × Nat

/-- A source a read consults: the memtable, one L0 file, or the L1 run.
Here it is the list of versions it holds; the order inside it does not
matter to anything below. -/
abbrev Source := List Version

/-! ## One source's answer -/

/-- `newestIn src k snap` is one source's answer to a point read of key `k`
at snapshot `snap`: the sequence of the newest version of `k` in `src` whose
sequence is at most `snap`, or `none` when `src` holds no such version. -/
def newestIn : Source → Nat → Nat → Option Nat
  -- An empty source holds nothing.
  | [], _, _ => none
  -- A first version `(k', s)`, followed by the versions `rest`.
  | (k', s) :: rest, k, snap =>
    -- Is the first version one of `k`'s, and may the snapshot see it?
    if k' = k ∧ s ≤ snap then
      -- Yes: the answer is the larger of `s` and whatever `rest` answers.
      some (match newestIn rest k snap with
        | none => s
        | some w => max s w)
    else
      -- No: the answer is whatever `rest` answers.
      newestIn rest k snap

/-- A source answers `none` exactly when every version of `k` it holds is
newer than the snapshot, so the snapshot may see none of them. -/
theorem newestIn_eq_none {src : Source} {k : Nat} {snap : Nat} :
    newestIn src k snap = none ↔ ∀ s, (k, s) ∈ src → snap < s := by
  -- By induction on the list of versions.
  induction src with
  | nil =>
    -- An empty source answers `none` and holds no version: both sides hold.
    simp [newestIn]
  | cons hd rest ih =>
    -- Name the first version `(k', s)`.
    obtain ⟨k', s⟩ := hd
    by_cases h : k' = k ∧ s ≤ snap
    · -- The first version is visible. The answer is `some`, so the left
      -- side is false; and that version is a visible one of `k`, so the
      -- right side is false too.
      rw [newestIn, ite_eq_left h]
      obtain ⟨hk, hs⟩ := h
      subst k'
      constructor
      · intro hc
        cases hc
      · intro hall
        have := hall s List.mem_cons_self
        omega
    · -- The first version is not visible, so the answer is `rest`'s.
      rw [newestIn, ite_eq_right h, ih]
      constructor
      · -- Every version of `k` in `rest` is too new; the first one is either
        -- another key's or too new as well.
        intro hr t ht
        rcases List.mem_cons.mp ht with he | hm
        · -- `(k, t)` is the first version `(k', s)`.
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          omega
        · exact hr t hm
      · -- Dropping the first version keeps the statement for `rest`.
        intro hall t ht
        exact hall t (List.mem_cons_of_mem _ ht)

/-- When a source answers `some v`, it holds the version `(k, v)`, the
snapshot may see it (`v ≤ snap`), and every other version of `k` the
snapshot may see in that source is no newer. -/
theorem newestIn_eq_some {src : Source} {k : Nat} {snap v : Nat}
    -- The source answered `some v`.
    (h : newestIn src k snap = some v) :
    (k, v) ∈ src ∧ v ≤ snap ∧ ∀ s, (k, s) ∈ src → s ≤ snap → s ≤ v := by
  -- By induction on the list of versions, for every answer `v`.
  induction src generalizing v with
  | nil =>
    -- An empty source answers `none`, never `some v`.
    simp [newestIn] at h
  | cons hd rest ih =>
    obtain ⟨k', s⟩ := hd
    by_cases hv : k' = k ∧ s ≤ snap
    · -- The first version `(k, s)` is visible.
      rw [newestIn, ite_eq_left hv] at h
      obtain ⟨hk, hs⟩ := hv
      subst k'
      -- What does `rest` answer?
      cases hr : newestIn rest k snap with
      | none =>
        -- `rest` holds nothing visible, so the answer is `s` itself.
        rw [hr] at h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨List.mem_cons_self, hs, ?_⟩
        intro t ht hts
        rcases List.mem_cons.mp ht with he | hm
        · -- The first version: `t = s`.
          simp only [Prod.mk.injEq] at he
          omega
        · -- A version in `rest`: impossible, `rest` holds nothing visible.
          have := (newestIn_eq_none.mp hr) t hm
          omega
      | some w =>
        -- `rest` answers `w`, so the answer is `max s w`.
        rw [hr] at h
        simp only [Option.some.injEq] at h
        obtain ⟨hw, hwle, hwmax⟩ := ih hr
        refine ⟨?_, by omega, ?_⟩
        · -- `max s w` is one of the two, and both are held.
          by_cases hsw : w ≤ s
          · have : v = s := by omega
            subst this
            exact List.mem_cons_self
          · have : v = w := by omega
            subst this
            exact List.mem_cons_of_mem _ hw
        · -- Every visible version is at most `s` or at most `w`.
          intro t ht hts
          rcases List.mem_cons.mp ht with he | hm
          · simp only [Prod.mk.injEq] at he
            omega
          · have := hwmax t hm hts
            omega
    · -- The first version is not visible: the answer is `rest`'s.
      rw [newestIn, ite_eq_right hv] at h
      obtain ⟨hw, hwle, hwmax⟩ := ih h
      refine ⟨List.mem_cons_of_mem _ hw, hwle, ?_⟩
      intro t ht hts
      rcases List.mem_cons.mp ht with he | hm
      · -- `(k, t)` is the first version, which is visible: a contradiction.
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact absurd ⟨rfl, hts⟩ hv
      · exact hwmax t hm hts

/-- Versions newer than the snapshot change nothing a snapshot reads:
putting versions that are all newer than `snap` in front of a source
leaves its answer at `snap` unchanged. This is what makes a write after a
snapshot invisible to it, here and in `Publication.lean`. -/
theorem newestIn_append_invisible {extra src : Source} {k : Nat} {snap : Nat}
    -- Every added version is newer than the snapshot.
    (hnew : ∀ e ∈ extra, snap < e.2) :
    newestIn (extra ++ src) k snap = newestIn src k snap := by
  -- By induction on the added versions.
  induction extra with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨k', s⟩ := hd
    -- The first added version is too new to be visible.
    have hs : snap < s := hnew (k', s) List.mem_cons_self
    have hnot : ¬ (k' = k ∧ s ≤ snap) := by omega
    -- So the answer is that of the rest, which the induction covers.
    rw [List.cons_append, newestIn, ite_eq_right hnot]
    exact ih (fun e he => hnew e (List.mem_cons_of_mem _ he))

/-! ## The read order -/

/-- `Holds srcs v`: some source in `srcs` holds the version `v`. -/
def Holds (srcs : List Source) (v : Version) : Prop := ∃ src ∈ srcs, v ∈ src

/-- `IsNewest srcs k snap v`: `v` is the sequence of the newest version of
`k` that a snapshot at `snap` may see, across all of `srcs`. This is what a
correct read returns. -/
def IsNewest (srcs : List Source) (k : Nat) (snap v : Nat) : Prop :=
  -- Some source holds `(k, v)` ...
  Holds srcs (k, v) ∧
  -- ... the snapshot may see it ...
  v ≤ snap ∧
  -- ... and every version of `k` the snapshot may see is no newer.
  ∀ s, Holds srcs (k, s) → s ≤ snap → s ≤ v

/-- `read srcs k snap` is the engine's point read of `k` at snapshot
`snap`. It asks the sources in read order, and the first one holding a
version the snapshot may see answers with its newest such version. `none`
means no source holds one: the key reads as absent. -/
def read : List Source → Nat → Nat → Option Nat
  -- No source left: the key is absent at this snapshot.
  | [], _, _ => none
  -- Ask the next source; stop at its answer if it has one.
  | src :: rest, k, snap =>
    match newestIn src k snap with
    | some v => some v
    | none => read rest k snap

/-- `Newer a b`: for every key, every version `a` holds is newer than every
version of the same key `b` holds. The memtable is newer than every L0
file, a newer L0 file is newer than an older one, and every L0 file is
newer than L1. -/
def Newer (a b : Source) : Prop := ∀ k s t, (k, s) ∈ a → (k, t) ∈ b → t < s

/-- `Ordered srcs`: every source is `Newer` than every source after it in
read order. `List.Pairwise R l` means `R x y` for every `x` that comes
before `y` in `l`. -/
def Ordered (srcs : List Source) : Prop := srcs.Pairwise Newer

/-- `newerB a b` computes `Newer a b`: for every version in `a` and every
version in `b`, either the keys differ or `b`'s version is older. It lets
Lean check `Ordered` on concrete examples by evaluation. -/
def newerB (a b : Source) : Bool :=
  a.all fun x => b.all fun y => x.1 != y.1 || decide (y.2 < x.2)

/-- The computation `newerB` agrees with the definition `Newer`. -/
theorem newer_iff_newerB {a b : Source} : Newer a b ↔ newerB a b = true := by
  -- Turn the computation into the statement "for every `x` in `a` and `y`
  -- in `b`, the keys differ or `y.2 < x.2`".
  simp only [Newer, newerB, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq]
  constructor
  · -- From `Newer`: two versions with the same key are ordered.
    intro h x hx y hy
    by_cases hk : x.1 = y.1
    · right
      obtain ⟨k, s⟩ := x
      obtain ⟨k', t⟩ := y
      simp only at hk
      subst hk
      exact h k s t hx hy
    · left
      exact hk
  · -- To `Newer`: the keys of `(k, s)` and `(k, t)` are equal, so the
    -- second disjunct must hold.
    intro h k s t hs ht
    rcases h (k, s) hs (k, t) ht with hne | hlt
    · exact absurd rfl hne
    · exact hlt

/-- `Newer` is decidable, through `newerB`. -/
instance : DecidableRel Newer := fun a b =>
  decidable_of_iff (newerB a b = true) newer_iff_newerB.symm

/-- A read answers `none` exactly when no source holds a version of `k`
the snapshot may see. This needs no ordering. -/
theorem read_eq_none {srcs : List Source} {k : Nat} {snap : Nat} :
    read srcs k snap = none ↔ ∀ s, Holds srcs (k, s) → snap < s := by
  induction srcs with
  | nil =>
    -- No sources: the read is `none` and nothing is held.
    simp [read, Holds]
  | cons src rest ih =>
    -- Split on the first source's answer.
    cases hn : newestIn src k snap with
    | some v =>
      -- It holds a visible version, so the read is `some` and the right
      -- side fails at that version.
      simp only [read, hn]
      obtain ⟨hv, hvle, -⟩ := newestIn_eq_some hn
      constructor
      · -- `some v = none` is impossible.
        intro hc
        cases hc
      · -- `(k, v)` is held and visible, against the right side.
        intro hall
        have := hall v ⟨src, List.mem_cons_self, hv⟩
        omega
    | none =>
      -- It holds nothing visible: the read is `rest`'s.
      simp only [read, hn]
      rw [ih]
      constructor
      · -- Nothing visible in `rest`, nor in the first source.
        intro hr t ⟨s', hs', ht⟩
        rcases List.mem_cons.mp hs' with rfl | hm
        · exact newestIn_eq_none.mp hn t ht
        · exact hr t ⟨s', hm, ht⟩
      · -- Nothing visible anywhere means nothing visible in `rest`.
        intro hall t ⟨s', hs', ht⟩
        exact hall t ⟨s', List.mem_cons_of_mem _ hs', ht⟩

/-- **The read order returns the newest visible version.** On ordered
sources, a read that answers `some v` answers the newest version of `k` the
snapshot may see. -/
theorem read_some_newest {srcs : List Source} {k : Nat} {snap v : Nat}
    -- The sources are ordered: each newer than every one after it.
    (hord : Ordered srcs)
    -- The read answered `some v`.
    (h : read srcs k snap = some v) :
    IsNewest srcs k snap v := by
  induction srcs with
  | nil =>
    -- No sources answer `none`, never `some v`.
    simp [read] at h
  | cons src rest ih =>
    -- Ordered splits into: the first source is newer than each later one,
    -- and the later ones are ordered among themselves.
    unfold Ordered at hord
    rw [List.pairwise_cons] at hord
    obtain ⟨hhead, hrest⟩ := hord
    cases hn : newestIn src k snap with
    | some w =>
      -- The first source answered `w`, so the read is `w`.
      simp only [read, hn, Option.some.injEq] at h
      subst h
      obtain ⟨hw, hwle, hwmax⟩ := newestIn_eq_some hn
      refine ⟨⟨src, List.mem_cons_self, hw⟩, hwle, ?_⟩
      intro s ⟨t, ht, hs⟩ hsle
      rcases List.mem_cons.mp ht with rfl | hm
      · -- Another version in the first source: no newer, by its answer.
        exact hwmax s hs hsle
      · -- A version in a later source: older, since the first is newer.
        exact Nat.le_of_lt (hhead t hm k w s hw hs)
    | none =>
      -- The first source holds nothing visible: the read is `rest`'s.
      simp only [read, hn] at h
      obtain ⟨⟨t, ht, hv⟩, hvle, hvmax⟩ := ih hrest h
      refine ⟨⟨t, List.mem_cons_of_mem _ ht, hv⟩, hvle, ?_⟩
      intro s ⟨t', ht', hs⟩ hsle
      rcases List.mem_cons.mp ht' with rfl | hm
      · -- A visible version in the first source would contradict `none`.
        have := newestIn_eq_none.mp hn s hs
        omega
      · exact hvmax s ⟨t', hm, hs⟩ hsle

/-- **`read_newest`.** On ordered sources a read answers `some v` exactly
when `v` is the newest version of `k` the snapshot may see. With
`read_eq_none` this pins the read down completely. -/
theorem read_newest {srcs : List Source} {k : Nat} {snap v : Nat}
    -- The sources are ordered.
    (hord : Ordered srcs) :
    read srcs k snap = some v ↔ IsNewest srcs k snap v := by
  constructor
  · -- One direction is `read_some_newest`.
    exact read_some_newest hord
  · intro hv
    -- The read is `none` or `some w`.
    cases hr : read srcs k snap with
    | none =>
      -- `none` means nothing visible is held, but `(k, v)` is.
      have := read_eq_none.mp hr v hv.1
      have := hv.2.1
      omega
    | some w =>
      -- `w` is the newest too, and the newest is unique: `v ≤ w ≤ v`.
      have hw := read_some_newest hord hr
      have h1 := hv.2.2 w hw.1 hw.2.1
      have h2 := hw.2.2 v hv.1 hv.2.1
      have : w = v := by omega
      rw [this]

/-- Two ordered read orders that hold the same versions answer every read
the same. This is how a compaction is shown to change no read: it only
moves versions between sources. -/
theorem read_eq_of_same_versions {a b : List Source}
    -- Both read orders are ordered.
    (ha : Ordered a) (hb : Ordered b)
    -- They hold exactly the same versions.
    (hsame : ∀ v, Holds a v ↔ Holds b v)
    (k : Nat) (snap : Nat) :
    read a k snap = read b k snap := by
  cases hr : read a k snap with
  | none =>
    -- Nothing visible in `a`, hence nothing visible in `b`.
    symm
    exact read_eq_none.mpr fun s hs => read_eq_none.mp hr s ((hsame (k, s)).mpr hs)
  | some v =>
    -- `v` is the newest in `a`; the same versions make it the newest in `b`.
    obtain ⟨hv, hvle, hvmax⟩ := read_some_newest ha hr
    symm
    exact (read_newest hb).mpr
      ⟨(hsame _).mp hv, hvle, fun s hs hsle => hvmax s ((hsame _).mpr hs) hsle⟩

/-! ## Writes and flushes keep the order -/

/-- A put of `(k, s)` into the memtable keeps the read order ordered, when
`s` is newer than every version already held: the engine hands out a
fresh, larger sequence for every write. -/
theorem put_ordered {mem : Source} {rest : List Source} {k : Nat} {s : Nat}
    -- The read order before the write is ordered.
    (hord : Ordered (mem :: rest))
    -- The new sequence is larger than every sequence already held.
    (hfresh : ∀ v, Holds (mem :: rest) v → v.2 < s) :
    Ordered (((k, s) :: mem) :: rest) := by
  unfold Ordered at *
  rw [List.pairwise_cons] at *
  obtain ⟨hhead, hrest⟩ := hord
  refine ⟨?_, hrest⟩
  -- The grown memtable is newer than every later source.
  intro src hsrc k' s' t hs ht
  rcases List.mem_cons.mp hs with he | hm
  · -- The new version: older versions are below `s` by freshness.
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact hfresh (k', t) ⟨src, List.mem_cons_of_mem _ hsrc, ht⟩
  · -- An old memtable version: newer than `src` as before.
    exact hhead src hsrc k' s' t hm ht

/-- A flush turns the memtable into the newest L0 file and starts an empty
memtable. The order is kept: the empty memtable holds nothing, so it is
vacuously newer than everything. -/
theorem flush_ordered {mem : Source} {rest : List Source}
    -- The read order before the flush is ordered.
    (hord : Ordered (mem :: rest)) :
    Ordered ([] :: mem :: rest) := by
  unfold Ordered at *
  refine List.Pairwise.cons ?_ hord
  -- The empty memtable holds no version, so there is nothing to compare.
  intro src _ k s t hs _
  cases hs

/-! ## Compaction of picked L0 files -/

/-- An L0 slot: one L0 file, and whether `compact_range` picked it as an
input. L0 is a list of slots, newest file first. -/
abbrev Slot := Source × Bool

/-- The keys a file holds. Its key range runs from the least to the
greatest of them. -/
def keysOf (f : Source) : List Nat := f.map Prod.fst

/-- Every key of every picked file. The picked set's key range, its hull,
runs from the least to the greatest of these. -/
def hullKeys (l0 : List Slot) : List Nat :=
  ((l0.filter Prod.snd).map fun x => keysOf x.1).flatten

/-- `overlaps f hull`: the key range of file `f` meets the picked set's key
range. Two ranges `[a, b]` and `[c, d]` meet exactly when `a ≤ d` and
`c ≤ b`, so this asks for a key of `f` at or below some key of the hull,
and a key of the hull at or below some key of `f`. It is the interval test
`min f ≤ max hull ∧ min hull ≤ max f`, written so that an empty file or an
empty hull overlaps nothing. -/
def overlaps (f : Source) (hull : List Nat) : Bool :=
  (f.any fun e => hull.any fun d => decide (e.1 ≤ d)) &&
  (hull.any fun c => f.any fun e => decide (c ≤ e.1))

/-- A file holding a key that a picked file also holds overlaps the hull:
the shared key lies in both ranges. -/
theorem overlaps_of_shared {f : Source} {hull : List Nat} {k : Nat} {s : Nat}
    -- `f` holds a version of `k`.
    (hf : (k, s) ∈ f)
    -- `k` is a key of the picked set.
    (hk : k ∈ hull) :
    overlaps f hull = true := by
  simp only [overlaps, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq]
  -- The shared key witnesses both comparisons, as `k ≤ k`.
  exact ⟨⟨(k, s), hf, k, hk, Nat.le_refl k⟩, ⟨k, hk, (k, s), hf, Nat.le_refl k⟩⟩

/-- A key of a picked file is a key of the hull. -/
theorem mem_hullKeys {l0 : List Slot} {x : Slot} {k : Nat} {s : Nat}
    -- `x` is an L0 slot ...
    (hx : x ∈ l0)
    -- ... that compaction picked ...
    (hpick : x.2 = true)
    -- ... and its file holds a version of `k`.
    (hk : (k, s) ∈ x.1) :
    k ∈ hullKeys l0 := by
  simp only [hullKeys, keysOf, List.mem_flatten, List.mem_map, List.mem_filter]
  -- The list of `x`'s keys is one of the flattened lists, and holds `k`.
  exact ⟨_, ⟨x, ⟨hx, hpick⟩, rfl⟩, List.mem_map.mpr ⟨(k, s), hk, rfl⟩⟩

/-- The closure rule for one pair of slots, `newer` coming before `older`
in L0: if the newer file is picked and the older one is not, the older
file's key range must not meet the picked set's range `hull`. Otherwise
the older file could hold an older version of a key whose newer version
leaves for L1, and a read would find the older one first. -/
def ClosureRule (hull : List Nat) (newer older : Slot) : Prop :=
  newer.2 = true → older.2 = false → overlaps older.1 hull = false

/-- `Closed l0`: the picked set obeys the closure rule for every pair of L0
slots, newer before older. -/
def Closed (l0 : List Slot) : Prop := l0.Pairwise (ClosureRule (hullKeys l0))

/-- The L0 files a compaction leaves in place, in their L0 order. -/
def remaining (l0 : List Slot) : List Source := (l0.filter fun x => !x.2).map Prod.fst

/-- Every version of every picked file: what the compaction merges into L1. -/
def moved (l0 : List Slot) : Source := ((l0.filter Prod.snd).map Prod.fst).flatten

/-- The read order before the compaction: the memtable, the L0 files newest
first, then L1. -/
def before (mem : Source) (l0 : List Slot) (l1 : Source) : List Source :=
  mem :: (l0.map Prod.fst ++ [l1])

/-- The read order after the picked files are compacted into L1.

L1 is one sorted run. Merging the picked files with the L1 files they
overlap and writing the result back leaves L1 holding its old versions
plus the picked ones; which L1 files were rewritten is invisible to a
read. A compaction may also drop a version no registered snapshot can see;
the reads here are at snapshots whose versions are kept, so the model
keeps every version. -/
def after (mem : Source) (l0 : List Slot) (l1 : Source) : List Source :=
  mem :: (remaining l0 ++ [l1 ++ moved l0])

/-- A remaining file is the file of an unpicked L0 slot. -/
theorem mem_remaining {l0 : List Slot} {f : Source} :
    f ∈ remaining l0 ↔ ∃ x ∈ l0, x.2 = false ∧ x.1 = f := by
  simp only [remaining, List.mem_map, List.mem_filter, Bool.not_eq_true']
  -- Both sides say: some slot of `l0`, unpicked, holds the file `f`.
  constructor
  · rintro ⟨x, ⟨hx, hun⟩, rfl⟩
    exact ⟨x, hx, hun, rfl⟩
  · rintro ⟨x, hx, hun, rfl⟩
    exact ⟨x, ⟨hx, hun⟩, rfl⟩

/-- A moved version is a version of a picked L0 file. -/
theorem mem_moved {l0 : List Slot} {v : Version} :
    v ∈ moved l0 ↔ ∃ x ∈ l0, x.2 = true ∧ v ∈ x.1 := by
  -- Both sides say: some slot of `l0`, picked, holds the version `v`.
  simp only [moved, List.mem_flatten, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨_, ⟨x, ⟨hx, hp⟩, rfl⟩, hv⟩
    exact ⟨x, hx, hp, hv⟩
  · rintro ⟨x, hx, hp, hv⟩
    exact ⟨_, ⟨x, ⟨hx, hp⟩, rfl⟩, hv⟩

/-- Two distinct members of a list satisfying `Pairwise R` are related one
way or the other, depending on which comes first. -/
theorem pairwise_either {α : Type} {R : α → α → Prop} {a b : α} :
    ∀ {l : List α}, l.Pairwise R → a ∈ l → b ∈ l → a ≠ b → R a b ∨ R b a
  | [], _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: xs, hp, ha, hb, hne => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · -- `a` and `b` would both be the head: excluded.
        exact absurd rfl hne
      · -- `a` is the head and `b` comes later.
        exact Or.inl (hp.1 b hb')
    · rcases List.mem_cons.mp hb with rfl | hb'
      · -- `b` is the head and `a` comes later.
        exact Or.inr (hp.1 a ha')
      · -- Both are in the tail.
        exact pairwise_either hp.2 ha' hb' hne

/-- **Compacting a closed set keeps the read order ordered.** -/
theorem compact_closed_preserves_order {mem l1 : Source} {l0 : List Slot}
    -- The read order before the compaction is ordered.
    (hord : Ordered (before mem l0 l1))
    -- The picked set is closed.
    (hclosed : Closed l0) :
    Ordered (after mem l0 l1) := by
  unfold Ordered before at hord
  rw [List.pairwise_cons, List.pairwise_append] at hord
  -- hmem: the memtable is newer than every L0 file and than L1.
  -- hl0: the L0 files are ordered among themselves.
  -- hl1: every L0 file is newer than L1.
  obtain ⟨hmem, hl0, -, hl1⟩ := hord
  rw [List.pairwise_map] at hl0
  -- The L0 order carries both facts per pair: newer, and the closure rule.
  have hboth := hl0.and hclosed
  -- Every L0 file is newer than L1, stated per slot.
  have hfile_l1 : ∀ x ∈ l0, Newer x.1 l1 := fun x hx =>
    hl1 x.1 (List.mem_map_of_mem hx) l1 List.mem_cons_self
  -- The memtable is newer than every L0 file, stated per slot.
  have hmem_file : ∀ x ∈ l0, Newer mem x.1 := fun x hx =>
    hmem x.1 (List.mem_append_left _ (List.mem_map_of_mem hx))
  -- The memtable is newer than L1.
  have hmem_l1 : Newer mem l1 := hmem l1 (List.mem_append_right _ List.mem_cons_self)
  unfold Ordered after
  rw [List.pairwise_cons, List.pairwise_append]
  refine ⟨?_, ?_, List.pairwise_singleton _ _, ?_⟩
  · -- The memtable is newer than every remaining file and than the new L1.
    intro src hsrc k s t hs ht
    rcases List.mem_append.mp hsrc with hrem | hl1'
    · -- A remaining file is an L0 file.
      obtain ⟨x, hx, -, rfl⟩ := mem_remaining.mp hrem
      exact hmem_file x hx k s t hs ht
    · -- The new L1 holds old L1 versions and moved L0 versions.
      rcases List.mem_singleton.mp hl1' with rfl
      rcases List.mem_append.mp ht with ht1 | htm
      · exact hmem_l1 k s t hs ht1
      · obtain ⟨y, hy, -, hty⟩ := mem_moved.mp htm
        exact hmem_file y hy k s t hs hty
  · -- The remaining files keep their L0 order, a sub-list of an ordered one.
    unfold remaining
    rw [List.pairwise_map]
    exact hl0.sublist List.filter_sublist
  · -- Every remaining file is newer than the new L1. This is where the
    -- closure rule is used.
    intro src hsrc l1' hl1' k s t hs ht
    obtain ⟨x, hx, hxkeep, rfl⟩ := mem_remaining.mp hsrc
    rcases List.mem_singleton.mp hl1' with rfl
    rcases List.mem_append.mp ht with ht1 | htm
    · -- An old L1 version: every L0 file is newer than L1.
      exact hfile_l1 x hx k s t hs ht1
    · -- A version `(k, t)` of a picked file `y`.
      obtain ⟨y, hy, hypick, hty⟩ := mem_moved.mp htm
      -- `x` is kept and `y` is picked, so they are different slots.
      have hne : x ≠ y := by
        intro hxy
        rw [hxy, hypick] at hxkeep
        cases hxkeep
      rcases pairwise_either hboth hx hy hne with ⟨hxy, -⟩ | ⟨-, hrule⟩
      · -- `x` comes before `y`: it is newer, so `t < s`.
        exact hxy k s t hs hty
      · -- `y` comes before `x`: the closure rule says `x` does not overlap
        -- the hull. Yet `x` holds `k`, which picked `y` also holds: a
        -- contradiction, so this case cannot happen.
        have hov := hrule hypick hxkeep
        have : overlaps x.1 (hullKeys l0) = true :=
          overlaps_of_shared hs (mem_hullKeys hy hypick hty)
        rw [hov] at this
        cases this

/-- A compaction moves versions and loses none: the read orders before and
after hold the same versions. -/
theorem compact_same_versions {mem l1 : Source} {l0 : List Slot} (v : Version) :
    Holds (after mem l0 l1) v ↔ Holds (before mem l0 l1) v := by
  unfold Holds after before
  constructor
  · -- From after to before: find the source that held `v` before.
    rintro ⟨src, hsrc, hv⟩
    rcases List.mem_cons.mp hsrc with rfl | hsrc'
    · -- The memtable is in both.
      exact ⟨src, List.mem_cons_self, hv⟩
    rcases List.mem_append.mp hsrc' with hrem | hl1'
    · -- A remaining file is an L0 file.
      obtain ⟨x, hx, -, rfl⟩ := mem_remaining.mp hrem
      exact ⟨x.1, List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem hx)), hv⟩
    · rcases List.mem_singleton.mp hl1' with rfl
      rcases List.mem_append.mp hv with hv1 | hvm
      · -- An old L1 version is in the old L1.
        exact ⟨l1, List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self), hv1⟩
      · -- A moved version is in its picked L0 file.
        obtain ⟨y, hy, -, hvy⟩ := mem_moved.mp hvm
        exact ⟨y.1, List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem hy)), hvy⟩
  · -- From before to after: find the source that holds `v` after.
    rintro ⟨src, hsrc, hv⟩
    rcases List.mem_cons.mp hsrc with rfl | hsrc'
    · -- The memtable is in both.
      exact ⟨src, List.mem_cons_self, hv⟩
    rcases List.mem_append.mp hsrc' with hl0' | hl1'
    · -- An L0 file either remains or moved into L1.
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl0'
      cases hp : x.2 with
      | false =>
        exact ⟨x.1, List.mem_cons_of_mem _
          (List.mem_append_left _ (mem_remaining.mpr ⟨x, hx, hp, rfl⟩)), hv⟩
      | true =>
        exact ⟨l1 ++ moved l0, List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self),
          List.mem_append_right _ (mem_moved.mpr ⟨x, hx, hp, hv⟩)⟩
    · -- The old L1 is inside the new L1.
      rcases List.mem_singleton.mp hl1' with rfl
      exact ⟨src ++ moved l0, List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self),
        List.mem_append_left _ hv⟩

/-- **Compacting a closed set changes no read.** For every key and every
snapshot, the read after the compaction answers what it answered before. -/
theorem compact_closed_preserves_reads {mem l1 : Source} {l0 : List Slot}
    -- The read order before the compaction is ordered.
    (hord : Ordered (before mem l0 l1))
    -- The picked set is closed.
    (hclosed : Closed l0) (k : Nat) (snap : Nat) :
    read (after mem l0 l1) k snap = read (before mem l0 l1) k snap :=
  -- Both orders are ordered and hold the same versions.
  read_eq_of_same_versions (compact_closed_preserves_order hord hclosed) hord
    compact_same_versions k snap

/-! ## The closure picker -/

/-- One pass of the closure rule over L0, newest file first. `seen` says
whether some newer slot is already picked. A slot becomes picked if it was,
or if a newer slot is picked and its file's range meets `hull`. -/
def stepWith (hull : List Nat) : Bool → List Slot → List Slot
  | _, [] => []
  | seen, (f, b) :: rest =>
    (f, b || (seen && overlaps f hull)) :: stepWith hull (seen || b) rest

/-- One closure step: a pass against the current picked set's hull. -/
def step (l0 : List Slot) : List Slot := stepWith (hullKeys l0) false l0

/-- Repeat closure steps until one changes nothing, at most `n` times. -/
def closeFuel : Nat → List Slot → List Slot
  | 0, l0 => l0
  | n + 1, l0 => if step l0 = l0 then l0 else closeFuel n (step l0)

/-- The closure: enough steps to reach the fixpoint, since each step that
changes something picks at least one more file (`closeFuel_fixpoint`). -/
def close (l0 : List Slot) : List Slot := closeFuel (l0.length + 1) l0

/-- `intersects f lo hi`: file `f` holds a key in `[lo, hi]`, the range
`compact_range` was asked for. -/
def intersects (f : Source) (lo hi : Nat) : Bool :=
  f.any fun e => decide (lo ≤ e.1 ∧ e.1 ≤ hi)

/-- The starting pick: the L0 files that intersect the range. This alone is
what the defective picker compacts. -/
def initialPick (lo hi : Nat) (files : List Source) : List Slot :=
  files.map fun f => (f, intersects f lo hi)

/-- The fixed picker: the starting pick, closed under the closure rule. -/
def pickL0 (lo hi : Nat) (files : List Source) : List Slot :=
  close (initialPick lo hi files)

/-- A pass keeps the files and their order; it only changes flags. -/
theorem stepWith_files (hull : List Nat) :
    ∀ (seen : Bool) (l : List Slot), (stepWith hull seen l).map Prod.fst = l.map Prod.fst
  | _, [] => rfl
  | seen, (f, b) :: rest => by
    -- The head keeps its file `f`; the rest keeps its files by induction.
    simp only [stepWith, List.map_cons]
    rw [stepWith_files hull (seen || b) rest]

/-- A pass keeps the number of slots. -/
theorem stepWith_length (hull : List Nat) (seen : Bool) (l : List Slot) :
    (stepWith hull seen l).length = l.length := by
  -- Same files, so same length.
  have := congrArg List.length (stepWith_files hull seen l)
  simpa using this

/-- A pass never unpicks a file. -/
theorem stepWith_keeps_picked (hull : List Nat) :
    ∀ (seen : Bool) (l : List Slot) (f : Source), (f, true) ∈ l → (f, true) ∈ stepWith hull seen l
  | _, [], _, h => absurd h List.not_mem_nil
  | seen, (g, b) :: rest, f, h => by
    simp only [stepWith]
    rcases List.mem_cons.mp h with he | hm
    · -- The picked slot is the head: its flag stays `true`.
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp
    · exact List.mem_cons_of_mem _ (stepWith_keeps_picked hull _ rest f hm)

/-- A pass that changes the list picks strictly more files; one that does
not change it picks at least as many. `countP Prod.snd` counts the picked
slots. -/
theorem stepWith_count (hull : List Nat) :
    ∀ (seen : Bool) (l : List Slot),
      l.countP Prod.snd ≤ (stepWith hull seen l).countP Prod.snd ∧
      (stepWith hull seen l ≠ l → l.countP Prod.snd < (stepWith hull seen l).countP Prod.snd)
  | _, [] => by simp [stepWith]
  | seen, (f, b) :: rest => by
    -- The claim for the rest of the list.
    obtain ⟨ih1, ih2⟩ := stepWith_count hull (seen || b) rest
    -- A picked head stays picked: `true || _` is `true`.
    have hmono : b = true → (b || (seen && overlaps f hull)) = true := by
      intro hb
      rw [hb]
      rfl
    simp only [stepWith]
    -- Name the head's new flag `b'`.
    generalize (b || (seen && overlaps f hull)) = b' at *
    -- Four cases for the old flag `b` and the new flag `b'`.
    cases b <;> cases b'
    · -- Unpicked before and after: any change is in the rest.
      simp only [List.countP_cons, Bool.false_eq_true, ite_false, ne_eq, List.cons.injEq,
        true_and]
      exact ⟨by omega, fun hne => by have := ih2 hne; omega⟩
    · -- Newly picked: the count grows by one.
      simp only [List.countP_cons, Bool.false_eq_true, ite_false, ite_true, ne_eq,
        List.cons.injEq]
      exact ⟨by omega, fun _ => by omega⟩
    · -- Picked before and unpicked after: impossible.
      exact absurd (hmono rfl) (by decide)
    · -- Picked before and after: any change is in the rest.
      simp only [List.countP_cons, ite_true, ne_eq, List.cons.injEq, true_and]
      exact ⟨by omega, fun hne => by have := ih2 hne; omega⟩

/-- Enough fuel reaches a fixpoint: if the fuel `n` exceeds the number of
files not yet picked, `closeFuel n l` is a list a step leaves unchanged. -/
theorem closeFuel_fixpoint :
    ∀ (n : Nat) (l : List Slot), l.length < l.countP Prod.snd + n →
      step (closeFuel n l) = closeFuel n l
  | 0, l, h => by
    -- No fuel: impossible, as no more files can be picked than exist.
    have := List.countP_le_length (p := Prod.snd) (l := l)
    omega
  | n + 1, l, h => by
    unfold closeFuel
    by_cases hfix : step l = l
    · -- Already a fixpoint: done.
      rw [ite_eq_left hfix]
      exact hfix
    · -- Not a fixpoint: the step picked one more file, so the remaining
      -- fuel still suffices.
      rw [ite_eq_right hfix]
      apply closeFuel_fixpoint n (step l)
      have hcount := (stepWith_count (hullKeys l) false l).2 hfix
      have hlen := stepWith_length (hullKeys l) false l
      unfold step
      omega

/-- The closure is a fixpoint of the closure step. -/
theorem close_fixpoint (l : List Slot) : step (close l) = close l :=
  closeFuel_fixpoint _ l (by omega)

/-- The closure keeps the files and their order. -/
theorem closeFuel_files : ∀ (n : Nat) (l : List Slot), (closeFuel n l).map Prod.fst = l.map Prod.fst
  | 0, _ => rfl
  | n + 1, l => by
    unfold closeFuel
    split
    · -- Stopped at a fixpoint: the list itself.
      rfl
    · -- One more step keeps the files, and the remaining steps do too.
      rw [closeFuel_files n (step l)]
      exact stepWith_files _ _ _

/-- The closure never unpicks a file. -/
theorem closeFuel_keeps_picked :
    ∀ (n : Nat) (l : List Slot) (f : Source), (f, true) ∈ l → (f, true) ∈ closeFuel n l
  | 0, _, _, h => h
  | n + 1, l, f, h => by
    unfold closeFuel
    split
    · -- Stopped at a fixpoint: the list itself.
      exact h
    · -- One more step keeps the pick, and the remaining steps do too.
      exact closeFuel_keeps_picked n _ f (stepWith_keeps_picked _ _ _ f h)

/-- A pass that changes nothing certifies the closure rule: every unpicked
slot after a picked one (or after `seen`) does not overlap `hull`. -/
theorem stepWith_fixed_closed (hull : List Nat) :
    ∀ (seen : Bool) (l : List Slot), stepWith hull seen l = l →
      (seen = true → ∀ x ∈ l, x.2 = false → overlaps x.1 hull = false) ∧
      l.Pairwise (ClosureRule hull)
  -- An empty list has no slot and no pair.
  | _, [], _ => ⟨fun _ _ h => absurd h List.not_mem_nil, List.Pairwise.nil⟩
  | seen, (f, b) :: rest, hfix => by
    -- An unchanged list is an unchanged head flag and an unchanged rest.
    simp only [stepWith, List.cons.injEq, Prod.mk.injEq, true_and] at hfix
    -- hflag: the head's flag did not change.
    -- hrest: the pass changed nothing in the rest.
    obtain ⟨hflag, hrest⟩ := hfix
    obtain ⟨ihseen, ihpair⟩ := stepWith_fixed_closed hull (seen || b) rest hrest
    refine ⟨?_, ?_⟩
    · -- With a picked slot before it, an unpicked slot cannot overlap.
      intro hseen x hx hxun
      rcases List.mem_cons.mp hx with rfl | hm
      · -- The head: unpicked, and its flag stayed unpicked, so the
        -- overlap test failed.
        simp only at hxun
        subst hseen hxun
        simpa using hflag
      · exact ihseen (by simp [hseen]) x hm hxun
    · -- The head obeys the rule with every later slot; the rest by induction.
      refine List.Pairwise.cons ?_ ihpair
      intro y hy hbpick hyun
      exact ihseen (by simp at hbpick; simp [hbpick]) y hy hyun

/-- A fixpoint of the closure step is closed. -/
theorem fixpoint_closed {l : List Slot} (hfix : step l = l) : Closed l :=
  (stepWith_fixed_closed (hullKeys l) false l hfix).2

/-- **The closure picker returns a closed set.** -/
theorem pickL0_closed (lo hi : Nat) (files : List Source) : Closed (pickL0 lo hi files) :=
  fixpoint_closed (close_fixpoint _)

/-- The picker keeps the L0 files and their order. -/
theorem pickL0_files (lo hi : Nat) (files : List Source) :
    (pickL0 lo hi files).map Prod.fst = files := by
  unfold pickL0 close
  rw [closeFuel_files]
  -- The starting pick pairs each file with a flag; dropping the flags
  -- gives the files back.
  simp [initialPick, Function.comp_def]

/-- **The picker covers the range.** Every L0 file that intersects
`[lo, hi]` is picked, so `compact_range` compacts what it was asked to. -/
theorem pickL0_covers {lo hi : Nat} {files : List Source} {f : Source}
    -- `f` is an L0 file ...
    (hf : f ∈ files)
    -- ... with a key in the range.
    (hint : intersects f lo hi = true) :
    (f, true) ∈ pickL0 lo hi files := by
  apply closeFuel_keeps_picked
  simp only [initialPick, List.mem_map]
  exact ⟨f, hf, by rw [hint]⟩

/-- **E1, `compact_range` at L0.** Start from any ordered read order (the
memtable, the L0 files newest first, L1). Compact the L0 files the closure
picker selects for `[lo, hi]` into L1. The result is ordered, so the next
write, flush or compaction starts from an ordered state again, and every
read at every snapshot answers what it answered before. -/
theorem compact_range_reads_newest {mem l1 : Source} {files : List Source} {lo hi : Nat}
    -- The read order before the compaction is ordered.
    (hord : Ordered (mem :: (files ++ [l1]))) :
    Ordered (after mem (pickL0 lo hi files) l1) ∧
    ∀ k snap, read (after mem (pickL0 lo hi files) l1) k snap =
      read (mem :: (files ++ [l1])) k snap := by
  -- Before the compaction, the slots' files are exactly `files`.
  have hbefore : before mem (pickL0 lo hi files) l1 = mem :: (files ++ [l1]) := by
    unfold before
    rw [pickL0_files]
  rw [← hbefore] at hord ⊢
  exact ⟨compact_closed_preserves_order hord (pickL0_closed lo hi files),
    compact_closed_preserves_reads hord (pickL0_closed lo hi files)⟩

/-! ## The RED case: picking only the files that meet the range -/

/-- The newer L0 file of the counterexample: key 1 at sequence 3 and key 5
at sequence 4. Its range `[1, 5]` meets the compacted range `[1, 1]`. -/
def redNewer : Source := [(1, 3), (5, 4)]

/-- The older L0 file: key 5 at sequence 2. Its range `[5, 5]` misses
`[1, 1]`, but it overlaps the newer file's range. -/
def redOlder : Source := [(5, 2)]

/-- The counterexample's read order is ordered: the newer file's key 5 is
newer than the older file's. -/
theorem red_ordered : Ordered ([] :: ([redNewer, redOlder] ++ [[]])) := by
  -- Every pair of sources is compared by evaluating `newerB`.
  unfold Ordered
  decide

/-- **`intersect_only_breaks_reads`.** Picking only the L0 files that
intersect the range `[1, 1]` moves the newer file into L1 and leaves the
older one in L0. A read of key 5 then finds the older file first and
answers sequence 2, where it answered 4 before. The fixed picker also
picks the older file (`red_closure_picks_both`). -/
theorem intersect_only_breaks_reads :
    read (after [] (initialPick 1 1 [redNewer, redOlder]) []) 5 10 = some 2 ∧
    read ([] :: ([redNewer, redOlder] ++ [[]])) 5 10 = some 4 := by
  decide

/-- The closure picker picks both files for `[1, 1]`, and the read of key 5
still answers 4 after the compaction. -/
theorem red_closure_picks_both :
    pickL0 1 1 [redNewer, redOlder] = [(redNewer, true), (redOlder, true)] ∧
    read (after [] (pickL0 1 1 [redNewer, redOlder]) []) 5 10 = some 4 := by
  decide

/-! ## Frozen memtables: install in memtable order

The story. A writer fills the memtable and seals it (rotation): the sealed
memtable joins the frozen ones, which a read asks after the active memtable,
newest first, and before L0. Since E9 the writer does not flush it; the
compaction worker does, or the next write when there is no worker, or a
rotation at the memtable cap, or an explicit flush. Several threads can be
flushing, so the code makes every flush take the `flushing` exclusion and the
OLDEST frozen memtable (`Flusher::flush_oldest` in `src/engine/flush.rs`).

What can go wrong: two frozen memtables, the newer holding key 1 at sequence
2, the older key 1 at sequence 1. If the newer one's flush finishes first, its
file goes into L0, behind the older frozen memtable that a read still asks
first, and the read of key 1 goes back from 2 to 1. The theorems below show
the oldest-first install changes no read, for any number of memtables and
flushes, and the newer-first install breaking one. The TLA+ configurations
`MC_LsmOrder_Green_Flush` and `MC_LsmOrder_Red_FlushAnyOrder` check the same
over interleavings. -/

/-- **Installing the oldest frozen memtable leaves the read order as it
was.** The oldest frozen memtable is the last one read before L0; as the
newest L0 file it is the first one read in L0: the same position. So the
order stays ordered and every read is unchanged. -/
theorem install_oldest_same_order (mem : Source) (imm l0 deeper : List Source) (f : Source) :
    -- Before: the active memtable, the frozen ones with `f` the oldest, L0,
    -- the deeper levels. After: `f` is the newest L0 file. Same list.
    mem :: (imm ++ [f]) ++ l0 ++ deeper = mem :: imm ++ (f :: l0) ++ deeper := by
  -- Both sides are the same list once the appends are flattened.
  simp

/-- **Flushing any number of frozen memtables, oldest first, changes no
read.** Moving the oldest `old` frozen memtables, one by one and oldest first,
to the front of L0 leaves the sources in the same order, so every read of
every key at every snapshot answers as before. This is every flush of E9 in
a row, whichever threads ran them. -/
theorem install_oldest_all (mem : Source) (imm old l0 deeper : List Source) :
    -- Before: `old` are the oldest frozen memtables, after `imm`. After:
    -- they are the newest L0 files, in the same order.
    mem :: (imm ++ old) ++ l0 ++ deeper = mem :: imm ++ (old ++ l0) ++ deeper := by
  -- Flatten the appends: both sides are the same list.
  simp

/-- The reads are unchanged too: a read of key `k` at snapshot `snap` gives
the same answer before and after the oldest-first flushes. -/
theorem install_oldest_all_reads (mem : Source) (imm old l0 deeper : List Source)
    (k snap : Nat) :
    -- The read before equals the read after.
    read (mem :: (imm ++ old) ++ l0 ++ deeper) k snap =
      read (mem :: imm ++ (old ++ l0) ++ deeper) k snap := by
  -- The two source lists are equal, so the reads are.
  rw [install_oldest_all]

/-- **`install_newer_breaks_reads`.** Two frozen memtables, the newer
holding key 1 at 2 and the older key 1 at 1. Installing the newer one
first puts it behind the older one, which is still read before L0: the
read of key 1 answers 1 where it answered 2. -/
theorem install_newer_breaks_reads :
    -- Before any flush: the read of key 1 finds 2 in the newer frozen one.
    read ([] :: [[(1, 2)], [(1, 1)]] ++ []) 1 10 = some 2 ∧
    -- After the newer one's file reaches L0 first: the older frozen one
    -- is asked first and answers 1.
    read ([] :: [[(1, 1)]] ++ ([(1, 2)] :: [])) 1 10 = some 1 := by
  -- Concrete lists: evaluate both reads.
  decide

/-! ## Ingest placement

An ingested file holds versions at one fresh sequence, newer than every
version in the tree. It may sit anywhere in the read order where every
source read before it holds none of its keys. The TLA+ configurations
`MC_LsmOrder_Green_Ingest` and `MC_LsmOrder_Red_IngestIgnoresUpper` check
the placement rule that guarantees this. -/

/-- `NoShared a b`: the sources `a` and `b` hold no version of a common
key. -/
def NoShared (a b : Source) : Prop := ∀ k s t, (k, s) ∈ a → (k, t) ∈ b → False

/-- Sources with no common key are `Newer` each way, vacuously. -/
theorem newer_of_noShared {a b : Source} (h : NoShared a b) : Newer a b :=
  fun k s t hs ht => (h k s t hs ht).elim

/-- **`ingest_ordered`.** Put the file `f` between `pre` (the sources read
before it) and `post` (those read after). If no source of `pre` shares a
key with `f`, and every version of `f` is newer than every version already
held, the read order stays ordered. -/
theorem ingest_ordered {pre post : List Source} {f : Source}
    -- The read order before the ingest is ordered.
    (hord : Ordered (pre ++ post))
    -- Nothing read before the file holds one of its keys.
    (hpre : ∀ src ∈ pre, NoShared src f)
    -- The file's versions are newer than every version held.
    (hfresh : ∀ v ∈ f, ∀ w, Holds (pre ++ post) w → w.2 < v.2) :
    Ordered (pre ++ f :: post) := by
  unfold Ordered at *
  rw [List.pairwise_append] at hord ⊢
  obtain ⟨hp, hq, hpq⟩ := hord
  refine ⟨hp, List.Pairwise.cons ?_ hq, ?_⟩
  · -- The file is newer than every source after it.
    intro b hb k s t hs ht
    exact hfresh (k, s) hs (k, t) ⟨b, List.mem_append_right _ hb, ht⟩
  · -- A source before the file is newer than the file (no common key) and
    -- than every source after it (as before).
    intro a ha b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact newer_of_noShared (hpre a ha)
    · exact hpq a ha b hb'

/-- **`ingest_below_holder_breaks_reads`.** L1 holds key 1 at 1. An
ingested file holding key 1 at 2, placed in L2 below it, is read after
it: the read answers 1. Placed in front, it answers 2. -/
theorem ingest_below_holder_breaks_reads :
    read [[], [(1, 1)], [(1, 2)]] 1 10 = some 1 ∧
    read [[], [(1, 2)], [(1, 1)]] 1 10 = some 2 := by
  decide

/-! ## Demotion of an overlapping level at open (E14, D13)

A tree's read order is its memtables, its L0 files newest first, then each
level's tables. Within a level whose tables do not overlap, at most one
table can hold a key, so reading the level's tables one after another
answers what reading the one table binary search finds answers
(`level_read_bsearch`, below). So a tree's read order is the flat list
`treeOrder`. A level whose recorded ranges overlap breaks the binary
search; the TLA+ configuration `MC_LsmOrder_Red_NoDemotion` shows the read
it gets wrong. -/

/-- The flat read order of a tree. -/
def treeOrder (mems l0 : List Source) (levels : List (List Source)) : List Source :=
  mems ++ l0 ++ levels.flatten

/-- The L0 files after the open demotes levels `1..d`: the old L0 files,
then those levels' tables, level by level, each level in the order given
(age order: newest first). -/
def demoteL0 (d : Nat) (l0 : List Source) (levels : List (List Source)) : List Source :=
  l0 ++ (levels.take d).flatten

/-- The levels after the open demotes levels `1..d`: those are empty, the
deeper ones unchanged. -/
def demoteLevels (d : Nat) (levels : List (List Source)) : List (List Source) :=
  (levels.take d).map (fun _ => []) ++ levels.drop d

/-- Demoting levels `1..d` leaves the flat read order exactly as it was. -/
theorem demote_same_order (mems l0 : List Source) (levels : List (List Source)) (d : Nat) :
    treeOrder mems (demoteL0 d l0 levels) (demoteLevels d levels) = treeOrder mems l0 levels := by
  -- The emptied levels contribute nothing, and the demoted tables sit
  -- exactly where they were: after L0 and before the deeper levels.
  unfold treeOrder demoteL0 demoteLevels
  have hnil : ((levels.take d).map (fun _ => ([] : List Source))).flatten = [] := by
    rw [List.flatten_eq_nil_iff]
    intro l hl
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hl
    rfl
  rw [List.flatten_append, hnil, List.nil_append]
  conv => rhs; rw [← List.take_append_drop d levels, List.flatten_append]
  simp only [List.append_assoc]

/-- **`demote_reads_newest`.** If the tree's read order is ordered, with
the overlapping level's tables in age order, then after the open demotes
every level from L1 down to it, the read order is still ordered and every
read answers as before: by `read_newest`, the newest visible version. -/
theorem demote_reads_newest {mems l0 : List Source} {levels : List (List Source)} (d : Nat)
    -- The read order before the open is ordered.
    (hord : Ordered (treeOrder mems l0 levels)) :
    Ordered (treeOrder mems (demoteL0 d l0 levels) (demoteLevels d levels)) ∧
    ∀ k snap, read (treeOrder mems (demoteL0 d l0 levels) (demoteLevels d levels)) k snap =
      read (treeOrder mems l0 levels) k snap := by
  rw [demote_same_order]
  exact ⟨hord, fun _ _ => rfl⟩

/-- The tables of the overlapping level E14 leaves behind share no key:
0.1.x placed the ingested file by its point keys, and only its recorded
range overlaps. Tables sharing no key are ordered among themselves in
any order, so age order is ordered. -/
theorem noShared_level_ordered {T : List Source}
    -- No two tables of the level share a key.
    (h : T.Pairwise NoShared) : Ordered T :=
  h.imp newer_of_noShared

/-- The defect: the open demotes only level `d`, moving it to the end of
L0, in front of levels `1..d-1`. -/
def demoteOnly (d : Nat) (l0 : List Source) (levels : List (List Source)) :
    List Source × List (List Source) :=
  (l0 ++ levels.getD (d - 1) [], levels.set (d - 1) [])

/-- **`demote_level_only_breaks_reads`.** L1 holds key 1 at 2; L2's tables
overlap and hold key 2 at 3 and key 1 at 1. Before the open, the read of
key 1 answers 2. Demoting L2 alone puts its tables in front of L1, and
the read answers 1. Demoting L1 with it keeps the answer 2. -/
theorem demote_level_only_breaks_reads :
    read (treeOrder [[]] [] [[[(1, 2)]], [[(2, 3)], [(1, 1)]]]) 1 10 = some 2 ∧
    read (treeOrder [[]] (demoteOnly 2 [] [[[(1, 2)]], [[(2, 3)], [(1, 1)]]]).1
      (demoteOnly 2 [] [[[(1, 2)]], [[(2, 3)], [(1, 1)]]]).2) 1 10 = some 1 ∧
    read (treeOrder [[]] (demoteL0 2 [] [[[(1, 2)]], [[(2, 3)], [(1, 1)]]])
      (demoteLevels 2 [[[(1, 2)]], [[(2, 3)], [(1, 1)]]])) 1 10 = some 2 := by
  decide

/-! ## Binary search within a level

Below L0, a read of key `k` binary-searches a level's tables, which are in
key order, for the first table whose range ends at or above `k`, and reads
that table if its range starts at or below `k`. -/

/-- Binary search over positions `[a, b)`: the least position `i` with
`k ≤ hi i`, or `b` when there is none, halving the interval each step.
`hi i` is the greatest key table `i` records. -/
def bsearch (hi : Nat → Nat) (k : Nat) (a b : Nat) : Nat :=
  if a < b then
    if hi ((a + b) / 2) < k then bsearch hi k ((a + b) / 2 + 1) b
    else bsearch hi k a ((a + b) / 2)
  else a
termination_by b - a
decreasing_by all_goals omega

/-- The linear scan: the least position `i` in `[a, b)` with `k ≤ hi i`,
or `b`, trying each position in turn. -/
def scan (hi : Nat → Nat) (k : Nat) (a b : Nat) : Nat :=
  if a < b then (if k ≤ hi a then a else scan hi k (a + 1) b) else a
termination_by b - a

/-- `IsFirst hi k a b r`: `r` is the least position in `[a, b)` whose
`hi` reaches `k`, or `b` when none does. -/
def IsFirst (hi : Nat → Nat) (k a b r : Nat) : Prop :=
  a ≤ r ∧ r ≤ b ∧ (∀ i, a ≤ i → i < r → hi i < k) ∧ (r < b → k ≤ hi r)

/-- `MonoUpTo hi n`: `hi` never decreases over positions `0..n-1`, as the
greatest keys of a key-ordered level's tables do. -/
def MonoUpTo (hi : Nat → Nat) (n : Nat) : Prop := ∀ i j, i ≤ j → j < n → hi i ≤ hi j

/-- Two positions both first are the same position. -/
theorem isFirst_unique {hi : Nat → Nat} {k a b r1 r2 : Nat}
    (h1 : IsFirst hi k a b r1) (h2 : IsFirst hi k a b r2) : r1 = r2 := by
  obtain ⟨ha1, hb1, hlt1, hge1⟩ := h1
  obtain ⟨ha2, hb2, hlt2, hge2⟩ := h2
  -- If one were smaller, it would lie below the other, where every `hi`
  -- is below `k`, yet its own `hi` reaches `k`.
  rcases Nat.lt_trichotomy r1 r2 with h | h | h
  · have := hlt2 r1 ha1 h
    have := hge1 (by omega)
    omega
  · exact h
  · have := hlt1 r2 ha2 h
    have := hge2 (by omega)
    omega

/-- The linear scan finds the first position. -/
theorem scan_spec (hi : Nat → Nat) (k : Nat) (a b : Nat) (hab : a ≤ b) :
    IsFirst hi k a b (scan hi k a b) := by
  rw [scan]
  split
  · rename_i hlt
    split
    · -- Position `a` reaches `k`: it is first.
      rename_i hk
      exact ⟨Nat.le_refl a, hab, fun i h1 h2 => absurd h2 (by omega), fun _ => hk⟩
    · -- It does not: the first is further on.
      rename_i hk
      obtain ⟨h1, h2, h3, h4⟩ := scan_spec hi k (a + 1) b (by omega)
      refine ⟨by omega, h2, fun i hi1 hi2 => ?_, h4⟩
      by_cases hia : i = a
      · subst hia
        omega
      · exact h3 i (by omega) hi2
  · -- An empty interval: the answer is its end.
    exact ⟨Nat.le_refl a, hab, fun i h1 h2 => absurd h2 (by omega), fun h => absurd h (by omega)⟩
termination_by b - a

/-- Binary search finds the first position, when `hi` never decreases. -/
theorem bsearch_spec (hi : Nat → Nat) (k : Nat) {n : Nat} (hmono : MonoUpTo hi n)
    (a b : Nat) (hab : a ≤ b) (hbn : b ≤ n) :
    IsFirst hi k a b (bsearch hi k a b) := by
  rw [bsearch]
  split
  · rename_i hlt
    split
    · -- The middle is below `k`, and so is everything before it: the
      -- first lies after the middle.
      rename_i hmid
      obtain ⟨h1, h2, h3, h4⟩ := bsearch_spec hi k hmono ((a + b) / 2 + 1) b (by omega) hbn
      refine ⟨by omega, h2, fun i hi1 hi2 => ?_, h4⟩
      by_cases hi3 : i ≤ (a + b) / 2
      · have := hmono i ((a + b) / 2) hi3 (by omega)
        omega
      · exact h3 i (by omega) hi2
    · -- The middle reaches `k`: the first is at or before it.
      rename_i hmid
      obtain ⟨h1, h2, h3, h4⟩ := bsearch_spec hi k hmono a ((a + b) / 2) (by omega) (by omega)
      refine ⟨h1, by omega, h3, fun _ => ?_⟩
      by_cases heq : bsearch hi k a ((a + b) / 2) = (a + b) / 2
      · rw [heq]
        omega
      · exact h4 (by omega)
  · -- An empty interval: the answer is its end.
    exact ⟨Nat.le_refl a, hab, fun i h1 h2 => absurd h2 (by omega), fun h => absurd h (by omega)⟩
termination_by b - a

/-- **`bsearch_eq_scan`.** On positions whose `hi` never decreases, binary
search finds the position the linear scan finds. -/
theorem bsearch_eq_scan (hi : Nat → Nat) (k : Nat) {n : Nat} (hmono : MonoUpTo hi n)
    (a b : Nat) (hab : a ≤ b) (hbn : b ≤ n) :
    bsearch hi k a b = scan hi k a b :=
  isFirst_unique (bsearch_spec hi k hmono a b hab hbn) (scan_spec hi k a b hab)

/-- A level table: the key range the manifest records and the versions. -/
structure Table where
  /-- The least key the range records. -/
  lo : Nat
  /-- The greatest key the range records. -/
  hi : Nat
  /-- The versions the table holds. -/
  src : Source

/-- `SortedLevel T`: each table's range is a range, holds every key of
the table, and ends below where every later table's range begins: a
level in key order whose tables do not overlap. -/
def SortedLevel (T : List Table) : Prop :=
  (∀ t ∈ T, t.lo ≤ t.hi ∧ ∀ v ∈ t.src, t.lo ≤ v.1 ∧ v.1 ≤ t.hi) ∧
  T.Pairwise (fun t u => t.hi < u.lo)

/-- The greatest key of table `i`, or 0 past the end. -/
def hiAt (T : List Table) (i : Nat) : Nat := (T[i]?.map Table.hi).getD 0

/-- In a sorted level the greatest keys never decrease. -/
theorem sorted_mono {T : List Table} (hT : SortedLevel T) : MonoUpTo (hiAt T) T.length := by
  obtain ⟨hrange, hpair⟩ := hT
  intro i j hij hj
  have hi' : i < T.length := by omega
  simp only [hiAt, List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj, Option.map_some,
    Option.getD_some]
  rcases Nat.lt_or_eq_of_le hij with h | h
  · -- An earlier table ends below where a later one begins.
    have := List.pairwise_iff_getElem.mp hpair i j hi' hj h
    have := (hrange T[j] (List.getElem_mem hj)).1
    omega
  · subst h
    exact Nat.le_refl _

/-- The read of a level through binary search: find the first table whose
range ends at or above `k`, and read it if its range starts at or below
`k`. -/
def levelReadB (T : List Table) (k snap : Nat) : Option Nat :=
  match T[bsearch (hiAt T) k 0 T.length]? with
  | some t => if t.lo ≤ k then newestIn t.src k snap else none
  | none => none

/-- A source holding no version of `k` answers nothing. -/
theorem newestIn_of_absent {src : Source} {k snap : Nat} (h : ∀ s, (k, s) ∉ src) :
    newestIn src k snap = none :=
  newestIn_eq_none.mpr fun s hs => absurd hs (h s)

/-- When every source but the one at position `r` holds no version of
`k`, a read answers what that one source answers. -/
theorem read_only_at {k snap : Nat} :
    ∀ (l : List Source) (r : Nat),
      (∀ i (hi : i < l.length), i ≠ r → ∀ s, (k, s) ∉ l[i]) →
      read l k snap = (match l[r]? with | some src => newestIn src k snap | none => none)
  | [], _, _ => rfl
  | src :: rest, 0, h => by
    -- Every later source holds nothing of `k`, so the read is the first's.
    have hrest : read rest k snap = none := by
      refine read_eq_none.mpr fun s ⟨src', hsrc', hs⟩ => ?_
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hsrc'
      exact absurd hs (h (i + 1) (by simp; omega) (by omega) s)
    simp only [read, List.getElem?_cons_zero]
    cases newestIn src k snap with
    | some v => rfl
    | none => exact hrest
  | src :: rest, r + 1, h => by
    -- The first source holds nothing of `k`: the read is the rest's.
    have hfirst : newestIn src k snap = none :=
      newestIn_of_absent fun s => h 0 (by simp) (by omega) s
    simp only [read, hfirst, List.getElem?_cons_succ]
    exact read_only_at rest r fun i hi hne s => h (i + 1) (by simp; omega) (by omega) s

/-- **`level_read_bsearch`.** On a level in key order whose tables do not
overlap, the read through binary search answers what a linear read of
every table in order answers. -/
theorem level_read_bsearch {T : List Table} (hT : SortedLevel T) (k snap : Nat) :
    levelReadB T k snap = read (T.map Table.src) k snap := by
  have hspec := bsearch_spec (hiAt T) k (sorted_mono hT) 0 T.length (Nat.zero_le _) (Nat.le_refl _)
  generalize hr : bsearch (hiAt T) k 0 T.length = r at hspec
  obtain ⟨-, hrle, hbelow, hat⟩ := hspec
  obtain ⟨hrange, hpair⟩ := hT
  -- The greatest key of a table in the level, by position.
  have hiAt_eq : ∀ i (hi : i < T.length), hiAt T i = T[i].hi := by
    intro i hi
    simp [hiAt, List.getElem?_eq_getElem hi]
  -- No table before `r` holds `k`: its keys end below `k`.
  have hbefore : ∀ i (hi : i < T.length), i < r → ∀ s, (k, s) ∉ T[i].src := by
    intro i hi hir s hs
    have h1 := hbelow i (Nat.zero_le _) hir
    rw [hiAt_eq i hi] at h1
    have := ((hrange T[i] (List.getElem_mem hi)).2 _ hs).2
    simp only at this
    omega
  -- No table after `r` holds `k`: its keys start above table `r`'s end,
  -- which reaches `k`.
  have hafter : ∀ i (hi : i < T.length), r < i → ∀ s, (k, s) ∉ T[i].src := by
    intro i hi hri s hs
    have hrl : r < T.length := by omega
    have h1 := hat hrl
    rw [hiAt_eq r hrl] at h1
    have h2 := List.pairwise_iff_getElem.mp hpair r i hrl hi hri
    have := ((hrange T[i] (List.getElem_mem hi)).2 _ hs).1
    simp only at this
    omega
  -- So only table `r` can answer, and a linear read answers what it does.
  have honly : ∀ i (hi : i < (T.map Table.src).length), i ≠ r → ∀ s, (k, s) ∉ (T.map Table.src)[i] := by
    intro i hi hne s
    simp only [List.length_map] at hi
    simp only [List.getElem_map]
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hbefore i hi h s
    · exact hafter i hi h s
  rw [read_only_at _ r honly]
  unfold levelReadB
  rw [hr, List.getElem?_map]
  cases hT : T[r]? with
  | none => rfl
  | some t =>
    simp only [Option.map_some]
    split
    · rfl
    · -- Table `r`'s range starts above `k`, so it holds no version of `k`.
      rename_i hlo
      have hmem : t ∈ T := List.mem_of_getElem? hT
      exact (newestIn_of_absent fun s hs => by
        have := ((hrange t hmem).2 _ hs).1
        simp only at this
        omega).symm

end Regolith.LsmOrder
