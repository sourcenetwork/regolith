/-!
# ReadViewPublishers: every publisher of the read view loses nothing

This file backs the TLA+ model `proofs/tla/ReadViewPublishers.tla`. TLC
checks there three rotations, their flushes, a compaction and an ingest
racing. Here the same rules are proved for every number of publications.

## The story, for a reader who has never seen the code

Every read starts from the read view (`src/engine/read_view.rs`): the
memtable writers append to (the active one), the memtables waiting for a
flush (frozen, oldest first), and the tables of the current version. Data
lives in exactly those three places.

Several threads change the view: a rotation seals the active memtable
behind a fresh one; a flush (the compaction worker's, a writer's after its
commit, or a writer's inside a stall step) installs a frozen memtable's
table and then retires the memtable; a compaction and an ingest install
tables. Each builds the next view from the view it loaded and swaps it in
with one compare-and-swap (CAS): only if the view it built from is still
the published one. Otherwise it builds again on the newer view.

Tiny example of what the CAS prevents. The view is (active 2, frozen [1],
tables [1]) and a flush is about to retire memtable 1; it builds (active 2,
frozen [], tables [1]). A rotation then publishes (active 3, frozen [1, 2],
tables [1]). If the flush stores its view without the CAS, memtable 3, the
one writers are appending to, is in no place at all, and every write in it
is lost. With the CAS the flush's swap loses, and it retires memtable 1 from
the newer view instead.

## What is proved, in plain words

1. `cas_applies_to_current`: a swap that goes in has the same effect as
   applying its update to the view published now. So a run of CAS
   publications is a run of updates, each applied to its predecessor,
   which is what the steps below are.
2. `no_lost_memtable`: every memtable ever made is active, frozen, or has
   its table in the version (TLA+ `NoLostMemtable`).
3. `no_lost_ingest`: every ingested table is in the version (TLA+
   `NoLostIngest`).
4. `retired_stay_gone`: a memtable a flush retired is never active or
   frozen again (TLA+ `RetiredStayGone`).
5. `frozen_sorted`: the frozen list is in seal order (TLA+
   `FrozenInSealOrder`).
6. The RED cases, as counterexamples: a retire stored without the CAS loses
   a racing seal (`plain_retire_loses_a_seal`), and so does a compaction's
   version publish stored without it (`plain_version_loses_a_seal`).

## How to read the Lean

`def` defines a thing, `theorem` states a fact and its proof follows
`:= by`. Lines starting with `--` are comments, in plain words. A proof is a
list of *tactics*; each one changes the goal still to be shown, and the
comment above it says how. `simp` rewrites with known facts; `omega` solves
arithmetic over natural numbers; `cases` splits on the ways a fact could be
true; `induction` proves a fact for every number of steps by proving it for
none and then for one more.
-/

-- Everything below is named Regolith.ReadViewPublishers.<name>.
namespace Regolith.ReadViewPublishers

/-! ## Part 1. Views and the publications -/

/-- One read view. Memtables are named by number, in the order they were
made; a table of a flushed memtable carries the memtable's number. -/
structure View where
  /-- The memtable writers append to. -/
  active : Nat
  /-- The memtables waiting for a flush, oldest first. -/
  frozen : List Nat
  /-- The flushed memtables whose tables the version holds. -/
  tables : List Nat
  /-- The ingested tables the version holds. -/
  ingests : List Nat
  -- Two views can be compared for equality, which the CAS needs.
  deriving DecidableEq

/-- A rotation's update (`seal_active`): the active memtable becomes the
newest frozen one, and `fresh`, made before the publication, is active. -/
def rotate (fresh : Nat) (v : View) : View :=
  -- Active is the fresh memtable; the old active joins the end of frozen.
  { v with active := fresh, frozen := v.frozen ++ [v.active] }

/-- A flush's install of memtable `m`'s table (a version publish). -/
def install (m : Nat) (v : View) : View :=
  -- The version holds `m`'s table now.
  { v with tables := m :: v.tables }

/-- A flush's retire of memtable `m` (`retire_memtable`), by identity. -/
def retire (m : Nat) (v : View) : View :=
  -- Every frozen memtable but `m`, in the same order.
  { v with frozen := v.frozen.filter (fun x => x != m) }

/-- An ingest's install of table `t` (a version publish). -/
def ingest (t : Nat) (v : View) : View :=
  -- The version holds the ingested table now.
  { v with ingests := t :: v.ingests }

/-- A compaction's install: its output holds the same data as its inputs,
so the places data lives in are the same. -/
def compact (v : View) : View :=
  -- Nothing a reader can tell apart changes.
  v

/-- The compare-and-swap of `ReadViewCell::publish`: the view built from
`base` goes in only if `base` is still the published view. -/
def cas (published base next : View) : View :=
  -- In when nothing was published since `base` was loaded, else no change.
  if published = base then next else published

/-- **`cas_applies_to_current`.** A swap that goes in has the effect of the
update applied to the view published now: what was loaded is what is there. -/
theorem cas_applies_to_current (published base : View) (upd : View → View)
    (h : published = base) :
    -- The claim itself; its proof follows.
    cas published base (upd base) = upd published := by
  -- Replace `base` by `published`, then the `if` holds and gives the update.
  subst h; simp [cas]

/-- A swap that loses changes nothing: the publisher builds again on what
won. -/
theorem cas_out (published base next : View) (h : published ≠ base) :
    -- The claim itself; its proof follows.
    cas published base next = published := by
  -- The `if` fails by `h`.
  simp [cas, h]

/-! ## Part 2. The steps and what every reachable state keeps -/

/-- Everything at one moment: the published view, how many memtables exist
(numbered `1..made`), and two ghosts the rules talk about. -/
structure World where
  /-- The published view. -/
  view : View
  /-- Memtables `1..made` have been made. -/
  made : Nat
  /-- Every memtable a flush retired. -/
  retired : List Nat
  /-- Every table an ingest installed. -/
  ingested : List Nat

/-- The start: memtable 1 is active, nothing else exists. -/
def init : World :=
  -- Active 1, nothing frozen, no table, nothing retired or ingested.
  ⟨⟨1, [], [], []⟩, 1, [], []⟩

/-- The publications, each one CAS that went in, so each one's update
applied to the view published now (`cas_applies_to_current`). -/
inductive Step : World → World → Prop
  /-- A rotation: a fresh memtable, number `made + 1`, becomes active. -/
  | rotate (w : World) :
      -- The view sealed, and one more memtable exists.
      Step w { w with view := rotate (w.made + 1) w.view, made := w.made + 1 }
  /-- A flush installs the table of frozen memtable `m`. -/
  | install (w : World) (m : Nat) (h : m ∈ w.view.frozen) :
      -- The version holds `m`'s table.
      Step w { w with view := install m w.view }
  /-- A flush retires memtable `m`, whose table the version holds. -/
  | retire (w : World) (m : Nat) (h : m ∈ w.view.tables) :
      -- `m` leaves the frozen list, and is noted as retired.
      Step w { w with view := retire m w.view, retired := m :: w.retired }
  /-- An ingest installs table `t`. -/
  | ingest (w : World) (t : Nat) :
      -- The version holds `t`, and it is noted as ingested.
      Step w { w with view := ingest t w.view, ingested := t :: w.ingested }
  /-- A compaction installs its output. -/
  | compact (w : World) :
      -- The places data lives in are the same.
      Step w { w with view := compact w.view }

/-- The worlds the steps can reach from the start. -/
inductive Reach : World → Prop
  /-- The start is reachable. -/
  | init : Reach init
  /-- One step from a reachable world reaches another. -/
  | step {w u : World} : Reach w → Step w u → Reach u

/-- The facts every reachable world has. The rules follow from them. -/
structure Inv (w : World) : Prop where
  /-- At least one memtable exists. -/
  made_pos : 1 ≤ w.made
  /-- The active memtable is the newest one. -/
  active_newest : w.view.active = w.made
  /-- Every frozen memtable is older than the active one. -/
  frozen_old : ∀ m ∈ w.view.frozen, 1 ≤ m ∧ m < w.made
  /-- Every flushed memtable is older than the active one. -/
  tables_old : ∀ m ∈ w.view.tables, m < w.made
  /-- Every memtable made is active, frozen, or has its table installed. -/
  no_lost : ∀ m, 1 ≤ m → m ≤ w.made →
    m = w.view.active ∨ m ∈ w.view.frozen ∨ m ∈ w.view.tables
  /-- A retired memtable's table is installed. -/
  retired_in_tables : ∀ r ∈ w.retired, r ∈ w.view.tables
  /-- A retired memtable is not frozen. -/
  retired_gone : ∀ r ∈ w.retired, r ∉ w.view.frozen
  /-- Every ingested table is installed. -/
  ingests_kept : ∀ t ∈ w.ingested, t ∈ w.view.ingests
  /-- The frozen list is in the order the memtables were made. -/
  frozen_sorted : w.view.frozen.Pairwise (· < ·)

/-- The start keeps every fact. -/
theorem inv_init : Inv init := by
  -- One field at a time; the start has one memtable and nothing else.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- One memtable exists.
  · simp [init]
  -- Memtable 1 is active and is the newest.
  · simp [init]
  -- Nothing is frozen.
  · intro m hm; simp [init] at hm
  -- Nothing is installed.
  · intro m hm; simp [init] at hm
  -- The only memtable, 1, is the active one.
  · intro m h1 h2; left; simp [init] at h2 ⊢; omega
  -- Nothing is retired.
  · intro r hr; simp [init] at hr
  -- Nothing is retired.
  · intro r hr; simp [init] at hr
  -- Nothing is ingested.
  · intro t ht; simp [init] at ht
  -- An empty list is in order.
  · simp [init]

/-- Every step keeps every fact. -/
theorem inv_step {w u : World} (hw : Inv w) (hst : Step w u) : Inv u := by
  -- One case per kind of publication.
  cases hst with
  | rotate =>
    -- The old active memtable is the newest one, number `made`.
    have hact := hw.active_newest
    -- Prove the facts one at a time.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- One more memtable exists.
    · simp only; omega
    -- The fresh one, `made + 1`, is active.
    · simp [rotate]
    -- Frozen: the old ones, older still, and the old active, `made`.
    · intro m hm
      -- A member of `l ++ [x]` is in `l` or is `x`.
      simp only [rotate, List.mem_append, List.mem_singleton] at hm
      -- Split on which.
      rcases hm with hm | rfl
      -- An old frozen memtable: older than `made`, so than `made + 1`.
      · have := hw.frozen_old m hm; simp only; omega
      -- The old active one: it is `made`, at least 1, below `made + 1`.
      · have := hw.made_pos; simp only; omega
    -- Tables: unchanged, and older than `made`, so than `made + 1`.
    · intro m hm; have := hw.tables_old m hm; simp only; omega
    -- Nothing lost: split on the memtable's number.
    · intro m h1 h2
      -- Split: is it the fresh one?
      by_cases hm : m = w.made + 1
      -- The fresh one is active.
      · left; simp [rotate, hm]
      -- Otherwise it is one of `1..made`, placed as before.
      · have hle : m ≤ w.made := by simp only at h2; omega
        -- Where it was before the seal.
        rcases hw.no_lost m h1 hle with h | h | h
        -- The old active one is now the newest frozen one.
        · right; left; simp [rotate, h]
        -- An old frozen one is still frozen.
        · right; left; simp [rotate, h]
        -- An installed one is still installed.
        · right; right; simpa [rotate] using h
    -- Retired ones keep their tables: tables are unchanged.
    · intro r hr; simpa [rotate] using hw.retired_in_tables r hr
    -- Retired ones are not frozen: not before, and not the old active.
    · intro r hr
      -- Its table is installed, so it is older than `made`, the old active.
      have hold := hw.tables_old r (hw.retired_in_tables r hr)
      -- Not in `frozen ++ [active]`.
      simp only [rotate, List.mem_append, List.mem_singleton, not_or]
      -- Not an old frozen one, and not the old active one (`made`).
      exact ⟨hw.retired_gone r hr, by omega⟩
    -- Ingests are unchanged.
    · intro t ht; simpa [rotate] using hw.ingests_kept t ht
    -- In order: the old list was, and every old frozen one is below `made`.
    · simp only [rotate, List.pairwise_append, List.pairwise_singleton, List.mem_singleton]
      -- The three parts: the old list, the one-element list, and between.
      refine ⟨hw.frozen_sorted, trivial, ?_⟩
      -- Each old frozen one is below the old active one, `made`.
      intro a ha b hb; subst hb; have := hw.frozen_old a ha; omega
  | install m h =>
    -- `m` is frozen, so older than the active one.
    have hm := hw.frozen_old m h
    -- Prove the facts one at a time.
    refine ⟨hw.made_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- The active one is unchanged.
    · simpa [install] using hw.active_newest
    -- Frozen is unchanged.
    · simpa [install] using hw.frozen_old
    -- Tables: `m`, older than `made`, then the old ones.
    · intro x hx
      -- A member of `m :: l` is `m` or in `l`.
      simp only [install, List.mem_cons] at hx
      -- Split on which.
      rcases hx with rfl | hx
      -- `m`: older than `made`.
      · exact hm.2
      -- An old one: as before.
      · exact hw.tables_old x hx
    -- Nothing lost: every place grew or stayed.
    · intro x h1 h2
      -- Where it was before.
      rcases hw.no_lost x h1 h2 with h' | h' | h'
      -- Still active.
      · left; simpa [install] using h'
      -- Still frozen.
      · right; left; simpa [install] using h'
      -- Still installed, behind `m`.
      · right; right; simp [install, h']
    -- Retired ones' tables: still installed.
    · intro r hr; simp [install, hw.retired_in_tables r hr]
    -- Retired ones: frozen is unchanged.
    · intro r hr; simpa [install] using hw.retired_gone r hr
    -- Ingests are unchanged.
    · intro t ht; simpa [install] using hw.ingests_kept t ht
    -- Frozen, unchanged, is in order.
    · simpa [install] using hw.frozen_sorted
  | retire m h =>
    -- `m`'s table is installed, so it is older than the active one.
    have hm := hw.tables_old m h
    -- Prove the facts one at a time.
    refine ⟨hw.made_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- The active one is unchanged.
    · simpa [retire] using hw.active_newest
    -- Frozen only lost `m`: every one left was frozen before.
    · intro x hx
      -- A member of the filtered list was in the list.
      simp only [retire, List.mem_filter] at hx
      -- As before.
      exact hw.frozen_old x hx.1
    -- Tables are unchanged.
    · simpa [retire] using hw.tables_old
    -- Nothing lost: a frozen one other than `m` stays frozen; `m` is installed.
    · intro x h1 h2
      -- Where it was before.
      rcases hw.no_lost x h1 h2 with h' | h' | h'
      -- Still active.
      · left; simpa [retire] using h'
      -- Was frozen: split on whether it is `m`.
      · by_cases hx : x = m
        -- It is `m`: its table is installed.
        · right; right; subst hx; simpa [retire] using h
        -- It is not: still frozen.
        · right; left; simp [retire, List.mem_filter, h', hx]
      -- Still installed.
      · right; right; simpa [retire] using h'
    -- Retired ones' tables: `m`'s is installed, and the others as before.
    · intro r hr
      -- A member of `m :: l` is `m` or in `l`.
      simp only [List.mem_cons] at hr
      -- Split on which.
      rcases hr with rfl | hr
      -- `m`: installed.
      · simpa [retire] using h
      -- An old one: as before.
      · simpa [retire] using hw.retired_in_tables r hr
    -- Retired ones are not frozen: `m` was filtered out, the others were not
    -- frozen before.
    · intro r hr
      -- A member of `m :: l` is `m` or in `l`.
      simp only [List.mem_cons] at hr
      -- Not in the filtered list.
      simp only [retire, List.mem_filter, not_and]
      -- Split on which.
      rcases hr with rfl | hr
      -- `m`: the filter removed every `m`.
      · intro _; simp
      -- An old one: it was not frozen at all.
      · intro hin; exact absurd hin (hw.retired_gone r hr)
    -- Ingests are unchanged.
    · intro t ht; simpa [retire] using hw.ingests_kept t ht
    -- A filtered list in order stays in order.
    · simpa [retire] using hw.frozen_sorted.filter _
  | ingest t =>
    -- Prove the facts one at a time; only the ingests change.
    refine ⟨hw.made_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- The active one is unchanged.
    · simpa [ingest] using hw.active_newest
    -- Frozen is unchanged.
    · simpa [ingest] using hw.frozen_old
    -- Tables are unchanged.
    · simpa [ingest] using hw.tables_old
    -- Nothing lost: no memtable place changed.
    · intro x h1 h2; simpa [ingest] using hw.no_lost x h1 h2
    -- Retired ones' tables: unchanged.
    · intro r hr; simpa [ingest] using hw.retired_in_tables r hr
    -- Retired ones: frozen is unchanged.
    · intro r hr; simpa [ingest] using hw.retired_gone r hr
    -- Ingests: `t`, installed now, and the others as before.
    · intro x hx
      -- A member of `t :: l` is `t` or in `l`.
      simp only [List.mem_cons] at hx
      -- Split on which.
      rcases hx with rfl | hx
      -- `t`: installed by this step.
      · simp [ingest]
      -- An old one: as before.
      · simp [ingest, hw.ingests_kept x hx]
    -- Frozen, unchanged, is in order.
    · simpa [ingest] using hw.frozen_sorted
  | compact =>
    -- Nothing changes: the view is the same.
    simpa [compact] using hw

/-- Every reachable world keeps every fact. -/
theorem inv_reach {w : World} (h : Reach w) : Inv w := by
  -- By how `w` was reached: the start, or one step from a reachable world.
  induction h with
  | init => exact inv_init
  | step _ hst ih => exact inv_step ih hst

/-! ## Part 3. The rules -/

/-- **`no_lost_memtable`.** Every memtable ever made is active, frozen, or
has its table in the version: no publication left one out. -/
theorem no_lost_memtable {w : World} (h : Reach w) :
    -- The claim itself; its proof follows.
    ∀ m, 1 ≤ m → m ≤ w.made → m = w.view.active ∨ m ∈ w.view.frozen ∨ m ∈ w.view.tables :=
  -- One of the facts every reachable world keeps.
  (inv_reach h).no_lost

/-- **`no_lost_ingest`.** Every ingested table is in the version. -/
theorem no_lost_ingest {w : World} (h : Reach w) :
    -- The claim itself; its proof follows.
    ∀ t ∈ w.ingested, t ∈ w.view.ingests :=
  -- One of the facts every reachable world keeps.
  (inv_reach h).ingests_kept

/-- **`retired_stay_gone`.** A memtable a flush retired is never frozen or
active again, so it is never flushed twice. -/
theorem retired_stay_gone {w : World} (h : Reach w) :
    -- The claim itself; its proof follows.
    ∀ r ∈ w.retired, r ∉ w.view.frozen ∧ r ≠ w.view.active := by
  -- The facts every reachable world keeps.
  have hi := inv_reach h
  -- Take a retired memtable.
  intro r hr
  -- Its table is installed, so it is older than the active one.
  have := hi.tables_old r (hi.retired_in_tables r hr)
  -- Not frozen, and not the active one, which is the newest.
  exact ⟨hi.retired_gone r hr, by rw [hi.active_newest]; omega⟩

/-- **`frozen_sorted`.** The frozen list is in the order the memtables were
sealed, the order flushes install them in. -/
theorem frozen_sorted {w : World} (h : Reach w) :
    -- The claim itself; its proof follows.
    w.view.frozen.Pairwise (· < ·) :=
  -- One of the facts every reachable world keeps.
  (inv_reach h).frozen_sorted

/-! ## Part 4. The RED cases -/

/-- The view in the story: memtable 1 flushed and installed, 2 active. -/
def flushed : View := ⟨2, [1], [1], []⟩

/-- **`plain_retire_loses_a_seal`.** A flush built its retire of memtable 1
from `flushed`; a rotation then published its seal of 2 behind a fresh 3.
Stored without the CAS, the retire puts back active 2 and an empty frozen
list: memtable 3, which exists (three were made), is in no place. With the
CAS the retire's swap loses, and it retires 1 from the sealed view instead,
which keeps 3 active and 2 frozen (bug `PlainRetire`). -/
theorem plain_retire_loses_a_seal :
    -- What the rotation published, and what the plain store leaves.
    let sealed := rotate 3 flushed
    let stored := retire 1 flushed
    -- The plain store loses memtable 3 ...
    ¬ (3 = stored.active ∨ 3 ∈ stored.frozen ∨ 3 ∈ stored.tables) ∧
    -- ... while the CAS refuses it, and the retire built again keeps 3.
    cas sealed flushed stored = sealed ∧
    (3 = (retire 1 sealed).active ∨ 3 ∈ (retire 1 sealed).frozen) := by
  -- Every part is a computation on small lists.
  refine ⟨?_, ?_, ?_⟩
  -- 3 is not 2, and the lists are [] and [1].
  · simp [retire, flushed]
  -- The views differ, so the swap loses.
  · simp [cas, rotate, flushed]
  -- The rebuilt retire keeps 3 active.
  · simp [retire, rotate, flushed]

/-- **`plain_version_loses_a_seal`.** A compaction built its version publish
from the start (active 1, nothing frozen); a rotation then published its
seal of 1 behind a fresh 2. Stored without the CAS, the compaction's view
puts back active 1: memtable 2, which exists, is in no place (bug
`PlainVersion`). -/
theorem plain_version_loses_a_seal :
    -- What the rotation published, and what the plain store leaves.
    let sealed := rotate 2 init.view
    let stored := compact init.view
    -- The plain store loses memtable 2 ...
    ¬ (2 = stored.active ∨ 2 ∈ stored.frozen ∨ 2 ∈ stored.tables) ∧
    -- ... while the CAS refuses it.
    cas sealed init.view stored = sealed := by
  -- Both parts are computations on small lists.
  refine ⟨?_, ?_⟩
  -- 2 is not 1, and nothing is frozen or installed.
  · simp [compact, init]
  -- The views differ, so the swap loses.
  · simp [cas, rotate, init]

-- The end of this file's names.
end Regolith.ReadViewPublishers
