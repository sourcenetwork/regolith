/-!
# BackupSeal: a backup of an encrypted database seals its metadata (plan 4.12, D57)

The story. regolith's BackupEngine (`src/backup.rs`) copies a database's
tables into a shared pool, one file per table, and writes one metadata file
per backup saying which pool file each table slot gets, which keys each
table spans, and which key each table is sealed under. On an encrypted
database that file is sealed under the database's current key and names the
key; only its listing (each pool file's name and size, which the pool shows
anyway) stays in the clear, so deleting a backup needs no key. The tag
covers the listing and the backup id too. A restore takes a key provider,
checks everything before it writes anything, copies every listed table into
the target and writes a sealed MANIFEST last.

Picture backup 1 holding one table under key 1, taken before a rotation to
key 2. A restore with a provider that still holds key 1 must work; one
without a provider, without key 1, with other bytes under key 1, or after
someone edited the listing or renamed the file, must refuse, and must not
have copied a single table first.

This file backs `proofs/tla/BackupSeal.tla` (configurations
`MC_BackupSeal_*`). What is proved, for backups of every size:

1. `refusal_writes_nothing`: a refused restore made no write
   (`RefusalWritesNothing`).
2. `entitled_restore_is_faithful`: a provider with the key the file names,
   the right bytes, its own current key and every table's key restores an
   untouched file, whatever key is current: it copies exactly the tables the
   tag covers and writes a MANIFEST sealed under a key it has
   (`RightKeysRestore`, `FaithfulRestore`).
3. The refusals: no provider, a missing key, a wrong key, an edited
   listing, a renamed file, a current or table key the provider lacks, and
   a target that already holds a MANIFEST.
4. `restored_manifest_is_sealed`: with a provider, every MANIFEST a restore
   writes is sealed (`SealedMetadata`).
5. `last_write_holds_all`, with `restore_manifest_follows_its_tables` and
   `backup_metadata_follows_its_tables`: whatever prefix of the writes a
   power cut keeps, if it kept the last write it kept every one before it
   (`FaithfulRestore`, `ListedRestores` under power cuts).
6. `collect_keeps_listed`: a delete never removes a pool file another
   backup lists (`ListedRestores`).
7. `collect_stream_eq` and `stream_keeps_listed`: the streamed delete, which
   reads each listing as its walk of `meta/` reaches it, removes exactly
   what the delete with every listing in hand removes, whatever batches and
   order the walk hands the listings out in, so it too never removes a
   listed file (`ListedRestores` with `WalkNext`).
8. `stream_holds_one_listing`: its candidates never outgrow the deleted
   backup's own listing, however many backups there are
   (`CollectionBounded`).
9. `list_pages_all`: listing the backups a page of ids at a time, each page
   the smallest ids above the last one listed, names every backup once, in
   id order, for every page size (`src/backup/listing.rs`).
10. The RED cases as counterexamples, one per defect of the model, with
   `stream_skip_removes_a_listed_file` for `StreamSkips` and
   `page_skip_loses_a_backup` for a page that starts one id too far.
-/

-- Everything below lives in its own namespace.
namespace Regolith.BackupSeal

/-- One backup's metadata file as a restore reads it
(`src/backup/format.rs`, version 4). -/
structure Meta where
  /-- The key id it is sealed under and names; `none` when it is plain. -/
  key : Option Nat
  /-- The clear listing: the pool file each table slot is copied from, as
  the file says now. -/
  listing : List Nat
  /-- The listing as it was when the tag was computed. -/
  sealedListing : List Nat
  /-- The key id each listed table names in its own footer. -/
  tableKeys : List Nat
  /-- The backup id the tag binds: the file's name when it was written. -/
  bound : Nat

/-- The key provider a restore is given (`KeyProvider`). -/
structure Provider where
  /-- Whether it hands back a key under id `k` (`KeyProvider::key`). -/
  has : Nat → Bool
  /-- Whether those keys are the bytes that sealed the files. -/
  right : Bool
  /-- The key it names current (`KeyProvider::current`). -/
  cur : Nat

/-- One write a restore makes into the target. -/
inductive Write where
  /-- A table copied from pool file `obj` (`copy_file_atomic`). -/
  | copy (obj : Nat)
  /-- The MANIFEST, sealed under `sealedUnder`, or plain when `none`. -/
  | manifest (sealedUnder : Option Nat)
  -- Two writes can be compared, so `decide` can check small examples.
  deriving DecidableEq

/-- What a restore did: its writes, in order, and whether it refused. -/
structure Run where
  /-- Every write, first to last. -/
  writes : List Write
  /-- Whether it returned a refusal. -/
  refused : Bool
  -- Two runs can be compared, so `decide` can check small examples.
  deriving DecidableEq

/-- Whether the file opens as backup `id` under the provider
(`format::decode`): plain metadata needs no key; sealed metadata needs a
provider, the key the file names, the right bytes, the listing the tag
covers, and the id the tag binds. -/
def opens (id : Nat) (m : Meta) : Option Provider → Bool
  -- No provider: only a plain file opens (Error::KeyProviderRequired).
  | none => m.key.isNone
  -- A provider: a plain file opens; a sealed one needs every check.
  | some p => match m.key with
    -- Plain: nothing to check.
    | none => true
    -- Sealed under key k: the key, the bytes, the listing and the id.
    | some k => p.has k && p.right && m.listing == m.sealedListing && m.bound == id

/-- Whether the provider has its current key, which the MANIFEST is sealed
under, and the key every table names; with no provider nothing is sealed. -/
def keysProvided (m : Meta) : Option Provider → Bool
  -- No provider: nothing to provide.
  | none => true
  -- A provider: its current key and each table's key.
  | some p => p.has p.cur && m.tableKeys.all p.has

/-- The engine's restore (`BackupEngine::restore`). `hasManifest` is
whether the target already holds a MANIFEST. Every check comes first; then
every listed table is copied, and the MANIFEST is written last, sealed
under the current key when there is a provider. -/
def restore (hasManifest : Bool) (id : Nat) (m : Meta) (p : Option Provider) : Run :=
  -- Every check before the first write.
  if !hasManifest && opens id m p && keysProvided m p then
    -- The copies, in listing order, then the MANIFEST.
    ⟨m.listing.map Write.copy ++ [Write.manifest (p.map Provider.cur)], false⟩
  -- Any check failed: refuse, having written nothing.
  else ⟨[], true⟩

/-! ## What the engine guarantees -/

/-- **A refused restore wrote nothing.** It rules out a target left half
written behind an error: every check runs before the first copy. -/
theorem refusal_writes_nothing (h : Bool) (id : Nat) (m : Meta) (p : Option Provider) :
    (restore h id m p).refused = true → (restore h id m p).writes = [] := by
  -- Open up the restore, then look at both of its branches.
  unfold restore
  -- In the branch that restores, `refused` is false, so the premise is
  -- impossible; in the branch that refuses, the writes are empty.
  split <;> simp

/-- **The right keys restore exactly what the backup holds.** A provider
with the key the file names, the right bytes, its current key and every
table's key, given an untouched file of this id and an empty target, never
refuses: it copies exactly the tables the tag covers and writes a MANIFEST
sealed under its current key. Nothing asks that key to be the one the file
names: a backup taken before a rotation restores after it. -/
theorem entitled_restore_is_faithful (id k : Nat) (m : Meta) (p : Provider)
    -- The file is sealed under key k...
    (hkey : m.key = some k)
    -- ...the provider has key k...
    (hk : p.has k = true)
    -- ...with the right bytes...
    (hr : p.right = true)
    -- ...nobody edited the listing...
    (hl : m.listing = m.sealedListing)
    -- ...the file is this id's own...
    (hb : m.bound = id)
    -- ...the provider has its current key...
    (hcur : p.has p.cur = true)
    -- ...and every table's key.
    (ht : m.tableKeys.all p.has = true) :
    restore false id m (some p) =
      ⟨m.sealedListing.map Write.copy ++ [Write.manifest (some p.cur)], false⟩ := by
  -- Every check passes by the hypotheses, so the restore takes its first
  -- branch, whose writes are the sealed listing's copies and the MANIFEST.
  simp [restore, opens, keysProvided, hkey, hk, hr, hl, hb, hcur, ht]

/-- **No provider, no restore** of a sealed file (Error::KeyProviderRequired). -/
theorem no_provider_refuses (h : Bool) (id k : Nat) (m : Meta)
    -- The file is sealed.
    (hkey : m.key = some k) :
    (restore h id m none).refused = true := by
  -- The file does not open without a provider, so the restore refuses.
  simp [restore, opens, hkey]

/-- **A key the provider lacks refuses** (Error::UnknownKey). -/
theorem missing_key_refuses (h : Bool) (id k : Nat) (m : Meta) (p : Provider)
    -- The file is sealed under key k.
    (hkey : m.key = some k)
    -- The provider has no key k.
    (hk : p.has k = false) :
    (restore h id m (some p)).refused = true := by
  -- The file does not open, so the restore refuses.
  simp [restore, opens, hkey, hk]

/-- **Other bytes under the right id refuse** (the tag fails). -/
theorem wrong_key_refuses (h : Bool) (id k : Nat) (m : Meta) (p : Provider)
    -- The file is sealed under key k.
    (hkey : m.key = some k)
    -- The provider's bytes are not the ones that sealed it.
    (hr : p.right = false) :
    (restore h id m (some p)).refused = true := by
  -- The file does not open, so the restore refuses.
  simp [restore, opens, hkey, hr]

/-- **An edited listing refuses**: the tag covers the listing. -/
theorem edited_listing_refuses (h : Bool) (id k : Nat) (m : Meta) (p : Option Provider)
    -- The file is sealed under key k.
    (hkey : m.key = some k)
    -- Someone changed the listing after the tag was computed.
    (hl : m.listing ≠ m.sealedListing) :
    (restore h id m p).refused = true := by
  -- With or without a provider, look at each case.
  cases p with
  -- No provider: a sealed file never opens.
  | none => simp [restore, opens, hkey]
  -- A provider: the listing check fails.
  | some p => simp [restore, opens, hkey, hl]

/-- **A renamed file refuses**: the tag binds the backup id. -/
theorem renamed_file_refuses (h : Bool) (id k : Nat) (m : Meta) (p : Option Provider)
    -- The file is sealed under key k.
    (hkey : m.key = some k)
    -- It was written as another backup's file.
    (hb : m.bound ≠ id) :
    (restore h id m p).refused = true := by
  -- With or without a provider, look at each case.
  cases p with
  -- No provider: a sealed file never opens.
  | none => simp [restore, opens, hkey]
  -- A provider: the id check fails.
  | some p => simp [restore, opens, hkey, hb]

/-- **A current key the provider lacks refuses**, before anything is
written: the MANIFEST could not be sealed. -/
theorem unprovided_current_refuses (h : Bool) (id : Nat) (m : Meta) (p : Provider)
    -- The provider does not have the key it names current.
    (hcur : p.has p.cur = false) :
    (restore h id m (some p)).refused = true := by
  -- The key check fails, so the restore refuses.
  simp [restore, keysProvided, hcur]

/-- **A table key the provider lacks refuses**, before anything is written:
the restored database could not open that table. -/
theorem unprovided_table_key_refuses (h : Bool) (id t : Nat) (m : Meta) (p : Provider)
    -- A listed table names key t...
    (ht : t ∈ m.tableKeys)
    -- ...which the provider does not have.
    (hmiss : p.has t = false) :
    (restore h id m (some p)).refused = true := by
  -- Not every table key is provided: the one at `t` is the witness.
  have hall : m.tableKeys.all p.has = false := by
    -- `all` is false when some member fails; `t` is that member.
    simp only [List.all_eq_false]
    -- Name it, and show it fails.
    exact ⟨t, ht, by simp [hmiss]⟩
  -- The key check fails, so the restore refuses.
  simp [restore, keysProvided, hall]

/-- **A target that already holds a MANIFEST refuses**: restoring over a
database would replace tables its MANIFEST names. -/
theorem finished_target_refuses (id : Nat) (m : Meta) (p : Option Provider) :
    (restore true id m p).refused = true := by
  -- The first check fails, so the restore refuses.
  simp [restore]

/-- **Every MANIFEST a restore writes with a provider is sealed**, under a
key that provider has. -/
theorem restored_manifest_is_sealed (h : Bool) (id : Nat) (m : Meta) (p : Provider)
    (w : Option Nat)
    -- The restore wrote a MANIFEST sealed under `w`.
    (hw : Write.manifest w ∈ (restore h id m (some p)).writes) :
    w = some p.cur ∧ p.has p.cur = true := by
  -- Open up the restore and look at its two branches.
  unfold restore at hw
  -- Split on whether every check passed.
  split at hw
  -- They passed: the condition holds, and the write is one of the restore's.
  · rename_i hpass
    -- A passing check includes the current key.
    have hcur : p.has p.cur = true := by
      -- Pull the key check out of the conjunction of checks.
      simp only [Bool.and_eq_true, keysProvided] at hpass
      -- It is the first half of the key check.
      exact hpass.2.1
    -- The MANIFEST is the last write; no copy is a MANIFEST.
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hw
    -- So `w` is the current key, and the provider has it.
    rcases hw with ⟨_, _, hc⟩ | heq
    -- A copy is not a MANIFEST.
    · cases hc
    -- The MANIFEST names the current key.
    · cases heq
      -- Both halves hold.
      exact ⟨rfl, hcur⟩
  -- They failed: no write at all, so nothing to show.
  · simp at hw

/-! ## Power cuts: the last write comes after every other -/

/-- **A prefix that kept the last write kept every write.** Every file is
written whole or not at all, and the writes land in order, so what a power
cut leaves is a prefix of them. If `x` is written last and nowhere before,
any prefix holding `x` holds all of `xs`. -/
theorem last_write_holds_all {α : Type} (xs : List α) (x : α)
    -- `x` is not among the writes before it.
    (hx : x ∉ xs) :
    -- For every prefix length the power cut leaves...
    ∀ n, x ∈ (xs ++ [x]).take n →
      -- ...holding `x`, every earlier write is in it too.
      ∀ y ∈ xs, y ∈ (xs ++ [x]).take n := by
  -- Take the prefix length, the fact that it holds `x`, and a write `y`.
  intro n hn y hy
  -- Write the prefix as a prefix of `xs` followed by a prefix of `[x]`.
  rw [List.take_append] at hn ⊢
  -- Either the cut fell after every write of `xs`, or inside them.
  by_cases hlen : xs.length ≤ n
  -- After them: the prefix of `xs` is all of `xs`, so `y` is in it.
  · rw [List.take_of_length_le hlen]
    -- `y` is in the left part.
    exact List.mem_append_left _ hy
  -- Inside them: nothing of `[x]` is in the prefix.
  · have hzero : n - xs.length = 0 := by omega
    -- So the prefix is part of `xs` alone.
    rw [hzero, List.take_zero, List.append_nil] at hn
    -- Then `x` would be in `xs`, which it is not.
    exact absurd (List.mem_of_mem_take hn) hx

/-- **The restored MANIFEST follows its tables**: a power cut that kept the
MANIFEST kept every table copy before it. -/
theorem restore_manifest_follows_its_tables (listing : List Nat) (w : Option Nat) :
    ∀ n, Write.manifest w ∈ (listing.map Write.copy ++ [Write.manifest w]).take n →
      ∀ c ∈ listing.map Write.copy,
        c ∈ (listing.map Write.copy ++ [Write.manifest w]).take n := by
  -- The MANIFEST is not a copy, so the general fact applies.
  apply last_write_holds_all
  -- No copy is a MANIFEST.
  simp

/-- One write a backup makes. -/
inductive Put where
  /-- A table copied into the pool, as pool file `obj`. -/
  | pool (obj : Nat)
  /-- The backup's metadata file. -/
  | metadata
  -- Two writes can be compared.
  deriving DecidableEq

/-- The engine's backup (`BackupEngine::create_backup`): every table into
the pool, then the metadata. -/
def backupWrites (objs : List Nat) : List Put :=
  -- The pool copies first, the metadata last.
  objs.map Put.pool ++ [Put.metadata]

/-- **A backup's metadata follows its tables**: a power cut that kept the
metadata kept every pool copy it lists. -/
theorem backup_metadata_follows_its_tables (objs : List Nat) :
    ∀ n, Put.metadata ∈ (backupWrites objs).take n →
      ∀ c ∈ objs.map Put.pool, c ∈ (backupWrites objs).take n := by
  -- The metadata is not a pool copy, so the general fact applies.
  apply last_write_holds_all
  -- No pool copy is the metadata.
  simp

/-! ## Deleting a backup -/

/-- The pool files a delete removes (`gc_shared`): those the deleted backup
listed that no remaining backup's listing names. Every listing counts,
sealed or not: each is readable without a key. -/
def collect (removed : List Nat) (remaining : List (List Nat)) : List Nat :=
  -- Keep each removed file that no remaining listing contains.
  removed.filter fun o => !(remaining.any fun l => l.contains o)

/-- **A delete never removes a file another backup lists.** -/
theorem collect_keeps_listed (removed : List Nat) (remaining : List (List Nat)) (o : Nat)
    -- The delete removes `o`.
    (h : o ∈ collect removed remaining) :
    -- Then no remaining listing names `o`.
    ∀ l ∈ remaining, o ∉ l := by
  -- Take a remaining listing, and suppose it names `o`.
  intro l hl ho
  -- Being collected means being in `removed` and in no remaining listing.
  simp only [collect, List.mem_filter, Bool.not_eq_true', List.any_eq_false] at h
  -- That listing names `o`, which contradicts it.
  exact h.2 l hl (by simp [ho])

/-! ## Deleting a backup, streamed

`gc_shared` does not gather every other listing before it decides. It walks
`meta/` one entry at a time (`Env::read_dir` hands entries out a batch at a
time, the way `readdir` fills its buffer), reads each listing as the walk
reaches it, and strikes from the candidates every file that listing names.
Only when the walk has handed out its last entry does it remove what is
left.

Picture backup 1 deleted, backups 2 and 3 left, backups 1 and 3 sharing
pool file 5. The walk hands out backup 2, which strikes nothing, then
backup 3, which strikes 5: file 5 stays. The theorems below show this is
the same decision `collect` makes with every listing in hand, for every
number of backups and every way the walk can batch and order them, and
that the candidates never outgrow the deleted backup's own listing. -/

/-- One read of the walk: keep only the candidates listing `l` does not
name. -/
def strike (cand : List Nat) (l : List Nat) : List Nat :=
  -- A candidate the listing names must stay in the pool, so it stops being
  -- a candidate.
  cand.filter fun o => !l.contains o

/-- The streamed collection: the walk hands out the remaining backups'
listings in `batches`, each batch in its order, and each listing is struck
as it comes. What is left is what the delete removes. -/
def collectStream (removed : List Nat) (batches : List (List (List Nat))) : List Nat :=
  -- Start from the deleted backup's own files, and strike batch after
  -- batch, listing after listing.
  batches.foldl (fun cand batch => batch.foldl strike cand) removed

/-- Striking listing after listing is one filter: keep the files that no
listing names. -/
theorem foldl_strike (ls : List (List Nat)) (cand : List Nat) :
    ls.foldl strike cand = cand.filter fun o => !(ls.any fun l => l.contains o) := by
  -- Peel the listings off one at a time, for every starting candidate list.
  induction ls generalizing cand with
  -- No listing: nothing is struck, and "no listing names it" keeps all,
  -- since a filter that keeps every file is the list itself.
  | nil => exact (List.filter_eq_self.mpr fun _ _ => rfl).symm
  -- One listing `l`, then the rest.
  | cons l ls ih =>
    -- Strike `l` first, then the rest by the hypothesis; two filters in a
    -- row are one filter by "and", which is "neither `l` nor the rest".
    simp only [List.foldl_cons, ih, strike, List.filter_filter, List.any_cons, Bool.not_or,
      Bool.and_comm]

/-- **However the walk batches and orders the listings, the streamed
collection removes exactly what the collection with every listing in hand
removes.** -/
theorem collect_stream_eq (removed : List Nat) (batches : List (List (List Nat))) :
    collectStream removed batches = collect removed batches.flatten := by
  -- Peel the batches off one at a time, for every starting candidate list.
  induction batches generalizing removed with
  -- No batch: nothing read, nothing struck, both keep every file, since a
  -- filter that keeps every file is the list itself.
  | nil => exact (List.filter_eq_self.mpr fun _ _ => rfl).symm
  -- One batch, then the rest.
  | cons batch rest ih =>
    -- The first batch strikes what its listings name; the rest strike the
    -- remainder by the hypothesis; together that is one filter by "named
    -- by no listing of the first batch or of the rest".
    simp only [collectStream, List.foldl_cons] at ih ⊢
    -- Rewrite the rest of the walk with the hypothesis, the first batch
    -- with `foldl_strike`, and merge the two filters into one.
    rw [ih, foldl_strike]
    -- What is left is the same filter written two ways.
    simp only [collect, List.filter_filter, List.flatten_cons, List.any_append, Bool.not_or,
      Bool.and_comm]

/-- **A streamed delete never removes a file another backup lists**,
whatever batches the walk makes. -/
theorem stream_keeps_listed (removed : List Nat) (batches : List (List (List Nat))) (o : Nat)
    -- The streamed delete removes `o`.
    (h : o ∈ collectStream removed batches) :
    -- Then no listing the walk handed out names `o`.
    ∀ l ∈ batches.flatten, o ∉ l := by
  -- The streamed collection is the one with every listing in hand...
  rw [collect_stream_eq] at h
  -- ...which never removes a listed file.
  exact collect_keeps_listed _ _ _ h

/-- **The collection holds one listing's worth**: after any number of
listings read, in any batches, the candidates are a sublist of the deleted
backup's own files, so their number never passes that listing's length,
however many backups the repository keeps. -/
theorem stream_holds_one_listing (removed : List Nat) (batches : List (List (List Nat))) :
    (collectStream removed batches).Sublist removed ∧
      (collectStream removed batches).length ≤ removed.length := by
  -- What is left is a filter of the deleted listing...
  have sub : (collectStream removed batches).Sublist removed := by
    -- ...by the theorem above...
    rw [collect_stream_eq]
    -- ...and a filter keeps a sublist.
    exact List.filter_sublist
  -- A sublist is no longer than the list it comes from.
  exact ⟨sub, sub.length_le⟩

/-! ## Listing the backups, a page at a time

`BackupEngine::list_backups` (`src/backup/listing.rs`) lists every backup in
id order without holding every id. Each page is one walk of `meta/` that
keeps the `k` smallest ids above the last one listed (`page_after`, a heap
of `k`), and a page that comes back short is the last (`Backups::next`).

Picture ids 1 to 5 and pages of 2. Page one: 1, 2. Page two, above 2: 3, 4.
Page three, above 4: just 5, short, so the listing ends: 1, 2, 3, 4, 5.
The theorems below show the pages always add up to every id, once, in
order, for every number of ids and every page size; the RED shows what one
id too far at a page boundary loses.

`s` stands for every id `meta/` holds, ascending (`page_after` returns its
page sorted, whatever order the directory walk met the ids in). -/

/-- Whether id `x` comes after the last id listed, `a`: every id does
before the first page. -/
def above (a : Option Nat) (x : Nat) : Bool :=
  -- No id listed yet: everything is ahead. Otherwise only the larger ids.
  a.all (· < x)

/-- One page (`page_after`): the `k` smallest ids above `a`, ascending. -/
def page (s : List Nat) (a : Option Nat) (k : Nat) : List Nat :=
  -- The ids above `a`, in order, cut after the first `k`.
  (s.filter (above a)).take k

/-- The listing (`Backups::next`): page after page, each starting above the
last id of the one before, until a page comes back short. `fuel` only
bounds the recursion; one more than the number of ids is always enough. -/
def listPages (s : List Nat) (k : Nat) : Nat → Option Nat → List Nat
  -- Out of fuel: nothing more (never reached with enough fuel).
  | 0, _ => []
  -- Take the page above `a`...
  | fuel + 1, a =>
    -- ...and stop there when it is short...
    if (page s a k).length < k then page s a k
    -- ...or go on above its last id.
    else page s a k ++ listPages s k fuel (page s a k).getLast?

/-- In a list in strictly rising order, nothing comes after the last
element: every element is at most the last one. -/
theorem le_last {t : List Nat} (h : t.Pairwise (· < ·)) {m : Nat} (hm : t.getLast? = some m) :
    ∀ x ∈ t, x ≤ m := by
  -- Take any element `x` of the list.
  intro x hx
  -- A list with a last element is not empty.
  have hne : t ≠ [] := by intro e; simp [e] at hm
  -- Its last element is `m`.
  have hlast : t.getLast hne = m := by
    -- `getLast?` of a non-empty list is `getLast`, so the two agree.
    rw [List.getLast?_eq_some_getLast hne] at hm; exact Option.some.inj hm
  -- Split the list into everything before the last element, and the last.
  rw [← List.dropLast_concat_getLast hne] at h hx
  -- `x` is either before the last element or is the last element.
  rcases List.mem_append.mp hx with hx | hx
  -- Before it: the order puts `x` below the last element, which is `m`.
  · have := (List.pairwise_append.mp h).2.2 x hx (t.getLast hne) (by simp)
    -- So `x < m`, and in particular `x ≤ m`.
    omega
  -- It is the last element: `x = m`.
  · simp at hx; omega

/-- The page boundary loses nothing and repeats nothing: the ids above the
last id of a page are exactly the ids after that page. -/
theorem above_last_is_rest {s : List Nat} (hs : s.Pairwise (· < ·)) (a : Option Nat) (k : Nat)
    {m : Nat} (hm : ((s.filter (above a)).take k).getLast? = some m) :
    s.filter (above (some m)) = (s.filter (above a)).drop k := by
  -- Call the ids above `a` by one name, `u`.
  generalize hu : s.filter (above a) = u at hm
  -- They rise strictly, as every part of `s` does.
  have hu_pw : u.Pairwise (· < ·) := hu ▸ hs.filter _
  -- `u` is the page followed by the rest.
  have hsplit := List.take_append_drop k u
  -- `m`, the page's last id, is on the page...
  have hmt : m ∈ u.take k := List.mem_of_getLast? hm
  -- ...so it is one of the ids above `a`...
  have hmu : m ∈ u := List.mem_of_mem_take hmt
  -- ...which means `m` itself is above `a`.
  have ham : above a m = true := by
    -- Membership in a filter says the filter's test held.
    rw [← hu] at hmu; exact (List.mem_filter.mp hmu).2
  -- An id above `m` is above `a` too, so filtering `s` by "above `m`" is
  -- filtering the ids above `a` by it.
  have hfilter : s.filter (above (some m)) = u.filter (above (some m)) := by
    -- Two filters in a row are one filter by "and".
    rw [← hu, List.filter_filter]
    -- Show the two tests agree on every id.
    apply List.filter_congr
    -- Take any id `x`.
    intro x _
    -- Whether there was a last id `a` or not.
    cases a with
    -- No `a`: "above `a`" is always true, so both tests are "above `m`".
    | none => simp [above]
    -- Some `a` below `m`.
    | some a =>
      -- Spell both tests out as comparisons.
      simp only [above, Option.all_some, decide_eq_true_eq] at ham ⊢
      -- Either `x` is above `m` or it is not.
      by_cases h : m < x
      -- Above `m`, so above `a` as well, since `a < m`: both tests pass.
      · simp [h, Nat.lt_trans ham h]
      -- Not above `m`: both tests fail.
      · simp [h]
  -- The order across the split: the page rises, the rest rises, and every
  -- page id is below every later id.
  have hpw := hsplit ▸ hu_pw
  -- Spell that out in its three parts.
  rw [List.pairwise_append] at hpw
  -- Nothing on the page is above its last id.
  have hnil : (u.take k).filter (above (some m)) = [] := by
    -- A filter is empty when no element passes it.
    rw [List.filter_eq_nil_iff]
    -- Take a page id `x`.
    intro x hx
    -- It is at most the page's last id.
    have := le_last hpw.1 hm x hx
    -- So it is not above it.
    simp [above]; omega
  -- Everything after the page is above its last id.
  have hall : (u.drop k).filter (above (some m)) = u.drop k := by
    -- A filter keeps the whole list when every element passes it.
    rw [List.filter_eq_self]
    -- Take an id `x` after the page.
    intro x hx
    -- The page's last id is below it.
    have := hpw.2.2 m hmt x hx
    -- So it is above `m`.
    simp [above]; omega
  -- Put it together: filtering `u` by "above `m`" drops the page, keeps the rest.
  rw [hfilter]
  -- Write `u` as the page and the rest...
  calc u.filter (above (some m)) = (u.take k ++ u.drop k).filter (above (some m)) := by
        -- ...which it is.
        rw [hsplit]
    -- ...filter each part: the page leaves nothing, the rest stays whole.
    _ = u.drop k := by rw [List.filter_append, hnil, hall, List.nil_append]

/-- **Page after page, the listing gives every id above `a`, once, in
order**, for every page size `k` of at least one, given fuel past the
number of those ids. -/
theorem list_pages {s : List Nat} (hs : s.Pairwise (· < ·)) {k : Nat} (hk : 0 < k) :
    ∀ fuel a, (s.filter (above a)).length < fuel → listPages s k fuel a = s.filter (above a) := by
  -- By induction on the fuel.
  intro fuel
  -- One page at a time.
  induction fuel with
  -- No fuel: impossible, since the number of ids is below it.
  | zero => intro a h; omega
  -- Fuel for one more page.
  | succ fuel ih =>
    -- Take any last id `a`, with fewer ids above it than the fuel.
    intro a hlen
    -- Unfold one step of the listing.
    rw [listPages]
    -- Either this page comes back short or it is full.
    by_cases hshort : (page s a k).length < k
    -- Short: the listing ends with it.
    · simp only [hshort, ↓reduceIte]
      -- Spell the page out.
      unfold page at hshort ⊢
      -- A short page is shorter than `k` because the ids ran out.
      rw [List.length_take] at hshort
      -- So the page is every id above `a`.
      rw [List.take_of_length_le]
      -- That is what the shortness says.
      omega
    -- Full: the listing goes on above the page's last id.
    · simp only [hshort, ↓reduceIte]
      -- Spell the page out.
      unfold page at hshort ⊢
      -- A full page of at least one id is not empty...
      have hne : (s.filter (above a)).take k ≠ [] := by
        -- ...since an empty page would be short.
        intro e; rw [e] at hshort; simp at hshort; omega
      -- ...so it has a last id `m`.
      obtain ⟨m, hm⟩ : ∃ m, ((s.filter (above a)).take k).getLast? = some m :=
        -- `getLast?` of a non-empty list is its last element.
        ⟨_, List.getLast?_eq_some_getLast hne⟩
      -- The rest of the listing is every id above `m` (the hypothesis),
      -- which is every id after the page (the boundary theorem), and the
      -- page followed by the ids after it is every id above `a`.
      rw [hm, ih (some m), above_last_is_rest hs a k hm, List.take_append_drop]
      -- Left to show: fewer ids above `m` than the fuel that remains.
      rw [above_last_is_rest hs a k hm, List.length_drop]
      -- The full page took `k` of them, and `k` is at least one.
      rw [List.length_take] at hshort
      -- So the count fell by at least one, below the remaining fuel.
      omega

/-- **The listing names every backup once, in id order**, whatever the
page size. -/
theorem list_pages_all {s : List Nat} (hs : s.Pairwise (· < ·)) {k : Nat} (hk : 0 < k) :
    listPages s k (s.length + 1) none = s := by
  -- Before the first page every id is ahead.
  have hnone : s.filter (above none) = s := List.filter_eq_self.mpr fun _ _ => rfl
  -- The theorem above, with one more fuel than ids.
  rw [list_pages hs hk (s.length + 1) none (by rw [hnone]; omega), hnone]

/-! ## The defects, as counterexamples -/

/-- The defect a page boundary invites: the next page starts above the id
after the last one listed (`id <= after + 1` for `id <= after`). -/
def listPagesSkip (s : List Nat) (k : Nat) : Nat → Option Nat → List Nat
  -- Out of fuel: nothing more.
  | 0, _ => []
  -- The page above `a`, one id too far...
  | fuel + 1, a =>
    -- ...the ids more than one above `a`, cut after `k`...
    let p := (s.filter fun x => a.all (· + 1 < x)).take k
    -- ...ending when short, otherwise going on above its last id.
    if p.length < k then p else p ++ listPagesSkip s k fuel p.getLast?

/-- **RED: one id too far at a page boundary.** Backups 1, 2 and 3, one per
page: the engine lists all three; the defect starts the second page above
2 and never lists backup 2, so a purge would never count it. -/
theorem page_skip_loses_a_backup :
    -- The engine lists every backup...
    listPages [1, 2, 3] 1 4 none = [1, 2, 3] ∧
    -- ...the defect loses backup 2.
    listPagesSkip [1, 2, 3] 1 4 none = [1, 3] :=
  -- Both are evaluations Lean can run.
  ⟨by decide, by decide⟩

/-- The defect `StreamSkips`: once the first batch is used up, the walk
starts every later batch one entry too far, so the first listing of each
batch after the first is never read. -/
def skipAtBoundary : List (List (List Nat)) → List (List (List Nat))
  -- No batch: nothing to lose.
  | [] => []
  -- The first batch comes whole; each later one loses its first listing.
  | first :: rest => first :: rest.map List.tail

/-- **RED `StreamSkips`.** Backup 1 is deleted; it and backup 3 list pool
file 5, backup 2 lists file 7. The walk hands out backup 2 in one batch and
backup 3 in the next. The engine keeps file 5; the defect loses backup 3's
listing at the boundary and removes file 5, which backup 3 still lists. -/
theorem stream_skip_removes_a_listed_file :
    -- The engine removes nothing...
    collectStream [5] [[[7]], [[5]]] = [] ∧
    -- ...the defect removes file 5...
    collectStream [5] (skipAtBoundary [[[7]], [[5]]]) = [5] ∧
    -- ...and file 5 is in a listing the walk had to hand out.
    [5] ∈ ([[[7]], [[5]]] : List (List (List Nat))).flatten :=
  -- Each is an evaluation Lean can run.
  ⟨by decide, by decide, by decide⟩

/-- The defect `CheckAfterCopy`: the key checks run after the copies. -/
def restoreCheckAfterCopy (hasManifest : Bool) (id : Nat) (m : Meta) (p : Option Provider) : Run :=
  -- The file still has to open and the target has to be empty...
  if !hasManifest && opens id m p then
    -- ...then the copies are made, and only then the keys checked.
    if keysProvided m p then
      ⟨m.listing.map Write.copy ++ [Write.manifest (p.map Provider.cur)], false⟩
    -- A refusal after the copies.
    else ⟨m.listing.map Write.copy, true⟩
  -- The file does not open: refuse with nothing written.
  else ⟨[], true⟩

/-- A provider with key 1 only, which names key 2 current. -/
def lacksCurrent : Provider := ⟨fun k => k == 1, true, 2⟩

/-- Backup 1: one table, pool file 5, sealed under key 1. -/
def backupOne : Meta := ⟨some 1, [5], [5], [1], 1⟩

/-- **RED `CheckAfterCopy`.** The engine refuses with nothing written; the
defect refuses after copying the table. -/
theorem check_after_copy_writes_before_refusing :
    -- The engine: refused, nothing written...
    restore false 1 backupOne (some lacksCurrent) = ⟨[], true⟩ ∧
    -- ...the defect: refused, the table already copied.
    restoreCheckAfterCopy false 1 backupOne (some lacksCurrent) = ⟨[Write.copy 5], true⟩ :=
  -- Both sides are evaluations Lean can run.
  ⟨by decide, by decide⟩

/-- The defects `ListingUnbound` and `IdUnbound`: the tag covers neither the
listing nor the id. -/
def opensUnbound (m : Meta) : Option Provider → Bool
  -- No provider: only a plain file opens.
  | none => m.key.isNone
  -- A provider: only the key and the bytes are checked.
  | some p => match m.key with
    -- Plain: nothing to check.
    | none => true
    -- Sealed: the key and the bytes, nothing else.
    | some k => p.has k && p.right

/-- The restore with the unbound tag. -/
def restoreUnbound (m : Meta) (p : Option Provider) : Run :=
  -- The same checks, less the listing and the id.
  if opensUnbound m p && keysProvided m p then
    ⟨m.listing.map Write.copy ++ [Write.manifest (p.map Provider.cur)], false⟩
  else ⟨[], true⟩

/-- A provider with both keys and the right bytes, key 1 current. -/
def bothKeys : Provider := ⟨fun k => k == 1 || k == 2, true, 1⟩

/-- Backup 1 with its listing edited to name pool file 9, another backup's
copy of the table. -/
def editedOne : Meta := ⟨some 1, [9], [5], [1], 1⟩

/-- Backup 2's file, holding pool file 7, under backup 1's name. -/
def renamedTwo : Meta := ⟨some 1, [7], [7], [1], 2⟩

/-- **RED `ListingUnbound` and `IdUnbound`.** The engine refuses both
files; the defect copies pool file 9 for a backup that recorded 5, and
restores backup 2's table as backup 1. -/
theorem unbound_tag_restores_other_tables :
    -- The engine refuses the edited listing...
    (restore false 1 editedOne (some bothKeys)).refused = true ∧
    -- ...the defect copies pool file 9...
    restoreUnbound editedOne (some bothKeys) =
      ⟨[Write.copy 9, Write.manifest (some 1)], false⟩ ∧
    -- ...the engine refuses the renamed file...
    (restore false 1 renamedTwo (some bothKeys)).refused = true ∧
    -- ...and the defect restores backup 2 as backup 1.
    restoreUnbound renamedTwo (some bothKeys) =
      ⟨[Write.copy 7, Write.manifest (some 1)], false⟩ :=
  -- Each is an evaluation Lean can run.
  ⟨by decide, by decide, by decide, by decide⟩

/-- The defect `OpenUnderCurrent`: the file is opened under the provider's
current key instead of the key it names. -/
def opensUnderCurrent (id : Nat) (m : Meta) : Option Provider → Bool
  -- No provider: only a plain file opens.
  | none => m.key.isNone
  -- A provider: the current key must be the one that sealed the file.
  | some p => match m.key with
    -- Plain: nothing to check.
    | none => true
    -- Sealed under k: opened under the current key, which must be k.
    | some k => p.cur == k && p.has k && p.right && m.listing == m.sealedListing && m.bound == id

/-- A provider after a rotation: both keys, key 2 current. -/
def rotated : Provider := ⟨fun k => k == 1 || k == 2, true, 2⟩

/-- **RED `OpenUnderCurrent`.** Backup 1, sealed under key 1, restored after
a rotation to key 2 with both keys: the engine restores it, the defect
refuses a provider that has every key it needs. -/
theorem open_under_current_refuses_after_a_rotation :
    -- The engine restores, the MANIFEST sealed under key 2...
    restore false 1 backupOne (some rotated) = ⟨[Write.copy 5, Write.manifest (some 2)], false⟩ ∧
    -- ...the defect's check refuses to open the file.
    opensUnderCurrent 1 backupOne (some rotated) = false :=
  -- Both are evaluations Lean can run.
  ⟨by decide, by decide⟩

/-- The defect `PlainRestore`: the MANIFEST is plain even with a provider. -/
def restorePlain (hasManifest : Bool) (id : Nat) (m : Meta) (p : Option Provider) : Run :=
  -- The engine's checks...
  if !hasManifest && opens id m p && keysProvided m p then
    -- ...but a plain MANIFEST.
    ⟨m.listing.map Write.copy ++ [Write.manifest none], false⟩
  else ⟨[], true⟩

/-- **RED `PlainRestore`.** With the right key the engine seals the MANIFEST
under key 1; the defect writes it plain. -/
theorem plain_restore_writes_a_plain_manifest :
    -- The engine: sealed under key 1...
    Write.manifest (some 1) ∈ (restore false 1 backupOne (some bothKeys)).writes ∧
    -- ...the defect: plain.
    Write.manifest none ∈ (restorePlain false 1 backupOne (some bothKeys)).writes :=
  -- Both are evaluations Lean can run.
  ⟨by decide, by decide⟩

/-- **RED `OverDatabase`.** Without the engine's first check, a restore over
a target that holds a MANIFEST copies tables over the ones it names. -/
theorem over_database_copies_over_named_tables :
    -- The engine refuses a finished target...
    restore true 1 backupOne (some bothKeys) = ⟨[], true⟩ ∧
    -- ...the same restore with the first check dropped copies into it.
    restore false 1 backupOne (some bothKeys) = ⟨[Write.copy 5, Write.manifest (some 1)], false⟩ :=
  -- Both are evaluations Lean can run.
  ⟨by decide, by decide⟩

/-- **RED `ManifestFirst`.** The MANIFEST written first: the power cut that
keeps one write keeps the MANIFEST and not the table it names. -/
theorem manifest_first_loses_a_table :
    -- The one-write prefix holds the MANIFEST...
    Write.manifest (some 1) ∈ ([Write.manifest (some 1), Write.copy 5]).take 1 ∧
    -- ...and not the table.
    Write.copy 5 ∉ ([Write.manifest (some 1), Write.copy 5]).take 1 :=
  -- Both are evaluations Lean can run.
  ⟨by decide, by decide⟩

/-- **RED `MetaFirst`.** The metadata written first: the power cut that
keeps one write keeps the metadata and not the table it lists. -/
theorem metadata_first_loses_a_table :
    -- The one-write prefix holds the metadata...
    Put.metadata ∈ ([Put.metadata, Put.pool 5]).take 1 ∧
    -- ...and not the pool copy.
    Put.pool 5 ∉ ([Put.metadata, Put.pool 5]).take 1 :=
  -- Both are evaluations Lean can run.
  ⟨by decide, by decide⟩

/-- The defect `GcSkipsSealed`: a delete counts only the listings it can
read without a key, so it skips the sealed ones. Each remaining backup is
(whether it is sealed, its listing). -/
def collectSkipsSealed (removed : List Nat) (remaining : List (Bool × List Nat)) : List Nat :=
  -- Only plain listings count.
  collect removed ((remaining.filter fun b => !b.1).map Prod.snd)

/-- **RED `GcSkipsSealed`.** Backups 1 and 2 share pool file 5, backup 2
sealed. Deleting backup 1: the engine keeps file 5, the defect removes the
file sealed backup 2 still lists. -/
theorem gc_skips_sealed_removes_a_listed_file :
    -- The engine removes nothing...
    collect [5] [[5]] = [] ∧
    -- ...the defect removes file 5.
    collectSkipsSealed [5] [(true, [5])] = [5] :=
  -- Both are evaluations Lean can run.
  ⟨by decide, by decide⟩

/-- The key a backup's metadata is sealed under (`create_backup`): the
database's current key when it is encrypted, none otherwise. -/
def metaKey (encrypted : Bool) (current : Nat) : Option Nat :=
  -- Sealed under the current key exactly when the database is encrypted.
  if encrypted then some current else none

/-- **The metadata of an encrypted database's backup is sealed** and names
the current key (`SealedMetadata`). -/
theorem encrypted_backup_names_its_key (current : Nat) :
    metaKey true current = some current := by
  -- The encrypted branch.
  simp [metaKey]

/-- **RED `PlainMeta`.** The metadata written plain whatever the database:
the backup of an encrypted database names no key, so it is plain text. -/
theorem plain_meta_is_not_sealed :
    -- The engine seals it under key 1...
    metaKey true 1 = some 1 ∧
    -- ...the defect writes every backup the way an unencrypted one is.
    metaKey false 1 = none :=
  -- Both are evaluations Lean can run.
  ⟨by decide, by decide⟩

-- The end of the namespace.
end Regolith.BackupSeal
