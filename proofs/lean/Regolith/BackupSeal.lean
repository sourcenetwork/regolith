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
7. The RED cases as counterexamples, one per defect of the model.
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

/-! ## The defects, as counterexamples -/

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
