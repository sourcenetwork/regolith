---- MODULE BackupSeal ----
\* Backups of a database encrypted at rest, and their restores (plan 4.12,
\* D57).
\*
\* THE STORY. regolith's BackupEngine (src/backup.rs) copies a database's
\* tables into a shared pool, one file per table named by its content, and
\* writes one small metadata file per backup saying which tables it holds,
\* where each goes and which keys each one spans. On an encrypted database
\* the tables are already sealed, but before D57 that metadata was plain
\* text: anyone with the backup disk could read the smallest and largest
\* key of every table, and a restore wrote a plain MANIFEST that said the
\* same. D57 seals the metadata through the database's own key provider.
\*
\* Picture one database, key 1 current, two tables. Backup 1 copies both
\* tables and writes its metadata sealed under key 1. The operator rotates
\* to key 2 and takes backup 2. Months later someone restores backup 1 with
\* a provider whose current key is 2. Things that can go wrong:
\*   - the metadata, or the restored MANIFEST, is written in plain text;
\*   - the restore opens backup 1 under the CURRENT key (2), not the key the
\*     file names (1), and refuses a provider that has every key it needs;
\*   - someone edits the plain listing (which names the shared files) so it
\*     points at another backup's copy of a table, or renames backup 2's
\*     file to backup 1's name, and the restore puts back the wrong tables;
\*   - the restore refuses (no key, a wrong key, a missing key) only after
\*     it has already copied tables into the target;
\*   - deleting a backup removes a shared table a sealed backup still needs,
\*     because the engine holds no key and skipped what it could not read;
\*   - a power cut leaves metadata that lists a table the pool never got,
\*     or a MANIFEST naming a table the target never got;
\*   - a restore runs over a target that is already a database.
\*
\* WHAT THE CODE DOES (each line below is one of these, by name).
\*   create_backup resolves the sealer for the current key first, copies
\*     every table it lists into the pool (each copy is written to a staging
\*     name, synced, renamed and its directory synced, so it lands whole or
\*     not at all), and only then writes the metadata the same way, sealed
\*     under that key and naming it.
\*   The metadata keeps the listing (each table's content id and size, which
\*     the pool's file names show anyway) in the clear, so listing and
\*     deleting need no key, and binds it with the tag: the tag's associated
\*     data is the backup id and every clear byte (src/backup/format.rs).
\*   restore refuses a target that holds a MANIFEST, then reads the metadata
\*     and checks, before it writes anything: a provider is given, it has the
\*     key the file names, the tag holds (right key bytes, listing unchanged,
\*     the file is the one this id wrote), and it has its current key and
\*     every key a table names. Then it copies every listed table into the
\*     target, and writes the MANIFEST last, sealed under the current key.
\*   delete_backup removes the metadata, then removes every pool file that
\*     backup listed and no other backup's listing names. It walks meta/ one
\*     entry at a time (Env::read_dir hands them out a batch at a time, the
\*     way readdir fills its buffer), reads each other listing as the walk
\*     reaches it, sealed or not, and strikes every candidate it names; it
\*     stops if one cannot be read or the walk breaks. Only once the walk
\*     has handed out its last entry does it remove what is left. So it holds
\*     the deleted listing and one other, never every listing at once.
\*
\* A STREAMED COLLECTION, IN ONE PICTURE. Backups 1 and 3 share table t;
\* backup 2 does not list it. Delete backup 1: the walk of meta/ hands out
\* backup 2's file, then backup 3's. Reading 2 strikes nothing, reading 3
\* strikes t, and t stays. Were the walk to lose backup 3's file where one
\* batch ends and the next begins, t would never be struck, and the delete
\* would remove a table backup 3 still lists.
\*
\* WHAT IS CHECKED.
\*   SealedMetadata        no backup's metadata, and no restored MANIFEST, is
\*                         plain text.
\*   RightKeysRestore      a restore never refuses a provider that has every
\*                         key the backup needs, after a rotation too.
\*   FaithfulRestore       a finished restore holds exactly the tables the
\*                         backup recorded when it was taken.
\*   RefusalWritesNothing  a refused restore wrote nothing.
\*   ListedRestores        every table an untampered backup lists is in the
\*                         pool, after any delete and any power cut.
\*   CollectionBounded     a delete's candidates are only ever files the
\*                         deleted backup listed: it holds one listing's
\*                         worth, however many backups there are.
\*
\* THE DEFECTS, one per Mutant value, and the promise each breaks.
\*   "PlainMeta"         the metadata is written plain.     SealedMetadata
\*   "PlainRestore"      the restored MANIFEST is plain.     SealedMetadata
\*   "OpenUnderCurrent"  the metadata is opened under the current key.
\*                                                          RightKeysRestore
\*   "ListingUnbound"    the tag does not cover the listing. FaithfulRestore
\*   "IdUnbound"         the tag does not cover the id.      FaithfulRestore
\*   "ManifestFirst"     the MANIFEST before the tables.     FaithfulRestore
\*   "OverDatabase"      a restore over a finished target.   FaithfulRestore
\*   "CheckAfterCopy"    key checks after the copies.   RefusalWritesNothing
\*   "GcSkipsSealed"     a delete counts only plain listings.  ListedRestores
\*   "MetaFirst"         metadata before the tables.          ListedRestores
\*   "StreamSkips"       the walk loses the first entry of each batch after
\*                       the first.                           ListedRestores
\*
\* WHAT THE MODEL LEAVES OUT, and why that loses nothing.
\*   - Bytes. A table is its content id <<t, k>>: table slot t sealed under
\*     key k. Two copies of one table under one key are one pool file, as
\*     content addressing makes them.
\*   - The checksum in front of the tag. It catches accidental damage with
\*     no key; a deliberate change keeps it valid, which is the case here.
\*   - Each copy's own crash steps. Every file is written to a staging name,
\*     synced and renamed, so a power cut leaves it whole or absent: one step
\*     here. A power cut is the Crash step, which drops what was in flight.
\*   - Unencrypted databases: their backups stay plain, as they always were,
\*     and none of these rules is about them.
\*
\* CONFIGURATIONS.
\*   MC_BackupSeal_Green                   every invariant holds
\*   MC_BackupSeal_Green_Stream            every invariant holds with three
\*                                         backups, so a delete's walk meets
\*                                         two files across a batch boundary
\*   MC_BackupSeal_Red_<defect>            the promise named above fails
\*
\* The Lean proof Regolith/BackupSeal.lean proves the streamed collection for
\* every number of backups and every batching: collect_stream_eq,
\* stream_keeps_listed and stream_holds_one_listing, with the StreamSkips
\* counterexample in stream_skip_removes_a_listed_file. It also proves the
\* listing a page of ids at a time names every backup once, in id order
\* (list_pages_all), which this model, whose ids are few, does not need.

\* Naturals for counting backups and restores, finite sets for how many
\* backups a walk meets, and sequences for the order it meets them in.
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  \* How many backups the model may take in one behaviour: bounds it.
  MaxBackups,
  \* How many restores the model may start in one behaviour: bounds it.
  MaxRestores,
  \* How many entries one batch of a walk of meta/ holds (the readdir
  \* buffer): the walk fetches the next batch when one is used up.
  Batch,
  \* "none" for the engine, or one defect named above.
  Mutant

\* At least one backup, or nothing happens.
ASSUME MaxBackups \in Nat \ {0}
\* Any number of restores; none for a run about deletes alone.
ASSUME MaxRestores \in Nat
\* A batch holds at least one entry.
ASSUME Batch \in Nat \ {0}
\* Only the engine and the defects above.
ASSUME Mutant \in {"none", "PlainMeta", "PlainRestore", "OpenUnderCurrent",
                   "ListingUnbound", "IdUnbound", "ManifestFirst", "OverDatabase",
                   "CheckAfterCopy", "GcSkipsSealed", "MetaFirst", "StreamSkips"}

\* The two key ids the database rotates between (KeyId).
Keys == {1, 2}
\* Two table slots: a table's place in the database (its file id).
Tables == {1, 2}
\* The backup ids, the numbers in meta/000001.backup and on: one per backup
\* the model may take.
Ids == 1..MaxBackups
\* A slot that holds no table.
NoObj == <<0, 0>>
\* Every table there can be: slot t sealed under key k.
Objs == Tables \X Keys
\* What a slot can hold: a table, or nothing.
Slot == Objs \cup {NoObj}
\* Every slot empty.
Empty == [t \in Tables |-> NoObj]
\* The key field of metadata written in plain text.
Plain == 0

\* A restore given no key provider (restore's `None`). Every stand-in value
\* in this module is a record shaped like the values beside it, because TLC
\* refuses to compare a string with a record.
NoProv == [given |-> FALSE, has |-> {}, right |-> FALSE, cur |-> 1]

\* The providers a restore may be given. `has` is the set of key ids it
\* hands out, `right` whether their bytes are the ones that sealed, `cur`
\* the key it names current (KeyProvider::current).
Providers ==
  \* No provider at all.
  {NoProv} \cup
  \* Both keys, the right bytes, key 1 current.
  { [given |-> TRUE, has |-> {1, 2}, right |-> TRUE, cur |-> 1],
    \* Both keys, the right bytes, key 2 current: after a rotation.
    [given |-> TRUE, has |-> {1, 2}, right |-> TRUE, cur |-> 2],
    \* Only key 2: key 1 was retired.
    [given |-> TRUE, has |-> {2}, right |-> TRUE, cur |-> 2],
    \* Only key 1.
    [given |-> TRUE, has |-> {1}, right |-> TRUE, cur |-> 1],
    \* Key 1 only, but it names key 2 current: a current key it lacks.
    [given |-> TRUE, has |-> {1}, right |-> TRUE, cur |-> 2],
    \* Both ids, but other bytes under them: the wrong keys.
    [given |-> TRUE, has |-> {1, 2}, right |-> FALSE, cur |-> 1] }

\* The values a slot map's tables take, without the empty marker.
Held(f) == {f[t] : t \in Tables} \ {NoObj}

\* The largest number in a non-empty set.
Max(S) == CHOOSE x \in S : \A y \in S : y <= x

\* A metadata file that does not exist (`on` says whether one does).
Absent == [on |-> FALSE, key |-> Plain, listing |-> Empty, sealed |-> Empty,
           body |-> Empty, bound |-> 1]

\* A target with no MANIFEST (`on` says whether it has one).
NoManifest == [on |-> FALSE, body |-> Empty, sealed |-> FALSE, want |-> Empty]

\* The backup in flight when there is none.
IdleBk == [phase |-> "idle", id |-> 1, objs |-> Empty, key |-> 1]

\* The delete in flight when there is none.
IdleGc == [phase |-> "idle", from |-> {}, cand |-> {}, order |-> <<>>, pos |-> 0]

\* Every order a walk can hand the ids in S out in: each sequence that holds
\* every id of S once. A directory lists its entries in an order of its own.
Orders(S) == {s \in [1..Cardinality(S) -> S] : \A i, j \in 1..Cardinality(S) : i # j => s[i] # s[j]}

\* The restore in flight when there is none.
IdleRs == [phase |-> "idle", id |-> 1, p |-> NoProv, m |-> Absent, want |-> Empty,
           ent |-> FALSE, wrote |-> FALSE]

VARIABLES
  \* The database's tables: live[t] is the key table slot t is sealed under,
  \* 0 when the slot holds no table (Version.levels; SsTableReader::seal_key).
  live,
  \* The key the database's provider names current (KeyProvider::current).
  current,
  \* The tables durable in the pool: backup_dir/shared/<content id>.sst.
  shared,
  \* meta[b]: backup b's metadata file, a record:
  \*   on       whether the file exists (Absent is the one that does not);
  \*   key      the key id it is sealed under and names, Plain when plain;
  \*   listing  each slot's content id as the clear listing says now;
  \*   sealed   the listing the tag was computed over when it was written;
  \*   body     the sealed part: which table each slot gets (file id, key
  \*            range, the key the table names);
  \*   bound    the backup id the tag binds (the file's name when written).
  meta,
  \* What backup b held when it was taken, by id: a ghost the checks read,
  \* nothing in the program stores it.
  recorded,
  \* The backup in flight (BackupEngine::create_backup): phase "idle" or
  \* "copy", the id it will write, the tables it lists, the key it seals
  \* under.
  bk,
  \* The restore target's table files: tgt[t] is what sits in its sst/ dir
  \* under slot t's file id.
  tgt,
  \* The restore target's MANIFEST: whether there is one (on), what it
  \* names (body), whether it is sealed, and the tables the backup recorded
  \* (want, a ghost).
  tman,
  \* The restore in flight (BackupEngine::restore): its phase ("idle",
  \* "check", "copy", "refused"), the backup id, the provider, the metadata
  \* it read, what that backup recorded (ghost), whether the provider was
  \* entitled to it (ghost), and whether it wrote into the target yet.
  rs,
  \* How many backups were started: bounds the model.
  made,
  \* How many restores were started: bounds the model.
  restores,
  \* How many times the attacker acted: at most once.
  adv,
  \* The delete in flight (BackupEngine::delete_backup, gc_shared), a record:
  \*   phase  "idle", "walk" while it reads the other listings, "remove"
  \*          once the walk is done;
  \*   from   the pool files the deleted backup listed (a ghost: the code
  \*          holds only what is left of them, below);
  \*   cand   the candidates still standing: the deleted backup's files that
  \*          no listing read so far names (the `unlisted` set);
  \*   order  the other backups' metadata files in the order the walk of
  \*          meta/ hands them out (Env::read_dir);
  \*   pos    how many entries the walk has handed out so far.
  gc

\* Every variable, so a step that changes none of them is a stutter.
vars == <<live, current, shared, meta, recorded, bk, tgt, tman, rs, made, restores, adv, gc>>

----------------------------------------------------------------------------
\* The start: an empty database under key 1, an empty pool, no backup.

Init ==
  \* No table yet.
  /\ live = [t \in Tables |-> 0]
  \* The provider names key 1 current.
  /\ current = 1
  \* Nothing in the pool.
  /\ shared = {}
  \* No metadata file.
  /\ meta = [b \in Ids |-> Absent]
  \* Nothing recorded.
  /\ recorded = [b \in Ids |-> Empty]
  \* No backup running.
  /\ bk = IdleBk
  \* The target holds no table...
  /\ tgt = Empty
  \* ...and no MANIFEST.
  /\ tman = NoManifest
  \* No restore running.
  /\ rs = IdleRs
  \* Nothing started yet.
  /\ made = 0
  \* Nothing restored yet.
  /\ restores = 0
  \* The attacker has not acted.
  /\ adv = 0
  \* No delete running.
  /\ gc = IdleGc

----------------------------------------------------------------------------
\* The database's own steps.

\* A flush writes table slot t, sealed under the current key.
WriteTable(t) ==
  \* Only an empty slot: the model keeps each slot to one table at a time.
  /\ live[t] = 0
  \* The new table names the key current right now.
  /\ live' = [live EXCEPT ![t] = current]
  \* Nothing else moves.
  /\ UNCHANGED <<current, shared, meta, recorded, bk, tgt, tman, rs, made, restores, adv, gc>>

\* A compaction rewrites table slot t under the current key (reseal_tables).
Reseal(t) ==
  \* Only a table under another key.
  /\ live[t] \notin {0, current}
  \* Now it names the current key: new bytes, a new content id.
  /\ live' = [live EXCEPT ![t] = current]
  \* Nothing else moves.
  /\ UNCHANGED <<current, shared, meta, recorded, bk, tgt, tman, rs, made, restores, adv, gc>>

\* The operator rotates the provider's current key.
Rotate ==
  \* 1 becomes 2 and 2 becomes 1.
  /\ current' = 3 - current
  \* Nothing written changes.
  /\ UNCHANGED <<live, shared, meta, recorded, bk, tgt, tman, rs, made, restores, adv, gc>>

----------------------------------------------------------------------------
\* Taking a backup (BackupEngine::create_backup).

\* The id the engine gives the next backup: one past the largest it finds
\* (next_backup_id).
NextId ==
  \* The ids whose metadata exists.
  LET present == {b \in Ids : meta[b].on}
  \* None: start at 1. Otherwise one past the largest.
  IN IF present = {} THEN 1 ELSE Max(present) + 1

\* A backup starts: it resolves the current key's sealer and captures the
\* tables the database holds right now.
StartBackup ==
  \* One backup at a time (create_backup takes &mut self).
  /\ bk.phase = "idle"
  \* And no restore or delete running on the same engine.
  /\ rs.phase = "idle"
  /\ gc.phase = "idle"
  \* Within the model's budget.
  /\ made < MaxBackups
  \* The id it would take is one the model has room for.
  /\ NextId \in Ids
  \* It will list every table the database holds, under the key each names,
  \* and seal under the current key.
  /\ bk' = [phase |-> "copy", id |-> NextId,
            objs |-> [t \in Tables |-> IF live[t] = 0 THEN NoObj ELSE <<t, live[t]>>],
            key |-> current]
  \* One more backup started.
  /\ made' = made + 1
  \* Nothing else moves.
  /\ UNCHANGED <<live, current, shared, meta, recorded, tgt, tman, rs, restores, adv, gc>>

\* One listed table lands in the pool, whole (ensure_shared_file).
CopyToPool(t) ==
  \* While copying.
  /\ bk.phase = "copy"
  \* A slot that holds a table...
  /\ bk.objs[t] # NoObj
  \* ...the pool does not have yet (a pool file it has is reused).
  /\ bk.objs[t] \notin shared
  \* Now the pool has it.
  /\ shared' = shared \cup {bk.objs[t]}
  \* Nothing else moves.
  /\ UNCHANGED <<live, current, meta, recorded, bk, tgt, tman, rs, made, restores, adv, gc>>

\* The metadata is written, whole, and the backup returns.
WriteMeta ==
  \* While copying.
  /\ bk.phase = "copy"
  \* Only once every table it lists is in the pool. MetaFirst skips this.
  /\ \/ Mutant = "MetaFirst"
     \/ \A t \in Tables : bk.objs[t] # NoObj => bk.objs[t] \in shared
  \* The file: sealed under the backup's key (plain under PlainMeta), the
  \* listing in the clear and the same listing under the tag, the body, and
  \* the id the tag binds.
  /\ meta' = [meta EXCEPT ![bk.id] =
                [on |-> TRUE, key |-> IF Mutant = "PlainMeta" THEN Plain ELSE bk.key,
                 listing |-> bk.objs, sealed |-> bk.objs, body |-> bk.objs,
                 bound |-> bk.id]]
  \* What this id now holds, for the checks.
  /\ recorded' = [recorded EXCEPT ![bk.id] = bk.objs]
  \* The backup is done.
  /\ bk' = IdleBk
  \* Nothing else moves.
  /\ UNCHANGED <<live, current, shared, tgt, tman, rs, made, restores, adv, gc>>

----------------------------------------------------------------------------
\* Deleting a backup (BackupEngine::delete_backup, gc_shared).

\* A delete starts: it reads backup b's listing, removes b's metadata file,
\* and opens a walk of meta/ (gc_shared). The candidates are the pool files
\* b listed, the only ones this collection may remove. The walk will hand
\* out the other backups' files in some order the directory picks: the
\* model tries every order.
StartDelete(b) ==
  \* It exists.
  /\ meta[b].on
  \* Nothing in flight on this engine (delete takes &mut self)...
  /\ bk.phase = "idle"
  \* ...no restore...
  /\ rs.phase = "idle"
  \* ...and no other collection.
  /\ gc.phase = "idle"
  \* The backups whose files the walk will meet: every other one that
  \* exists, in any order the directory hands them out.
  /\ \E order \in Orders({c \in Ids \ {b} : meta[c].on}) :
       \* Candidates are b's own pool files; nothing is struck yet, and
       \* the walk has handed out no entry.
       gc' = [phase |-> "walk", from |-> Held(meta[b].listing),
              cand |-> Held(meta[b].listing), order |-> order, pos |-> 0]
  \* The metadata file is gone before the walk starts.
  /\ meta' = [meta EXCEPT ![b] = Absent]
  \* Nothing else moves.
  /\ UNCHANGED <<live, current, shared, recorded, bk, tgt, tman, rs, made, restores, adv>>

\* The walk hands out its next entry and the collection reads that backup's
\* listing, striking every candidate the listing names: a file another
\* backup lists must stay. Each entry is read as the walk reaches it, so the
\* collection holds the candidates and one listing, never every listing.
\*
\* The walk comes in batches of Batch entries (readdir's buffer). After a
\* batch is used up the next one is fetched; StreamSkips fetches it one
\* entry too far, so the first entry of every later batch is never handed
\* out. GcSkipsSealed reads a sealed listing as if it named nothing.
WalkNext ==
  \* A walk is running and has entries left.
  /\ gc.phase = "walk"
  /\ gc.pos < Len(gc.order)
  \* At a batch boundary (a whole batch handed out), StreamSkips loses one.
  /\ LET skip == Mutant = "StreamSkips" /\ gc.pos > 0 /\ gc.pos % Batch = 0
         \* The position of the entry handed out now.
         i == IF skip THEN gc.pos + 2 ELSE gc.pos + 1
     IN IF i > Len(gc.order)
        \* The lost entry was the last one: the walk ends with nothing more.
        THEN gc' = [gc EXCEPT !.pos = i]
        \* Otherwise backup c's listing is read.
        ELSE LET c == gc.order[i]
                 \* Whether its listing counts: always, except a sealed one
                 \* under GcSkipsSealed.
                 counted == Mutant # "GcSkipsSealed" \/ meta[c].key = Plain
                 \* What it lists, as far as the collection is concerned.
                 names == IF counted THEN Held(meta[c].listing) ELSE {}
             \* The position moves on, and every candidate c names is struck.
             IN gc' = [gc EXCEPT !.pos = i, !.cand = @ \ names]
  \* Nothing else moves.
  /\ UNCHANGED <<live, current, shared, meta, recorded, bk, tgt, tman, rs, made, restores, adv>>

\* The walk has handed out its last entry (or lost it): the collection
\* stops reading and turns to removing.
WalkDone ==
  \* A walk with no entry left.
  /\ gc.phase = "walk"
  /\ gc.pos >= Len(gc.order)
  \* Removal comes next.
  /\ gc' = [gc EXCEPT !.phase = "remove"]
  \* Nothing else moves.
  /\ UNCHANGED <<live, current, shared, meta, recorded, bk, tgt, tman, rs, made, restores, adv>>

\* Every candidate still standing is removed from the pool, and the delete
\* returns. The code removes them one at a time, each followed by a sync of
\* shared/; one step loses nothing here, because no backup lists any of
\* them, so a power cut that keeps any subset of the removals is as safe as
\* keeping all of them.
Collect ==
  \* After the walk.
  /\ gc.phase = "remove"
  \* The pool loses exactly the unstruck candidates.
  /\ shared' = shared \ gc.cand
  \* The engine is free again.
  /\ gc' = IdleGc
  \* Nothing else moves.
  /\ UNCHANGED <<live, current, meta, recorded, bk, tgt, tman, rs, made, restores, adv>>

----------------------------------------------------------------------------
\* Restoring a backup (BackupEngine::restore).

\* Whether provider p has everything restoring backup b from file m needs:
\* the key the file names, the right bytes, its current key, every key a
\* table names, and a file that is the one id b wrote, unchanged.
Entitled(m, b, p) ==
  \* A provider, with the right bytes.
  /\ p.given
  /\ p.right
  \* The key the file names.
  /\ m.key \in p.has
  \* Its own current key, which the MANIFEST is sealed under.
  /\ p.cur \in p.has
  \* Every key a listed table names.
  /\ \A t \in Tables : m.body[t] # NoObj => m.body[t][2] \in p.has
  \* The listing is the one the tag covers, and the file is b's own.
  /\ m.listing = m.sealed
  /\ m.bound = b

\* Whether the engine opens file m as backup b under p (format::decode).
MetaOpens(m, b, p) ==
  \* Plain metadata needs no key.
  IF m.key = Plain THEN TRUE
  ELSE
    \* A sealed file needs a provider (Error::KeyProviderRequired)...
    /\ p.given
    \* ...with the key the file names (Error::UnknownKey). OpenUnderCurrent
    \* opens it under the provider's current key instead.
    /\ IF Mutant = "OpenUnderCurrent"
       THEN p.cur = m.key /\ p.cur \in p.has
       ELSE m.key \in p.has
    \* The tag holds only under the right bytes...
    /\ p.right
    \* ...over the listing as it was sealed (ListingUnbound skips this)...
    /\ Mutant = "ListingUnbound" \/ m.listing = m.sealed
    \* ...and the id it was sealed as (IdUnbound skips this).
    /\ Mutant = "IdUnbound" \/ m.bound = b

\* Whether p has its current key and every key a table names, the checks
\* restore makes before its first write.
KeysProvided(m, p) ==
  \* No provider: nothing is sealed, nothing to provide.
  \/ ~p.given
  \* Otherwise the current key and each table's key.
  \/ /\ p.cur \in p.has
     /\ \A t \in Tables : m.body[t] # NoObj => m.body[t][2] \in p.has

\* A restore of backup b with provider p starts: it reads b's metadata.
StartRestore(b, p) ==
  \* One restore at a time, and no backup or delete running on this engine.
  /\ rs.phase = "idle"
  /\ bk.phase = "idle"
  /\ gc.phase = "idle"
  \* Within the model's budget.
  /\ restores < MaxRestores
  \* The backup exists.
  /\ meta[b].on
  \* The target holds no MANIFEST: a target that does is refused before
  \* this, with nothing written. OverDatabase restores over it.
  /\ Mutant = "OverDatabase" \/ ~tman.on
  \* The restore holds the file as it read it, and the ghosts.
  /\ rs' = [phase |-> "check", id |-> b, p |-> p, m |-> meta[b],
            want |-> recorded[b], ent |-> Entitled(meta[b], b, p), wrote |-> FALSE]
  \* One more restore started.
  /\ restores' = restores + 1
  \* Nothing else moves.
  /\ UNCHANGED <<live, current, shared, meta, recorded, bk, tgt, tman, made, adv, gc>>

\* Every check, before any write.
Check ==
  \* Only right after the read.
  /\ rs.phase = "check"
  \* The file opens, and the keys are there. CheckAfterCopy leaves the key
  \* checks to the end.
  /\ LET pass == /\ MetaOpens(rs.m, rs.id, rs.p)
                 /\ Mutant = "CheckAfterCopy" \/ KeysProvided(rs.m, rs.p)
     \* Go on to copy, or refuse.
     IN rs' = [rs EXCEPT !.phase = IF pass THEN "copy" ELSE "refused"]
  \* Nothing written.
  /\ UNCHANGED <<live, current, shared, meta, recorded, bk, tgt, tman, made, restores, adv, gc>>

\* One table is copied from the pool into the target, whole: the pool file
\* the listing names, put at slot t's file id (copy_file_atomic).
CopyToTarget(t) ==
  \* While copying.
  /\ rs.phase = "copy"
  \* A slot the listing fills...
  /\ rs.m.listing[t] # NoObj
  \* ...whose pool file is there (verify_shared_file)...
  /\ rs.m.listing[t] \in shared
  \* ...and not copied yet.
  /\ tgt[t] # rs.m.listing[t]
  \* The target now holds it.
  /\ tgt' = [tgt EXCEPT ![t] = rs.m.listing[t]]
  \* This restore has written.
  /\ rs' = [rs EXCEPT !.wrote = TRUE]
  \* Nothing else moves.
  /\ UNCHANGED <<live, current, shared, meta, recorded, bk, tman, made, restores, adv, gc>>

\* The MANIFEST is written, whole, and the restore returns.
WriteManifest ==
  \* While copying.
  /\ rs.phase = "copy"
  \* Only once every listed table is in the target. ManifestFirst skips it.
  /\ \/ Mutant = "ManifestFirst"
     \/ \A t \in Tables : rs.m.listing[t] # NoObj => tgt[t] = rs.m.listing[t]
  \* CheckAfterCopy checks the keys only now, after the copies.
  /\ IF Mutant = "CheckAfterCopy" /\ ~KeysProvided(rs.m, rs.p)
     \* It refuses here, the tables already in the target.
     THEN /\ rs' = [rs EXCEPT !.phase = "refused"]
          /\ UNCHANGED tman
     \* The engine: the MANIFEST names the body's tables, sealed whenever a
     \* provider was given (plain under PlainRestore).
     ELSE /\ tman' = [on |-> TRUE, body |-> rs.m.body,
                      sealed |-> rs.p.given /\ Mutant # "PlainRestore",
                      want |-> rs.want]
          /\ rs' = IdleRs
  \* The target's tables do not move.
  /\ UNCHANGED <<live, current, shared, meta, recorded, bk, tgt, made, restores, adv, gc>>

\* A refused restore returns its error.
EndRefusal ==
  \* Only a refusal.
  /\ rs.phase = "refused"
  \* The engine is free again.
  /\ rs' = IdleRs
  \* Nothing else moves.
  /\ UNCHANGED <<live, current, shared, meta, recorded, bk, tgt, tman, made, restores, adv, gc>>

\* The operator removes the target, to restore into an empty one again.
ResetTarget ==
  \* No restore running.
  /\ rs.phase = "idle"
  \* Something to remove.
  /\ \/ tgt # Empty
     \/ tman.on
  \* No table...
  /\ tgt' = Empty
  \* ...and no MANIFEST.
  /\ tman' = NoManifest
  \* Nothing else moves.
  /\ UNCHANGED <<live, current, shared, meta, recorded, bk, rs, made, restores, adv, gc>>

----------------------------------------------------------------------------
\* Power cuts and the attacker.

\* The power goes. Every file is whole or absent (staging name, sync,
\* rename), so the disk keeps what it has; whatever was in flight stops.
Crash ==
  \* Something was in flight.
  /\ bk.phase # "idle" \/ rs.phase # "idle" \/ gc.phase # "idle"
  \* The backup stops: its pool files stay, unlisted until a later backup.
  /\ bk' = IdleBk
  \* The restore stops: its copies stay, with no MANIFEST after them.
  /\ rs' = IdleRs
  \* The collection stops: the deleted metadata stays deleted, and its
  \* candidates stay in the pool, listed by nobody.
  /\ gc' = IdleGc
  \* The disk keeps everything.
  /\ UNCHANGED <<live, current, shared, meta, recorded, tgt, tman, made, restores, adv>>

\* The attacker edits backup b's clear listing so slot t names pool file o,
\* fixing the checksum: another backup's copy of the table, or none.
TamperListing(b, t, o) ==
  \* Once.
  /\ adv = 0
  \* On a repository at rest: no engine shares a backup directory with
  \* another writer, so no edit lands in the middle of a delete.
  /\ gc.phase = "idle"
  \* The file exists.
  /\ meta[b].on
  \* Slot t's table under either key, or nothing, but not what is there.
  /\ o \in {<<t, k>> : k \in Keys} \cup {NoObj}
  /\ o # meta[b].listing[t]
  \* The listing changes; the tag and the body do not.
  /\ meta' = [meta EXCEPT ![b].listing[t] = o]
  \* The attacker is done.
  /\ adv' = 1
  \* Nothing else moves.
  /\ UNCHANGED <<live, current, shared, recorded, bk, tgt, tman, rs, made, restores, gc>>

\* The attacker swaps the two metadata files' names, each whole and valid.
Swap ==
  \* Once.
  /\ adv = 0
  \* On a repository at rest, as above.
  /\ gc.phase = "idle"
  \* Both exist.
  /\ meta[1].on
  /\ meta[2].on
  \* Each file now sits under the other's name.
  /\ meta' = [meta EXCEPT ![1] = meta[2], ![2] = meta[1]]
  \* The attacker is done.
  /\ adv' = 1
  \* Nothing else moves.
  /\ UNCHANGED <<live, current, shared, recorded, bk, tgt, tman, rs, made, restores, gc>>

\* Every step anything can take.
Next ==
  \* A flush or a compaction writes a table; a copy lands in the pool or in
  \* the target.
  \/ \E t \in Tables : WriteTable(t) \/ Reseal(t) \/ CopyToPool(t) \/ CopyToTarget(t)
  \* The operator rotates the current key.
  \/ Rotate
  \* A backup starts.
  \/ StartBackup
  \* A backup writes its metadata and returns.
  \/ WriteMeta
  \* A delete starts, its walk reads the other listings one entry at a
  \* time, the walk ends, and the unlisted candidates go.
  \/ \E b \in Ids : StartDelete(b)
  \/ WalkNext
  \/ WalkDone
  \/ Collect
  \* A restore of any backup starts, under any provider.
  \/ \E b \in Ids, p \in Providers : StartRestore(b, p)
  \* The restore runs its checks.
  \/ Check
  \* The restore writes its MANIFEST and returns.
  \/ WriteManifest
  \* A refused restore returns its error.
  \/ EndRefusal
  \* The operator removes the target.
  \/ ResetTarget
  \* The power goes.
  \/ Crash
  \* The attacker edits a listing...
  \/ \E b \in Ids, t \in Tables, o \in Slot : TamperListing(b, t, o)
  \* ...or swaps two files' names.
  \/ Swap

\* Start at Init, then take steps or stutter.
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Invariants.

\* A metadata file as the engine writes it.
MetaType == [on : BOOLEAN, key : Keys \cup {Plain}, listing : [Tables -> Slot],
             sealed : [Tables -> Slot], body : [Tables -> Slot], bound : Ids]

\* Every variable holds what its comment says.
TypeOK ==
  \* Each slot is empty or names a key.
  /\ live \in [Tables -> {0} \cup Keys]
  \* The current key is one of the two.
  /\ current \in Keys
  \* The pool holds tables.
  /\ shared \subseteq Objs
  \* Each id has a file or none.
  /\ meta \in [Ids -> MetaType]
  \* What each id held.
  /\ recorded \in [Ids -> [Tables -> Slot]]
  \* The backup in flight.
  /\ bk \in [phase : {"idle", "copy"}, id : Ids, objs : [Tables -> Slot], key : Keys]
  \* The target's tables.
  /\ tgt \in [Tables -> Slot]
  \* The target's MANIFEST.
  /\ tman \in [on : BOOLEAN, body : [Tables -> Slot], sealed : BOOLEAN,
               want : [Tables -> Slot]]
  \* The restore in flight.
  /\ rs \in [phase : {"idle", "check", "copy", "refused"}, id : Ids, p : Providers,
             m : MetaType, want : [Tables -> Slot], ent : BOOLEAN, wrote : BOOLEAN]
  \* The budgets.
  /\ made \in 0..MaxBackups
  /\ restores \in 0..MaxRestores
  /\ adv \in 0..1
  \* The delete in flight: its candidates, the walk's order and position.
  /\ gc.phase \in {"idle", "walk", "remove"}
  /\ gc.from \subseteq Objs
  /\ gc.cand \subseteq Objs
  /\ gc.order \in Seq(Ids)
  /\ gc.pos \in 0..MaxBackups + 1

\* No backup's metadata is plain, and no restored MANIFEST is. It rules out
\* the PlainMeta story (backup 1's file names every table's key range in
\* plain text) and the PlainRestore story (a restore with the right key
\* writes a MANIFEST that names them all in plain text). This is D57.
SealedMetadata ==
  \* Every metadata file names a key it is sealed under.
  /\ \A b \in Ids : meta[b].on => meta[b].key \in Keys
  \* Every restored MANIFEST is sealed.
  /\ tman.on => tman.sealed

\* A restore never refuses a provider that has every key the backup needs.
\* It rules out the OpenUnderCurrent story: backup 1 sealed under key 1, the
\* provider rotated to key 2 but still holding key 1, and the restore
\* refusing because it tried key 2.
RightKeysRestore == rs.phase = "refused" => ~rs.ent

\* A finished restore holds exactly what the backup held when it was taken:
\* its MANIFEST names those tables, and each sits in the target. It rules
\* out the ListingUnbound story (an edited listing puts another backup's
\* copy of a table under this backup's MANIFEST), the IdUnbound story
\* (backup 2's file under backup 1's name restores backup 2 as backup 1),
\* the ManifestFirst story (a power cut after the MANIFEST and before the
\* tables) and the OverDatabase story (a restore over a finished target
\* replaces tables its MANIFEST names).
FaithfulRestore ==
  \* When the target has a MANIFEST...
  tman.on =>
    \* ...it names exactly the tables the backup recorded...
    /\ tman.body = tman.want
    \* ...and each one it names is in the target.
    /\ \A t \in Tables : tman.body[t] # NoObj => tgt[t] = tman.body[t]

\* A refused restore wrote nothing. It rules out the CheckAfterCopy story:
\* a provider without its current key is refused only after every table was
\* copied into the target.
RefusalWritesNothing == rs.phase = "refused" => ~rs.wrote

\* A delete's candidates are always among the files the deleted backup
\* listed: striking only ever takes files away. It rules out a collection
\* that gathers what every other backup lists into one set, which grows with
\* the number of backups; the code keeps only what is left of one listing.
CollectionBounded == gc.cand \subseteq gc.from

\* Every table a backup lists is in the pool, unless the attacker edited
\* that listing. It rules out the GcSkipsSealed story (deleting backup 1
\* removes a table sealed backup 2 still lists) and the MetaFirst story (a
\* power cut after the metadata and before its tables).
ListedRestores ==
  \A b \in Ids :
    \* For a file whose listing is the one it was sealed with...
    (meta[b].on /\ meta[b].listing = meta[b].sealed) =>
      \* ...every table it lists is in the pool.
      \A t \in Tables : meta[b].listing[t] # NoObj => meta[b].listing[t] \in shared

====
