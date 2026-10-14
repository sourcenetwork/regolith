---- MODULE EnvFiles ----
\* ===========================================================================
\* THE STORY
\* ===========================================================================
\* regolith reads and writes its files through an Env. Two Envs keep files
\* in memory (MemEnv, and the OPFS mirror in a browser tab), and the real
\* one reads files from the disk. Many threads read at once: get, scans,
\* compaction. The rule every Env must keep:
\*
\*     a read sees the bytes of every write that finished before it began,
\*     at the offset it asked for.
\*
\* PART 1, the disk: a shared cursor. An open file has one "cursor"
\* position. Reading with seek-then-read is two steps on that one cursor:
\* reader A seeks to 0, reader B seeks to 100, reader A reads... at 100. A
\* got B's bytes. A positional read (pread, StdReadFile in
\* src/env/std_env.rs) names its offset in the one call, so there is no
\* shared position to race on.
\*
\* PART 2, a file in memory (MemFile, src/env/mem_file.rs). The file is a
\* buffer with spare room and a published length L; readers read below L
\* with no lock. An append that fits writes ABOVE L, under a WRITER flag it
\* took with a compare-and-swap (CAS), and then publishes L+n with a second
\* CAS. Anything else (no room, an overwrite, two appends at once) builds a
\* NEW buffer from the old one's first L bytes plus its own, FREEZES the old
\* buffer with a CAS so no append can publish there any more, and swaps the
\* new buffer in with a CAS on the file's pointer.
\*
\* Tiny example of why the freeze matters. Writer A holds WRITER on buffer
\* E and is copying its record above L. Writer B gives up on E (it is busy)
\* and copies E's first L bytes into E2, plus its own record, and swaps E2
\* in. If B did not freeze E, A now publishes on E, an old buffer nobody
\* reads any more: A's append "finished", but no later read can see it.
\* With the freeze, A's publishing CAS fails, and A appends again on E2.
\*
\* What this model checks cannot happen:
\*   - a disk read returns bytes from another offset (ReadsOwnBytes);
\*   - a memory read misses a write that finished before it began
\*     (ReadSeesFinished), or the current buffer misses one
\*     (CurrentHoldsFinished);
\*   - a record lands twice (AtMostOnce).
\*
\* WHAT IS MODELLED, and the code each piece mirrors:
\*   cursor, pgot     the shared position of a seek-then-read file, and
\*                    what each disk reader got
\*   cur              MemFile::current, the buffer readers load
\*   buf, len         an Extent's bytes (published and pending) and its
\*                    published length (the LEN bits of Extent::state)
\*   wbit, frozen     the WRITER and FROZEN bits of Extent::state
\*   finished         the appends that returned
\*   wpc.. / rpc..    each writer's and reader's step and what it holds
\*
\* WHAT IS LEFT OUT, and why that loses nothing:
\*   - Byte counts: a record is one slot of a sequence; an append of n
\*     bytes is the same protocol with n slots.
\*   - Overwrites and shrinks: they always take the copy path, which is
\*     the path modelled here for appends too.
\*   - The spare capacity: when it runs out a writer takes the copy path;
\*     here a writer may take either path at any time, which covers it.
\*   - Memory ordering: the CAS steps are atomic here; the code's Acquire
\*     and Release make them so.
\*
\* CONFIGURATIONS (each GREEN must pass, each RED must break the one
\* invariant it names):
\*   MC_EnvFiles_Green               two disk readers, two appenders, one
\*                                   memory reader.
\*   MC_EnvFiles_Green_ThreeWriters  three appenders, so one publishes in
\*                                   place between another's build and a
\*                                   third's freeze.
\*   MC_EnvFiles_Red_SharedCursor    disk reads seek then read on one shared
\*                                   cursor: ReadsOwnBytes breaks.
\*   MC_EnvFiles_Red_NoFreeze        a copy swaps without freezing the old
\*                                   buffer: CurrentHoldsFinished breaks.
\*   MC_EnvFiles_Red_StaleFrozen     a copy skips its freeze because the
\*                                   buffer is frozen NOW, though it was not
\*                                   at its build: CurrentHoldsFinished
\*                                   breaks.
\*
\* Lean, proofs/lean/Regolith/EnvFiles.lean, proves the same rules for
\* every number of readers, writers and steps.

\* We use numbers, sequences and finite sets.
EXTENDS Naturals, Sequences, FiniteSets

\* The fixed inputs of a configuration.
CONSTANTS
  \* Threads reading a file on disk, each at its own offset.
  DiskReaders,
  \* [DiskReaders -> Nat]: the offset each disk reader reads.
  At,
  \* Threads appending to the in-memory file; writer w appends record w.
  Writers,
  \* Threads reading the whole in-memory file once.
  MemReaders,
  \* How many buffers may ever exist (a bound for TLC).
  MaxExt,
  \* "none" for the real code, or the name of one planted bug.
  Mutant

\* The bug names this model knows.
ASSUME Mutant \in {"none", "SharedCursor", "NoFreeze", "StaleFrozen"}
\* Every disk reader reads one offset.
ASSUME At \in [DiskReaders -> Nat]

\* For the configurations: disk reader 1 reads offset 0, reader 2 offset 1.
AtTwo == [r \in {1, 2} |-> r - 1]
\* For the configurations: no disk reader.
NoDisk == [r \in {} |-> 0]

\* The bytes of the file on disk at offset o: a table file never changes,
\* so each offset holds one known value.
Data(o) == 100 + o

\* The buffer numbers.
Exts == 1..MaxExt

\* The set of values in a sequence.
Range(s) == {s[i] : i \in DOMAIN s}

\* The state that changes from step to step.
VARIABLES
  \* Part 1: the shared cursor of a seek-then-read file.
  cursor,
  \* [DiskReaders -> {"start","sought","done"}]: each disk reader's step.
  ppc,
  \* [DiskReaders -> Nat]: what each disk reader got (0: nothing yet).
  pgot,
  \* Part 2: the buffer readers load now.
  cur,
  \* [Exts -> Seq(Writers)]: each buffer's records, published or pending.
  buf,
  \* [Exts -> Nat]: each buffer's published length.
  len,
  \* [Exts -> BOOLEAN]: each buffer's WRITER bit.
  wbit,
  \* [Exts -> BOOLEAN]: each buffer's FROZEN bit.
  frozen,
  \* The next buffer number.
  nextExt,
  \* The appends that returned.
  finished,
  \* [Writers -> step name]: each writer's step.
  wpc,
  \* [Writers -> Exts]: the buffer a writer works on.
  wext,
  \* [Writers -> Nat]: the length a writer saw.
  wlen,
  \* [Writers -> [bit, frz]]: the WRITER and FROZEN bits a copier saw when
  \* it built (the state word its freeze CAS expects).
  wsaw,
  \* [Writers -> Seq(Writers)]: the new buffer a copier built.
  wnew,
  \* [MemReaders -> {"start","begun","loaded","lenread","done"}].
  rpc,
  \* [MemReaders -> SUBSET Writers]: appends finished when the read began.
  rfin,
  \* [MemReaders -> Exts]: the buffer a reader loaded.
  rext,
  \* [MemReaders -> Nat]: the length it loaded.
  rlen,
  \* [MemReaders -> Seq(Writers)]: what it read.
  rgot

\* All the variables, for "nothing else changes".
\* The disk part's variables.
diskVars == <<cursor, ppc, pgot>>
\* The in-memory part's variables.
memVars == <<cur, buf, len, wbit, frozen, nextExt, finished, wpc, wext, wlen,
             wsaw, wnew, rpc, rfin, rext, rlen, rgot>>
\* Both together.
vars == <<diskVars, memVars>>

\* Every variable holds the kind of value it should.
TypeOK ==
  \* The cursor is an offset.
  /\ cursor \in Nat
  \* Each disk reader is at one step.
  /\ ppc \in [DiskReaders -> {"start", "sought", "done"}]
  \* The current buffer is a buffer number.
  /\ cur \in Exts
  \* Lengths are numbers and bits are booleans.
  /\ len \in [Exts -> Nat]
  /\ wbit \in [Exts -> BOOLEAN]
  /\ frozen \in [Exts -> BOOLEAN]
  \* Finished appends are writers' records.
  /\ finished \subseteq Writers
  \* Each writer and memory reader is at one step.
  /\ wpc \in [Writers -> {"start", "claimed", "written", "built", "frozen", "done"}]
  /\ rpc \in [MemReaders -> {"start", "begun", "loaded", "lenread", "done"}]

\* The start: an empty file in buffer 1, nobody has done anything.
Init ==
  \* The cursor is at 0.
  /\ cursor = 0
  \* Disk readers have not read.
  /\ ppc = [r \in DiskReaders |-> "start"]
  /\ pgot = [r \in DiskReaders |-> 0]
  \* Readers load buffer 1.
  /\ cur = 1
  \* Every buffer is empty.
  /\ buf = [e \in Exts |-> <<>>]
  /\ len = [e \in Exts |-> 0]
  \* No WRITER bit, nothing frozen.
  /\ wbit = [e \in Exts |-> FALSE]
  /\ frozen = [e \in Exts |-> FALSE]
  \* The next new buffer is number 2.
  /\ nextExt = 2
  \* No append has returned.
  /\ finished = {}
  \* Every writer is about to append.
  /\ wpc = [w \in Writers |-> "start"]
  /\ wext = [w \in Writers |-> 1]
  /\ wlen = [w \in Writers |-> 0]
  /\ wsaw = [w \in Writers |-> [bit |-> FALSE, frz |-> FALSE]]
  /\ wnew = [w \in Writers |-> <<>>]
  \* Every memory reader is about to read.
  /\ rpc = [r \in MemReaders |-> "start"]
  /\ rfin = [r \in MemReaders |-> {}]
  /\ rext = [r \in MemReaders |-> 1]
  /\ rlen = [r \in MemReaders |-> 0]
  /\ rgot = [r \in MemReaders |-> <<>>]

\* ---------------------------------------------------------------------------
\* Part 1: disk reads.
\* ---------------------------------------------------------------------------

\* A positional read: one call names the offset and returns its bytes
\* (pread). The bug SharedCursor never takes this step.
PRead(r) ==
  \* The real code.
  /\ Mutant # "SharedCursor"
  \* The reader has not read.
  /\ ppc[r] = "start"
  \* It gets the bytes at its own offset, in one step.
  /\ pgot' = [pgot EXCEPT ![r] = Data(At[r])]
  /\ ppc' = [ppc EXCEPT ![r] = "done"]
  \* Nothing else changes.
  /\ UNCHANGED <<cursor, memVars>>

\* Bug SharedCursor, step 1: move the file's one cursor to my offset.
Seek(r) ==
  \* Only with the bug.
  /\ Mutant = "SharedCursor"
  \* The reader has not read.
  /\ ppc[r] = "start"
  \* The shared cursor goes to its offset.
  /\ cursor' = At[r]
  /\ ppc' = [ppc EXCEPT ![r] = "sought"]
  \* Nothing else changes.
  /\ UNCHANGED <<pgot, memVars>>

\* Bug SharedCursor, step 2: read at the cursor, wherever it is now.
ReadAtCursor(r) ==
  \* The reader sought.
  /\ ppc[r] = "sought"
  \* It gets the bytes at the cursor, which another reader may have moved.
  /\ pgot' = [pgot EXCEPT ![r] = Data(cursor)]
  /\ ppc' = [ppc EXCEPT ![r] = "done"]
  \* Nothing else changes.
  /\ UNCHANGED <<cursor, memVars>>

\* ---------------------------------------------------------------------------
\* Part 2: the in-memory file.
\* ---------------------------------------------------------------------------

\* An append in place, step 1: take WRITER on the current buffer with a CAS
\* that needs no WRITER and no FROZEN (MemFile::in_place).
InPlaceClaim(w) ==
  \* The writer is about to append.
  /\ wpc[w] = "start"
  \* The current buffer is free to append to.
  /\ ~wbit[cur]
  /\ ~frozen[cur]
  \* The CAS sets WRITER.
  /\ wbit' = [wbit EXCEPT ![cur] = TRUE]
  \* The writer remembers the buffer and its length.
  /\ wext' = [wext EXCEPT ![w] = cur]
  /\ wlen' = [wlen EXCEPT ![w] = len[cur]]
  /\ wpc' = [wpc EXCEPT ![w] = "claimed"]
  \* Nothing else changes.
  /\ UNCHANGED <<diskVars, cur, buf, len, frozen, nextExt, finished, wsaw, wnew,
                 rpc, rfin, rext, rlen, rgot>>

\* An append in place, step 2: write the record just above the published
\* length. No reader reads there.
InPlaceWrite(w) ==
  \* The writer holds WRITER.
  /\ wpc[w] = "claimed"
  \* Its record goes right after the published records.
  /\ buf' = [buf EXCEPT ![wext[w]] = SubSeq(buf[wext[w]], 1, wlen[w]) \o <<w>>]
  /\ wpc' = [wpc EXCEPT ![w] = "written"]
  \* Nothing else changes.
  /\ UNCHANGED <<diskVars, cur, len, wbit, frozen, nextExt, finished, wext, wlen,
                 wsaw, wnew, rpc, rfin, rext, rlen, rgot>>

\* An append in place, step 3: publish the new length with a CAS that
\* clears WRITER. It fails if a copier froze the buffer meanwhile; then the
\* writer appends again from the start.
InPlacePublish(w) ==
  \* The writer wrote its record.
  /\ wpc[w] = "written"
  /\ LET e == wext[w] IN
       \* Not frozen: the CAS publishes, and the append has finished.
       IF ~frozen[e]
       THEN /\ len' = [len EXCEPT ![e] = wlen[w] + 1]
            /\ wbit' = [wbit EXCEPT ![e] = FALSE]
            /\ finished' = finished \cup {w}
            /\ wpc' = [wpc EXCEPT ![w] = "done"]
       \* Frozen: the CAS fails; the buffer is dead and the writer retries.
       ELSE /\ wpc' = [wpc EXCEPT ![w] = "start"]
            /\ UNCHANGED <<len, wbit, finished>>
  \* Nothing else changes.
  /\ UNCHANGED <<diskVars, cur, buf, frozen, nextExt, wext, wlen, wsaw, wnew,
                 rpc, rfin, rext, rlen, rgot>>

\* A copy, step 1: build a new buffer from the current one's published
\* records plus this writer's record (MemFile::copy).
CopyBuild(w) ==
  \* The writer is about to append, and a buffer number is left.
  /\ wpc[w] = "start"
  /\ nextExt <= MaxExt
  \* The new buffer: the published records, then this one.
  /\ wnew' = [wnew EXCEPT ![w] = SubSeq(buf[cur], 1, len[cur]) \o <<w>>]
  \* The writer remembers the buffer and the state word it saw.
  /\ wext' = [wext EXCEPT ![w] = cur]
  /\ wlen' = [wlen EXCEPT ![w] = len[cur]]
  /\ wsaw' = [wsaw EXCEPT ![w] = [bit |-> wbit[cur], frz |-> frozen[cur]]]
  /\ wpc' = [wpc EXCEPT ![w] = "built"]
  \* Nothing else changes.
  /\ UNCHANGED <<diskVars, cur, buf, len, wbit, frozen, nextExt, finished,
                 rpc, rfin, rext, rlen, rgot>>

\* A copy, step 2: freeze the old buffer with a CAS on the word it saw when
\* it built, so no append publishes there any more. If that word was already
\* frozen, the length it copied is final and there is nothing to do. The
\* choice is made from the word seen at build time, as the code makes it
\* (MemFile::copy tests the `state` it loaded first): a buffer someone else
\* froze AFTER the build may have published more records before that freeze.
\* The bug NoFreeze skips the freeze.
CopyFreeze(w) ==
  \* The writer built its new buffer.
  /\ wpc[w] = "built"
  /\ LET e == wext[w] IN
       \* The bug NoFreeze, or a buffer frozen when it built: go straight to
       \* the swap. The bug StaleFrozen also goes straight on when the buffer
       \* is frozen NOW, though its length may have grown since the build.
       IF \/ Mutant = "NoFreeze"
          \/ wsaw[w].frz
          \/ Mutant = "StaleFrozen" /\ frozen[e]
       THEN /\ wpc' = [wpc EXCEPT ![w] = "frozen"]
            /\ UNCHANGED frozen
       \* The word is still what it saw: the CAS sets FROZEN.
       ELSE IF len[e] = wlen[w] /\ wbit[e] = wsaw[w].bit /\ ~frozen[e]
            THEN /\ frozen' = [frozen EXCEPT ![e] = TRUE]
                 /\ wpc' = [wpc EXCEPT ![w] = "frozen"]
            \* The word changed (an append published, or another copy froze
            \* it): start over.
            ELSE /\ wpc' = [wpc EXCEPT ![w] = "start"]
                 /\ UNCHANGED frozen
  \* Nothing else changes.
  /\ UNCHANGED <<diskVars, cur, buf, len, wbit, nextExt, finished, wext, wlen,
                 wsaw, wnew, rpc, rfin, rext, rlen, rgot>>

\* A copy, step 3: swap the new buffer in with a CAS on the file's pointer.
\* It fails if another copy swapped first; then the writer starts over.
CopySwap(w) ==
  \* The old buffer is frozen (or the bug skipped it).
  /\ wpc[w] = "frozen"
  \* The pointer still names the old buffer: the CAS wins ...
  /\ IF cur = wext[w]
     THEN /\ cur' = nextExt
          \* ... and the new buffer holds what the writer built, all published.
          /\ buf' = [buf EXCEPT ![nextExt] = wnew[w]]
          /\ len' = [len EXCEPT ![nextExt] = Len(wnew[w])]
          /\ nextExt' = nextExt + 1
          /\ finished' = finished \cup {w}
          /\ wpc' = [wpc EXCEPT ![w] = "done"]
     \* ... otherwise another copy won: start over.
     ELSE /\ wpc' = [wpc EXCEPT ![w] = "start"]
          /\ UNCHANGED <<cur, buf, len, nextExt, finished>>
  \* Nothing else changes.
  /\ UNCHANGED <<diskVars, wbit, frozen, wext, wlen, wsaw, wnew, rpc, rfin, rext, rlen, rgot>>

\* A memory read, step 1: it begins; note the appends finished by now.
ReadBegin(r) ==
  \* The reader has not begun.
  /\ rpc[r] = "start"
  \* Every append that returned before this moment must be seen.
  /\ rfin' = [rfin EXCEPT ![r] = finished]
  /\ rpc' = [rpc EXCEPT ![r] = "begun"]
  \* Nothing else changes.
  /\ UNCHANGED <<diskVars, cur, buf, len, wbit, frozen, nextExt, finished, wpc, wext,
                 wlen, wsaw, wnew, rext, rlen, rgot>>

\* A memory read, step 2: load the file's current buffer.
ReadLoad(r) ==
  \* The reader began.
  /\ rpc[r] = "begun"
  \* It holds the buffer the pointer names now.
  /\ rext' = [rext EXCEPT ![r] = cur]
  /\ rpc' = [rpc EXCEPT ![r] = "loaded"]
  \* Nothing else changes.
  /\ UNCHANGED <<diskVars, cur, buf, len, wbit, frozen, nextExt, finished, wpc, wext,
                 wlen, wsaw, wnew, rfin, rlen, rgot>>

\* A memory read, step 3: load that buffer's published length.
ReadLen(r) ==
  \* The reader holds a buffer.
  /\ rpc[r] = "loaded"
  \* It reads the length published on it now.
  /\ rlen' = [rlen EXCEPT ![r] = len[rext[r]]]
  /\ rpc' = [rpc EXCEPT ![r] = "lenread"]
  \* Nothing else changes.
  /\ UNCHANGED <<diskVars, cur, buf, len, wbit, frozen, nextExt, finished, wpc, wext,
                 wlen, wsaw, wnew, rfin, rext, rgot>>

\* A memory read, step 4: copy the records below that length.
ReadCopy(r) ==
  \* The reader has its length.
  /\ rpc[r] = "lenread"
  \* It copies the published records of its buffer.
  /\ rgot' = [rgot EXCEPT ![r] = SubSeq(buf[rext[r]], 1, rlen[r])]
  /\ rpc' = [rpc EXCEPT ![r] = "done"]
  \* Nothing else changes.
  /\ UNCHANGED <<diskVars, cur, buf, len, wbit, frozen, nextExt, finished, wpc, wext,
                 wlen, wsaw, wnew, rfin, rext, rlen>>

\* Every step anyone can take.
Next ==
  \/ \E r \in DiskReaders : PRead(r) \/ Seek(r) \/ ReadAtCursor(r)
  \/ \E w \in Writers :
       \/ InPlaceClaim(w) \/ InPlaceWrite(w) \/ InPlacePublish(w)
       \/ CopyBuild(w) \/ CopyFreeze(w) \/ CopySwap(w)
  \/ \E r \in MemReaders : ReadBegin(r) \/ ReadLoad(r) \/ ReadLen(r) \/ ReadCopy(r)

\* The behaviours: start in Init, take Next steps.
Spec == Init /\ [][Next]_vars

\* ===========================================================================
\* THE RULES
\* ===========================================================================

\* A disk read returns the bytes at its own offset. Rules out: A seeks to 0,
\* B seeks to 1, A reads at the shared cursor and gets offset 1's bytes.
ReadsOwnBytes ==
  \* Every disk reader that read got the bytes of its own offset.
  \A r \in DiskReaders : ppc[r] = "done" => pgot[r] = Data(At[r])

\* The current buffer's published records hold every finished append.
\* Rules out: an append publishing on a buffer a copy already replaced, so
\* it "finished" where nobody will ever read.
CurrentHoldsFinished ==
  \* Every finished append is among the current buffer's published records.
  finished \subseteq Range(SubSeq(buf[cur], 1, len[cur]))

\* A memory read sees every append that finished before it began. Rules
\* out: a reader that began after an append returned and missed it.
ReadSeesFinished ==
  \* Every memory reader that is done got every append finished at its start.
  \A r \in MemReaders : rpc[r] = "done" => rfin[r] \subseteq Range(rgot[r])

\* No record is published twice in the current buffer. Rules out: an
\* append retried after a lost race that also landed the first time.
AtMostOnce ==
  \* The current buffer's published records ...
  LET s == SubSeq(buf[cur], 1, len[cur]) IN
    \* ... hold no record at two positions.
    \A i, j \in 1..Len(s) : s[i] = s[j] => i = j

====
