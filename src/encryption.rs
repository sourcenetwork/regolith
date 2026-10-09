//! Encryption at rest: the keys a database seals its files under.
//!
//! With [`crate::Options::key_provider`] set, regolith seals every frame it
//! writes with AES-256-GCM-SIV (RFC 8452): each SSTable data, index and
//! filter block, each write-ahead log record, and each manifest edit batch.
//! The 16-byte tag takes the place of the frame's checksum, so a
//! random-access read still decrypts exactly one block, and a frame whose
//! tag fails is treated as corruption wherever a failed checksum is.
//!
//! Values are plaintext inside the engine: the memtable, the block cache,
//! merge operators, byte-equality checks, value-validated reads,
//! content-addressed keys, appends and allocations all see the bytes the
//! caller wrote, so every mechanism works unchanged on an encrypted store.
//!
//! # Keys and rotation
//!
//! A [`KeyProvider`] names the key new files are sealed under
//! ([`KeyProvider::current`]) and hands out key material by id
//! ([`KeyProvider::key`]). Every sealed file records the id of the key it
//! was sealed under (a table in its footer, a write-ahead log in its
//! stamp, a manifest in each edit batch), so rotating `current` takes
//! effect for each new table, each new log (the next memtable switch) and
//! each new manifest batch, while everything already written stays
//! readable for as long as the provider still provides the key it names.
//! A key id that some file names and the provider does not provide refuses
//! the open with [`crate::Error::UnknownKey`].
//!
//! # Turning encryption on, and re-encrypting
//!
//! A database written without encryption opens with a provider: its files
//! stay readable, and from then on every file regolith writes is sealed.
//! The first read-write open rewrites the manifest sealed, and recovery
//! rewrites the replayed write-ahead log into a sealed one. Tables are
//! re-sealed as compaction rewrites them, which is automatic but not
//! guaranteed to reach cold data. The one-time re-encryption is a manual
//! compaction: on an encrypted database, [`crate::Db::compact_range`] (any
//! range, any column family) also rewrites every table in the database not
//! sealed under the current key, the active write-ahead log, and the
//! manifest when it holds a batch under another key. After it returns, no
//! file names any other key and nothing is left in plaintext; the same call
//! completes a key rotation, after which the provider may drop the old key.
//!
//! An encrypted database opened without a provider refuses with
//! [`crate::Error::KeyProviderRequired`]; it never reads as empty.
//!
//! # Nonces
//!
//! Every frame draws a fresh 96-bit nonce from the operating system's
//! random source. GCM-SIV is nonce-misuse resistant: were two frames ever
//! to draw the same nonce under one key, that would reveal only whether
//! the two frames were identical, never the key stream. The chance of any
//! repeat among `n` frames under one key is at most `n^2 / 2^97`.
//!
//! # What this does not hide
//!
//! File sizes, the size and count of frames, and which key id sealed each
//! file are visible on disk. The format authenticates each frame and binds
//! it to its file and position, but a database opened with a provider still
//! reads files written before encryption was turned on, so an attacker who
//! can replace whole files with unsealed ones, or with older sealed ones, is
//! outside what this protects against. Backups made by
//! [`crate::BackupEngine`] copy sealed tables byte for byte, but record each
//! table's smallest and largest key in their own metadata in plaintext, and
//! a restored database's manifest stays plaintext until its first open with
//! a provider.

use std::fmt;

use zeroize::Zeroizing;

/// The name of one key a [`KeyProvider`] provides.
///
/// Sealed files record the id, never the key. An id must name the same key
/// material for as long as any file names it: a provider that hands out
/// different bytes under an id already in use makes every frame sealed
/// under the old bytes fail its tag, which reads as corruption.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct KeyId(pub u32);

impl fmt::Display for KeyId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// A 256-bit key, wiped from memory when it drops.
///
/// Regolith keeps the key schedule derived from it for as long as the
/// database is open, and wipes that too when the database drops. `Debug`
/// never prints the bytes.
#[derive(Clone)]
pub struct KeyMaterial(Zeroizing<[u8; 32]>);

impl KeyMaterial {
    /// Wrap 32 bytes of key material. The caller should wipe its own copy.
    pub fn new(bytes: [u8; 32]) -> Self {
        Self(Zeroizing::new(bytes))
    }

    pub(crate) fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

impl fmt::Debug for KeyMaterial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("KeyMaterial(..)")
    }
}

/// The source of the keys a database seals its files under. Install one
/// with [`crate::Options::key_provider`].
///
/// Both methods are synchronous and must answer from memory: they run on
/// any thread that creates or opens a file (the committing thread when a
/// write-ahead log rotates, flush and compaction threads, and the thread
/// that opens the database). They must not block, panic or re-enter the
/// database.
///
/// Regolith asks for each key id once and keeps what it derives from the
/// key until the database drops; [`KeyProvider::current`] is asked each
/// time a file is created and each time a manifest batch is written.
pub trait KeyProvider: Send + Sync + 'static {
    /// The key new files are sealed under. [`KeyProvider::key`] must
    /// provide it: a current key the provider cannot provide refuses the
    /// open, and fails any later write that needs a new file, with
    /// [`crate::Error::UnknownKey`].
    fn current(&self) -> KeyId;

    /// The key `id` names, or `None` when this provider does not have it.
    /// `None` for an id some file names refuses the open (or fails the
    /// read) with [`crate::Error::UnknownKey`]; it is never read as an
    /// empty or damaged file.
    fn key(&self, id: KeyId) -> Option<KeyMaterial>;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn key_material_never_prints_its_bytes() {
        let key = KeyMaterial::new([0xAB; 32]);
        let shown = format!("{key:?}");
        assert_eq!(shown, "KeyMaterial(..)");
        assert!(!shown.contains("171"), "{shown}");
        assert_eq!(key.as_bytes(), &[0xAB; 32]);
    }

    #[test]
    fn key_id_displays_as_its_number() {
        assert_eq!(KeyId(7).to_string(), "7");
    }
}
