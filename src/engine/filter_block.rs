//! The filter region of an SSTable: the user-key bloom filter plus the
//! optional prefix bloom filter, decoded as one unit.
//!
//! On-disk format, written by `SsTableWriter::finish`:
//!
//! ```text
//! [prefix_bloom_len: 7 bytes LE][prefix form: u8][prefix bloom bytes][user-key bloom bytes]
//! ```
//!
//! A `prefix_bloom_len` of `0` means the file was written without a
//! prefix extractor, and the whole header is then zero. The header is
//! written unconditionally, so the region decodes the same way either way.
//!
//! The prefix form says which key the prefix bloom's entries were built
//! from (`prefix_call::PrefixForm`). Its byte was the top byte of an
//! eight-byte length before the caller-key form existed, and no table has a
//! prefix bloom of 2^56 bytes, so every table written then reads as form
//! `0`, the engine-key form it holds. A form this build does not know is a
//! later one: its prefix bloom is left unused, which rules nothing out. A
//! build from before the forms reads a caller-key table's header as a
//! length past the region and refuses the table, where asking its bloom the
//! old way would have ruled out keys it holds.
//!
//! The two filters travel together because the footer describes them as
//! one region: one region, one decode, one cache entry, one charge.

use std::io;

use super::bloom::{BloomFilter, decode_bloom_block};
use super::prefix_call::{PrefixForm, PrefixProbe};

/// Header bytes in front of the prefix bloom.
const PREFIX_LEN_HEADER: usize = 8;

/// Where the header's top byte, the prefix bloom's form, starts.
const PREFIX_FORM_SHIFT: u32 = 56;

/// The header's low seven bytes: the prefix bloom's length.
const PREFIX_LEN_MASK: u64 = (1 << PREFIX_FORM_SHIFT) - 1;

/// Smallest legal encoded bloom block (`decode_bloom_block` reads a
/// 4-byte `num_hashes` header).
const MIN_BLOOM_BLOCK: usize = 4;

/// The header of a bloom region whose prefix bloom is `prefix_bloom_len`
/// bytes of `form`. A region with no prefix bloom has an all-zero header,
/// whatever the form.
pub(crate) fn prefix_header(
    form: PrefixForm,
    prefix_bloom_len: usize,
) -> io::Result<[u8; PREFIX_LEN_HEADER]> {
    let len = u64::try_from(prefix_bloom_len)
        .ok()
        .filter(|len| *len <= PREFIX_LEN_MASK)
        .ok_or_else(|| invalid_data("prefix bloom is too large to record"))?;
    let form = if len == 0 { 0 } else { u64::from(form.tag()) };
    Ok(((form << PREFIX_FORM_SHIFT) | len).to_le_bytes())
}

/// Both bloom filters of one SSTable.
pub(crate) struct FilterBlock {
    user: BloomFilter,
    /// `None` also for a prefix bloom of a form this build does not know.
    prefix: Option<(PrefixForm, BloomFilter)>,
    charge: usize,
}

impl FilterBlock {
    /// Decode the filter region read from an SSTable's bloom range.
    ///
    /// Rejects a region too short to hold the length header, a prefix
    /// length that runs past the region, and either bloom block being
    /// too short to carry its own header.
    pub(crate) fn decode(region: &[u8]) -> io::Result<Self> {
        let Some(header) = region.first_chunk::<PREFIX_LEN_HEADER>() else {
            return Err(invalid_data(
                "bloom region too short for prefix-bloom length header",
            ));
        };
        let header = u64::from_le_bytes(*header);
        let form = PrefixForm::from_tag((header >> PREFIX_FORM_SHIFT) as u8);
        let prefix_len = usize::try_from(header & PREFIX_LEN_MASK)
            .map_err(|_| invalid_data("prefix bloom length is too large to address"))?;
        let user_offset = PREFIX_LEN_HEADER
            .checked_add(prefix_len)
            .ok_or_else(|| invalid_data("prefix bloom length overflows"))?;
        if user_offset > region.len() {
            return Err(invalid_data("prefix bloom length exceeds bloom region"));
        }
        if prefix_len > 0 && prefix_len < MIN_BLOOM_BLOCK {
            return Err(invalid_data("prefix bloom block too short"));
        }
        if region.len() - user_offset < MIN_BLOOM_BLOCK {
            return Err(invalid_data("user bloom block too short"));
        }

        let prefix = form.filter(|_| prefix_len > 0).map(|form| {
            let bloom = decode_bloom_block(&region[PREFIX_LEN_HEADER..user_offset]);
            (form, bloom)
        });
        let user = decode_bloom_block(&region[user_offset..]);

        Ok(Self {
            user,
            prefix,
            // The decoded filters hold the region's bit arrays minus the
            // two 4-byte `num_hashes` headers and the 8-byte length
            // header, so the region length is the charge to within a
            // handful of bytes and never under-reports.
            charge: std::mem::size_of::<Self>() + region.len(),
        })
    }

    /// Whether this SSTable *might* contain `user_key`. `false` means
    /// definitely not.
    pub(crate) fn may_contain(&self, user_key: &[u8]) -> bool {
        self.user.may_contain(user_key)
    }

    /// Whether this SSTable *might* contain a key of the seek `probe` is
    /// for, asked in the form its prefix bloom was built in. Conservatively
    /// `true` when the file carries no prefix bloom this build can ask, or
    /// the seek has no key for that form, since there is then no negative
    /// information to act on.
    pub(crate) fn may_have_prefix(&self, probe: &mut PrefixProbe<'_>) -> bool {
        match &self.prefix {
            Some((form, filter)) => probe
                .key_for(*form)
                .is_none_or(|key| filter.may_contain(key)),
            None => true,
        }
    }

    /// The form of this table's prefix bloom, when it has one this build
    /// can ask.
    #[cfg(test)]
    pub(crate) fn prefix_form(&self) -> Option<PrefixForm> {
        self.prefix.as_ref().map(|(form, _)| *form)
    }

    /// Heap bytes held, for block-cache charging.
    pub(crate) fn charge(&self) -> usize {
        self.charge
    }
}

impl std::fmt::Debug for FilterBlock {
    /// Shape only: a bloom filter's bits are not readable and printing
    /// them would leak nothing useful and a great deal of noise.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FilterBlock")
            .field("has_prefix_bloom", &self.prefix.is_some())
            .field("charge", &self.charge)
            .finish()
    }
}

fn invalid_data(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::column_family::prefix_key;
    use crate::engine::bloom::{BloomFilterBuilder, encode_bloom_block};
    use crate::options::FixedLengthPrefix;

    /// A bloom region whose prefix bloom holds `prefix_keys`, behind the
    /// header `header` makes for its length.
    fn region_with(
        header: impl Fn(usize) -> [u8; PREFIX_LEN_HEADER],
        prefix_keys: Option<&[&[u8]]>,
        user_keys: &[&[u8]],
    ) -> Vec<u8> {
        let prefix_bytes = match prefix_keys {
            Some(keys) => {
                let mut builder = BloomFilterBuilder::new(10);
                for key in keys {
                    builder.add_key(key);
                }
                encode_bloom_block(&builder.build())
            }
            None => Vec::new(),
        };
        let mut builder = BloomFilterBuilder::new(10);
        for key in user_keys {
            builder.add_key(key);
        }
        let user_bytes = encode_bloom_block(&builder.build());

        let mut out = Vec::new();
        out.extend_from_slice(&header(prefix_bytes.len()));
        out.extend_from_slice(&prefix_bytes);
        out.extend_from_slice(&user_bytes);
        out
    }

    /// A region as this build writes it.
    fn region(form: PrefixForm, prefix_keys: Option<&[&[u8]]>, user_keys: &[&[u8]]) -> Vec<u8> {
        region_with(
            |len| prefix_header(form, len).unwrap(),
            prefix_keys,
            user_keys,
        )
    }

    /// A region as a build from before the forms wrote it: the header is
    /// the length, eight bytes of it.
    fn region_before_forms(prefix_keys: Option<&[&[u8]]>, user_keys: &[&[u8]]) -> Vec<u8> {
        region_with(|len| (len as u64).to_le_bytes(), prefix_keys, user_keys)
    }

    /// Whether `filter` lets a seek for the caller's `prefix` in family 1
    /// through, with a three-byte extractor.
    fn lets_through(filter: &FilterBlock, prefix: &[u8]) -> bool {
        let prefixed = prefix_key(1, prefix);
        filter.may_have_prefix(&mut PrefixProbe::new(&FixedLengthPrefix(3), &prefixed))
    }

    #[test]
    fn decodes_region_without_prefix_bloom() {
        for form in [PrefixForm::EngineKey, PrefixForm::CallerKey] {
            let bytes = region(form, None, &[b"alpha", b"beta"]);
            assert_eq!(bytes[..PREFIX_LEN_HEADER], [0; PREFIX_LEN_HEADER]);
            assert_eq!(bytes, region_before_forms(None, &[b"alpha", b"beta"]));
            let filter = FilterBlock::decode(&bytes).unwrap();
            assert!(filter.may_contain(b"alpha"));
            assert!(filter.may_contain(b"beta"));
            assert_eq!(filter.prefix_form(), None);
            assert!(
                lets_through(&filter, b"anything"),
                "no prefix bloom means no negative information"
            );
        }
    }

    #[test]
    fn a_caller_key_prefix_bloom_is_asked_with_the_family_id_and_the_callers_prefix() {
        let entry = prefix_key(1, b"pre");
        let bytes = region(PrefixForm::CallerKey, Some(&[&entry]), &[b"prefix-key"]);
        assert_eq!(bytes[PREFIX_LEN_HEADER - 1], PrefixForm::CallerKey.tag());
        let filter = FilterBlock::decode(&bytes).unwrap();
        assert!(filter.may_contain(b"prefix-key"));
        assert_eq!(filter.prefix_form(), Some(PrefixForm::CallerKey));
        assert!(lets_through(&filter, b"pre"));
        assert!(lets_through(&filter, b"prefix"));
        assert!(!lets_through(&filter, b"zzz"));
        assert!(
            lets_through(&filter, b"pr"),
            "the extractor gives no key for it, so nothing is ruled out"
        );
    }

    /// A table written before the forms holds what the extractor carved out
    /// of the engine's key, and is asked the same way: here three bytes of
    /// the family id, which every seek in that family shares.
    #[test]
    fn a_region_from_before_the_forms_is_read_as_the_engine_key_form() {
        let bytes = region_before_forms(Some(&[&[0, 0, 0]]), &[b"prefix-key"]);
        let filter = FilterBlock::decode(&bytes).unwrap();
        assert_eq!(filter.prefix_form(), Some(PrefixForm::EngineKey));
        assert!(filter.may_contain(b"prefix-key"));
        assert!(lets_through(&filter, b"pre"));
        assert!(lets_through(&filter, b"zzz"));
        assert!(lets_through(&filter, b"pr"), "asked whatever its length");

        // And it rules out a seek whose engine key it does not hold.
        let absent = region_before_forms(Some(&[&[9, 9, 9]]), &[b"prefix-key"]);
        assert!(!lets_through(
            &FilterBlock::decode(&absent).unwrap(),
            b"pre"
        ));
    }

    #[test]
    fn a_prefix_bloom_of_an_unknown_form_is_left_unused_and_the_user_bloom_still_read() {
        let entry = prefix_key(1, b"pre");
        let mut bytes = region(PrefixForm::CallerKey, Some(&[&entry]), &[b"prefix-key"]);
        bytes[PREFIX_LEN_HEADER - 1] = 2;
        let filter = FilterBlock::decode(&bytes).unwrap();
        assert_eq!(filter.prefix_form(), None);
        assert!(lets_through(&filter, b"zzz"), "nothing is ruled out");
        assert!(filter.may_contain(b"prefix-key"));
        assert!(!filter.may_contain(b"another-key"));
    }

    /// What a build from before the forms makes of a caller-key table: it
    /// reads the whole header as the length, which runs past the region, so
    /// it refuses the table instead of asking its bloom the old way.
    #[test]
    fn a_caller_key_header_read_as_a_plain_length_runs_past_the_region() {
        let entry = prefix_key(1, b"pre");
        let bytes = region(PrefixForm::CallerKey, Some(&[&entry]), &[b"prefix-key"]);
        let header = u64::from_le_bytes(bytes[..PREFIX_LEN_HEADER].try_into().unwrap());
        assert!(header > bytes.len() as u64);
        assert_eq!(header >> PREFIX_FORM_SHIFT, 1);
    }

    #[test]
    fn a_prefix_bloom_too_large_for_the_header_is_refused_not_truncated() {
        let largest = usize::try_from(PREFIX_LEN_MASK).unwrap_or(usize::MAX);
        assert!(prefix_header(PrefixForm::CallerKey, largest).is_ok());
        if let Some(too_large) = largest.checked_add(1) {
            let err = prefix_header(PrefixForm::CallerKey, too_large).expect_err("too large");
            assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        }
    }

    #[test]
    fn rejects_short_region() {
        for len in 0..PREFIX_LEN_HEADER {
            let err = FilterBlock::decode(&vec![0u8; len]).expect_err("short region");
            assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        }
    }

    #[test]
    fn rejects_prefix_length_past_region() {
        let mut bytes = region(PrefixForm::CallerKey, None, &[b"k"]);
        for form in [PrefixForm::EngineKey, PrefixForm::CallerKey] {
            let claimed = prefix_header(form, bytes.len() + 1).unwrap();
            bytes[..PREFIX_LEN_HEADER].copy_from_slice(&claimed);
            let err = FilterBlock::decode(&bytes).expect_err("prefix past end");
            assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        }
    }

    #[test]
    fn rejects_truncated_prefix_bloom() {
        let mut bytes = region(PrefixForm::CallerKey, None, &[b"k"]);
        for form in [PrefixForm::EngineKey, PrefixForm::CallerKey] {
            bytes[..PREFIX_LEN_HEADER].copy_from_slice(&prefix_header(form, 2).unwrap());
            let err = FilterBlock::decode(&bytes).expect_err("prefix bloom too short");
            assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        }
    }

    #[test]
    fn rejects_truncated_user_bloom() {
        let bytes = vec![0u8; PREFIX_LEN_HEADER + 3];
        let err = FilterBlock::decode(&bytes).expect_err("user bloom too short");
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    }

    #[test]
    fn charge_covers_the_whole_region() {
        let entry = prefix_key(1, b"pre");
        let bytes = region(PrefixForm::CallerKey, Some(&[&entry]), &[b"a", b"b", b"c"]);
        let filter = FilterBlock::decode(&bytes).unwrap();
        assert!(filter.charge() >= bytes.len());
    }
}
