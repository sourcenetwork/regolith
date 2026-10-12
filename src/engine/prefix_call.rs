//! Every call the engine makes of the caller's [`PrefixExtractor`], and the
//! two forms a table's prefix bloom comes in.
//!
//! The extractor is the caller's code, and it carves a prefix out of the
//! caller's key. So a table built here asks it about the key as the caller
//! wrote it, never about one of the database's own entries, and a prefix
//! seek asks it about the prefix the caller passed. What the table's prefix
//! bloom then holds is the id of the key's column family followed by what
//! the extractor returned: the id is put back so that one prefix in two
//! column families is two entries, and a seek in one family is not answered
//! by the other's keys.
//!
//! That is the [`PrefixForm::CallerKey`] form. A table written before it
//! existed holds [`PrefixForm::EngineKey`]: the extractor was asked about
//! the engine's key, the family id in front of the caller's, and the bloom
//! holds what it returned. Such a table is still filtered exactly as it was
//! built, by asking the extractor the same way, so nothing it holds is
//! ruled out wrongly. It is the one place the extractor still sees an
//! engine key, and only while such a table is in level 0: a compaction
//! writes every table in the caller-key form. Nothing starts a table in the
//! old form any more, outside this crate's own tests.
//!
//! A table says which form it holds in the header of its bloom region
//! (`filter_block`), and a seek asks each table in the table's own form
//! ([`PrefixProbe`]).

use crate::column_family::{CF_PREFIX_LEN, META_CF_ID};
use crate::options::PrefixExtractor;

/// Which key a table's prefix bloom was built from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PrefixForm {
    /// The engine's key. Read; written only by this crate's tests.
    EngineKey,
    /// The caller's key, with the family id in front of each entry.
    CallerKey,
}

impl PrefixForm {
    /// The byte a table records this form as.
    pub(crate) fn tag(self) -> u8 {
        match self {
            Self::EngineKey => 0,
            Self::CallerKey => 1,
        }
    }

    /// The form a table recorded as `tag`, or `None` for a form this build
    /// does not know: a later one, whose bloom it then does not use.
    pub(crate) fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::EngineKey),
            1 => Some(Self::CallerKey),
            _ => None,
        }
    }
}

/// Split an engine key into its family id and the caller's key. `None` for a
/// key too short to carry an id, and for one of the database's own entries,
/// which the caller's extractor is never asked about.
fn callers(prefixed: &[u8]) -> Option<(&[u8; CF_PREFIX_LEN], &[u8])> {
    let (family, key) = prefixed.split_first_chunk::<CF_PREFIX_LEN>()?;
    (u32::from_be_bytes(*family) != META_CF_ID).then_some((family, key))
}

/// The bloom entry of `form` for the engine key `prefixed`, written into
/// `out`. In the caller-key form that is the family id, then what the
/// extractor carves out of the caller's key. `false`, with `out` empty, when
/// the key gets no entry.
pub(crate) fn entry(
    form: PrefixForm,
    extractor: &dyn PrefixExtractor,
    prefixed: &[u8],
    out: &mut Vec<u8>,
) -> bool {
    out.clear();
    match form {
        PrefixForm::CallerKey => {
            let Some((family, key)) = callers(prefixed) else {
                return false;
            };
            let Some(prefix) = extractor.extract(key) else {
                return false;
            };
            out.extend_from_slice(family);
            out.extend_from_slice(prefix);
        }
        PrefixForm::EngineKey => {
            let Some(prefix) = extractor.extract(prefixed) else {
                return false;
            };
            out.extend_from_slice(prefix);
        }
    }
    true
}

/// The bloom keys of one prefix seek, one for each form a table's prefix
/// bloom comes in.
pub(crate) struct PrefixProbe<'a> {
    extractor: &'a dyn PrefixExtractor,
    /// The seek's prefix as the engine keys it.
    prefixed: &'a [u8],
    /// `None` when the extractor derives no bloom key from the caller's
    /// prefix: the seek then rules out no table of the caller-key form.
    caller_key: Option<Vec<u8>>,
    /// Made the first time the seek meets a table of the engine-key form,
    /// so a database with none never asks the extractor about an engine
    /// key. `Some(None)`: asked, and the extractor gave no key.
    engine_key: Option<Option<Vec<u8>>>,
}

impl<'a> PrefixProbe<'a> {
    /// The probe of a seek for the engine prefix `prefixed`. The extractor
    /// is asked about the caller's prefix here, once.
    pub(crate) fn new(extractor: &'a dyn PrefixExtractor, prefixed: &'a [u8]) -> Self {
        let caller_key = callers(prefixed).and_then(|(family, prefix)| {
            let extracted = extractor.extract_query(prefix)?;
            let mut key = Vec::with_capacity(CF_PREFIX_LEN + extracted.len());
            key.extend_from_slice(family);
            key.extend_from_slice(extracted);
            Some(key)
        });
        Self {
            extractor,
            prefixed,
            caller_key,
            engine_key: None,
        }
    }

    /// The bloom key to ask a table of `form` with, or `None` when there is
    /// none, in which case the table is not ruled out.
    pub(crate) fn key_for(&mut self, form: PrefixForm) -> Option<&[u8]> {
        match form {
            PrefixForm::CallerKey => self.caller_key.as_deref(),
            PrefixForm::EngineKey => {
                let (extractor, prefixed) = (self.extractor, self.prefixed);
                self.engine_key
                    .get_or_insert_with(|| extractor.extract_query(prefixed).map(<[u8]>::to_vec))
                    .as_deref()
            }
        }
    }
}

#[cfg(test)]
thread_local! {
    /// Test seam: while set, a table this thread starts builds its prefix
    /// bloom in the engine-key form.
    static WRITE_ENGINE_KEY_FORM: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// The form a table started now builds its prefix bloom in: the caller-key
/// form, except in a test of this crate that asked for the old one.
pub(crate) fn form_to_write() -> PrefixForm {
    #[cfg(test)]
    if WRITE_ENGINE_KEY_FORM.with(std::cell::Cell::get) {
        return PrefixForm::EngineKey;
    }
    PrefixForm::CallerKey
}

/// Test-only: run `f` with every table this thread starts built in the
/// engine-key form, as tables written before the caller-key form were.
#[cfg(test)]
pub(crate) fn writing_engine_key_form<T>(f: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            WRITE_ENGINE_KEY_FORM.with(|form| form.set(self.0));
        }
    }
    let _restore = Restore(WRITE_ENGINE_KEY_FORM.with(|form| form.replace(true)));
    f()
}

#[cfg(test)]
mod tests {
    use std::sync::Mutex;

    use super::*;
    use crate::column_family::prefix_key;
    use crate::options::FixedLengthPrefix;

    /// The first three bytes, recording what it is asked.
    #[derive(Default)]
    struct Asked {
        keys: Mutex<Vec<Vec<u8>>>,
        seeks: Mutex<Vec<Vec<u8>>>,
    }

    impl PrefixExtractor for Asked {
        fn extract<'a>(&self, key: &'a [u8]) -> Option<&'a [u8]> {
            self.keys.lock().unwrap().push(key.to_vec());
            FixedLengthPrefix(3).extract(key)
        }

        fn extract_query<'a>(&self, prefix: &'a [u8]) -> Option<&'a [u8]> {
            self.seeks.lock().unwrap().push(prefix.to_vec());
            FixedLengthPrefix(3).extract_query(prefix)
        }

        fn name(&self) -> &'static str {
            "asked"
        }
    }

    #[test]
    fn an_entry_is_the_family_id_and_the_prefix_of_the_callers_key() {
        let extractor = Asked::default();
        let form = PrefixForm::CallerKey;
        let mut out = vec![9];
        assert!(entry(form, &extractor, &prefix_key(7, b"abcdef"), &mut out));
        assert_eq!(out, prefix_key(7, b"abc"));
        // Too short for the extractor: no entry.
        assert!(!entry(form, &extractor, &prefix_key(7, b"ab"), &mut out));
        assert!(out.is_empty());
        assert_eq!(
            *extractor.keys.lock().unwrap(),
            [b"abcdef".to_vec(), b"ab".to_vec()],
            "asked about the caller's key"
        );
    }

    #[test]
    fn the_databases_own_entries_get_no_entry_and_are_not_shown() {
        let extractor = Asked::default();
        let form = PrefixForm::CallerKey;
        let registry = prefix_key(META_CF_ID, b"name:x");
        let mut out = Vec::new();
        assert!(!entry(form, &extractor, &registry, &mut out));
        assert!(!entry(form, &extractor, b"abc", &mut out), "no family id");
        let registry_prefix = prefix_key(META_CF_ID, b"name:");
        let mut probe = PrefixProbe::new(&extractor, &registry_prefix);
        assert_eq!(probe.key_for(form), None);
        assert!(extractor.keys.lock().unwrap().is_empty());
        assert!(extractor.seeks.lock().unwrap().is_empty());
    }

    #[test]
    fn an_engine_key_entry_is_what_the_extractor_carves_out_of_the_engines_key() {
        let extractor = Asked::default();
        let prefixed = prefix_key(7, b"abcdef");
        let mut out = Vec::new();
        assert!(entry(
            PrefixForm::EngineKey,
            &extractor,
            &prefixed,
            &mut out
        ));
        assert_eq!(out, [0, 0, 0], "three bytes of the family id");
        assert_eq!(*extractor.keys.lock().unwrap(), [prefixed]);
    }

    #[test]
    fn a_seek_asks_about_the_callers_prefix_and_about_the_engines_only_for_an_old_table() {
        let extractor = Asked::default();
        let prefixed = prefix_key(7, b"abcd");
        let mut probe = PrefixProbe::new(&extractor, &prefixed);
        let caller_key = prefix_key(7, b"abc");
        assert_eq!(probe.key_for(PrefixForm::CallerKey), Some(&caller_key[..]));
        assert_eq!(probe.key_for(PrefixForm::CallerKey), Some(&caller_key[..]));
        assert_eq!(*extractor.seeks.lock().unwrap(), [b"abcd".to_vec()]);

        // The engine-key form: the first three bytes of the engine's key,
        // which are bytes of the family id, asked for once.
        assert_eq!(probe.key_for(PrefixForm::EngineKey), Some(&[0, 0, 0][..]));
        assert_eq!(probe.key_for(PrefixForm::EngineKey), Some(&[0, 0, 0][..]));
        assert_eq!(
            *extractor.seeks.lock().unwrap(),
            [b"abcd".to_vec(), prefixed.clone()]
        );
    }

    /// A prefix shorter than the extractor's width rules out no table of
    /// the caller-key form, and an old table is still asked the way it was
    /// built: with what the extractor carves out of the engine's prefix.
    #[test]
    fn a_prefix_the_extractor_gives_no_key_for_asks_only_an_old_table() {
        let extractor = Asked::default();
        let prefixed = prefix_key(7, b"ab");
        let mut probe = PrefixProbe::new(&extractor, &prefixed);
        assert_eq!(probe.key_for(PrefixForm::CallerKey), None);
        assert_eq!(probe.key_for(PrefixForm::EngineKey), Some(&[0, 0, 0][..]));

        let short = [0, 7];
        let mut probe = PrefixProbe::new(&extractor, &short);
        assert_eq!(probe.key_for(PrefixForm::CallerKey), None);
        assert_eq!(probe.key_for(PrefixForm::EngineKey), None);
    }

    #[test]
    fn a_form_round_trips_through_its_tag_and_an_unknown_tag_is_no_form() {
        for form in [PrefixForm::EngineKey, PrefixForm::CallerKey] {
            assert_eq!(PrefixForm::from_tag(form.tag()), Some(form));
        }
        assert_eq!(PrefixForm::from_tag(2), None);
        assert_eq!(PrefixForm::from_tag(0xFF), None);
    }

    #[test]
    fn a_table_is_started_in_the_caller_key_form_unless_a_test_asks_for_the_old_one() {
        assert_eq!(form_to_write(), PrefixForm::CallerKey);
        writing_engine_key_form(|| assert_eq!(form_to_write(), PrefixForm::EngineKey));
        assert_eq!(form_to_write(), PrefixForm::CallerKey);
    }
}
