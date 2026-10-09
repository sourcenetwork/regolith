//! Repair the overlapping runs a legacy ingest could record.
//!
//! Old manifests list surviving tables in installation order. Keep that
//! order within each demoted level, and keep shallower levels newer than
//! deeper ones. Key-sorting first would lose the age of an ingested table
//! whose range tombstone widened its recorded range.

use std::collections::BTreeSet;

use super::*;

#[derive(Default)]
pub(super) struct Repair {
    pub(super) records: Vec<ManifestRecord>,
    pub(super) tables: u64,
    deepest_level: usize,
}

impl Repair {
    /// Move the whole prefix through the deepest overlapping level into
    /// L0. Its oldest-to-newest order is deep levels, shallow levels, then
    /// the existing L0. Demoting only the offending level would put its
    /// older values ahead of newer shallow-level values.
    pub(super) fn prepare(levels: &mut [Vec<SsTableMeta>]) -> io::Result<Self> {
        let deepest = levels
            .iter()
            .enumerate()
            .skip(1)
            .rev()
            .find(|(_, files)| overlaps(files))
            .map(|(level, _)| level);
        let Some(deepest_level) = deepest else {
            return Ok(Self::default());
        };

        // Moving a duplicate reference would replay a merge twice. It
        // is not the range-widening defect this repair accounts for.
        let mut seen = BTreeSet::new();
        let mut records = Vec::new();
        let mut tables = 0;
        for (level, files) in levels.iter().enumerate().take(deepest_level + 1) {
            for meta in files {
                if !seen.insert(meta.file_id) && level > 0 {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!(
                            "manifest lists table {} more than once while repairing overlapping levels",
                            meta.file_id
                        ),
                    ));
                }
                records.push(ManifestRecord::RemoveFile {
                    level,
                    file_id: meta.file_id,
                });
                tables += u64::from(level > 0);
            }
        }

        let old_l0 = std::mem::take(&mut levels[0]);
        for level in (1..=deepest_level).rev() {
            let files = std::mem::take(&mut levels[level]);
            levels[0].extend(files);
        }
        levels[0].extend(old_l0);
        records.extend(levels[0].iter().map(|meta| ManifestRecord::AddFile {
            level: 0,
            meta: meta.clone(),
        }));
        Ok(Self {
            records,
            tables,
            deepest_level,
        })
    }

    /// All removals and re-additions share one synced frame. A crash
    /// leaves either the old layout (repairable again) or the new one.
    pub(super) fn persist(&self, writer: &mut BufferedWriter) -> io::Result<u64> {
        if self.records.is_empty() {
            return Ok(0);
        }
        let bytes = VersionSet::encode_records(&self.records)?;
        writer.write_all(&bytes)?;
        writer.sync_all()?;
        Ok(bytes.len() as u64)
    }

    pub(super) fn report(&self, manifest: &Path, read_only: bool) {
        if self.tables > 0 {
            tracing::warn!(
                path = %manifest.display(),
                deepest_level = self.deepest_level,
                tables_demoted = self.tables,
                read_only,
                "demoted overlapping legacy levels to L0"
            );
        }
    }
}

/// Check key order without changing the installation order needed by a
/// repair. Already key-ordered runs need no temporary allocation.
fn overlaps(files: &[SsTableMeta]) -> bool {
    if files.is_sorted_by(|a, b| a.smallest_key <= b.smallest_key) {
        return files
            .windows(2)
            .any(|p| p[0].largest_key > p[1].smallest_key);
    }
    let mut sorted: Vec<_> = files.iter().collect();
    sorted.sort_by(|a, b| a.smallest_key.cmp(&b.smallest_key));
    sorted
        .windows(2)
        .any(|p| p[0].largest_key > p[1].smallest_key)
}
