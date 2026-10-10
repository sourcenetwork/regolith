//! Column-family births and deaths, ordered with the writes (plan 4.6).
//!
//! The registry ([`CfRegistry`]) is read without a lock everywhere. What
//! keeps a family's life consistent with the data is *where* it changes and
//! where it is checked: both happen in the ordered commit step, under the
//! pipeline mutex every write group already holds.
//!
//! - **A write is fenced at admission.** Before a request joins a group (it
//!   takes no sequence until then), [`RegolithEngine::cf_fence`] checks every
//!   family its keys name. A request naming a dropped family is refused
//!   whole, with nothing logged and no sequence taken.
//! - **A drop is a group of its own, then a retire.** [`RegolithEngine::drop_family`]
//!   commits the family's range tombstone and meta delete as a group of one,
//!   and only after that group is durable and applied removes the family from
//!   the registry, still holding the mutex. Every write admitted before it
//!   took a lower sequence, so the tombstone deletes it; every write admitted
//!   after sees the family gone.
//! - **A create is a group of its own, then a publish.** [`RegolithEngine::create_family`]
//!   draws the next id, commits the meta entry, and publishes the family only
//!   once that commit succeeded, so no handle exists for a family the log
//!   does not hold.
//!
//! So a write to a family lands only while the family is live, and a write
//! racing a drop is either deleted by the drop or refused: never committed
//! after the tombstone, where it would be invisible to every handle and never
//! reclaimed. `proofs/tla/CfRegistry.tla` and `proofs/lean/Regolith/CfRegistry.lean`
//! model exactly this order, with the fence moved out of the ordered step as
//! the bug they rule out.

use std::collections::BTreeMap;
use std::io;
use std::sync::Arc;

use super::super::{DurabilityMode, RegolithEngine, grouped_batch_ops};
use super::{GroupTicket, WriteRequest, release_stranded};
use crate::WriteBatchOp;
use crate::column_family::{
    CF_PREFIX_LEN, CfRegistry, ColumnFamilyHandle, DEFAULT_CF_ID, META_CF_ID, cf_lower_bound,
    cf_upper_bound, cf_upper_bound_bytes, dropped_family_error, invalid_handle_error, meta,
};

impl RegolithEngine {
    /// Hand the engine the database's column-family registry, so the ordered
    /// step fences writes against it. `Db::open` calls this once, before the
    /// first write; an engine with no registry (the engine's own tests,
    /// whose keys carry no family prefix) fences nothing.
    pub(crate) fn attach_families(&self, families: Arc<CfRegistry>) {
        // A second attach would be a second `Db` over one engine, which
        // `Db::open` never builds; the first registry stays.
        let _ = self.families.set(families);
    }

    fn families(&self) -> io::Result<&CfRegistry> {
        self.families.get().map(Arc::as_ref).ok_or_else(|| {
            io::Error::other("column families need the database's registry, which is not attached")
        })
    }

    /// Refuse `request` when a key in it names a column family that is not
    /// live. Runs in the ordered step, under the pipeline mutex, before the
    /// request joins a group: that is what orders it against a drop.
    pub(super) fn cf_fence(&self, request: &WriteRequest) -> io::Result<()> {
        match request {
            WriteRequest::Idle => Ok(()),
            WriteRequest::Put { key, .. } => self.cf_fence_keys(std::iter::once(key.as_slice())),
            WriteRequest::Batch { ops, .. } => self.cf_fence_ops(ops),
        }
    }

    /// [`Self::cf_fence`] over a batch's operations.
    pub(super) fn cf_fence_ops(&self, ops: &[WriteBatchOp]) -> io::Result<()> {
        let Some(families) = self.families.get() else {
            return Ok(());
        };
        let mut last = None;
        for op in ops {
            match op {
                WriteBatchOp::Put { key, .. }
                | WriteBatchOp::Delete { key }
                | WriteBatchOp::Merge { key, .. } => fence_key(families, &mut last, key)?,
                WriteBatchOp::DeleteRange { start, end } => {
                    fence_key(families, &mut last, start)?;
                    // A range that ends at the next family's first key (a
                    // whole-family delete) writes nothing in that family.
                    let whole_family = family_of(start)
                        .is_some_and(|id| end.as_slice() == cf_upper_bound_bytes(id));
                    if !whole_family {
                        fence_key(families, &mut last, end)?;
                    }
                }
            }
        }
        Ok(())
    }

    /// [`Self::cf_fence`] over a run of keys.
    fn cf_fence_keys<'a>(&self, keys: impl IntoIterator<Item = &'a [u8]>) -> io::Result<()> {
        let Some(families) = self.families.get() else {
            return Ok(());
        };
        let mut last = None;
        keys.into_iter()
            .try_for_each(|key| fence_key(families, &mut last, key))
    }

    /// [`Self::cf_fence`] over the families an ingested table holds keys of.
    pub(crate) fn cf_fence_ids(&self, ids: &[u32]) -> io::Result<()> {
        let Some(families) = self.families.get() else {
            return Ok(());
        };
        let mut last = None;
        ids.iter()
            .try_for_each(|id| fence_id(families, &mut last, *id))
    }

    /// Create the column family `name`, or return the live one of that name.
    ///
    /// Draws the next id, commits its meta entry and the advanced id counter
    /// as a group of one, and publishes the family only once that group is
    /// durable and applied. Concurrent creates of one name are ordered by
    /// the pipeline mutex, so the second finds the first's family.
    pub(crate) fn create_family(
        &self,
        name: &str,
        durability: DurabilityMode,
    ) -> io::Result<ColumnFamilyHandle> {
        let families = self.families()?;
        self.ensure_writable()?;
        let mut pipe = self.pipeline.lock();
        if let Some(existing) = families.get(name) {
            return Ok(existing);
        }
        let Some(id) = families.next_id() else {
            return Err(
                crate::Error::invalid_argument("the column-family id space is exhausted")
                    .into_io_error(),
            );
        };
        let mut point_ops = BTreeMap::new();
        point_ops.insert(meta::name_key(name), Some(id.to_be_bytes().to_vec()));
        point_ops.insert(meta::next_id_key(), Some((id + 1).to_be_bytes().to_vec()));
        let request = WriteRequest::Batch {
            ops: grouped_batch_ops(point_ops, Vec::new(), Vec::new()),
            durability,
            disable_wal: false,
        };
        release_stranded(&mut pipe.group);
        pipe.group.push(GroupTicket {
            slot: None,
            request,
        });
        let view = self.view.load();
        let result = self.run_and_complete(&mut pipe, view);
        // Published inside the ordered step, before any later group runs.
        let created = result.map(|_| families.publish(id, name));
        self.drain_locked(&mut pipe);
        created
    }

    /// Drop the column family `cf`.
    ///
    /// Commits a range tombstone over the family's keys and the delete of
    /// its meta entry as a group of one, then retires the family from the
    /// registry before releasing the pipeline mutex. A handle that is not
    /// live when the drop reaches the ordered step (another drop won) is
    /// refused there.
    pub(crate) fn drop_family(
        &self,
        cf: &ColumnFamilyHandle,
        durability: DurabilityMode,
    ) -> io::Result<()> {
        let families = self.families()?;
        self.ensure_writable()?;
        let mut pipe = self.pipeline.lock();
        if !families.is_live_handle(cf) {
            return Err(invalid_handle_error(cf).into_io_error());
        }
        let mut point_ops = BTreeMap::new();
        point_ops.insert(meta::name_key(cf.name()), None);
        let range = (cf_lower_bound(cf.id()), cf_upper_bound(cf.id()));
        let request = WriteRequest::Batch {
            ops: grouped_batch_ops(point_ops, vec![range], Vec::new()),
            durability,
            disable_wal: false,
        };
        release_stranded(&mut pipe.group);
        pipe.group.push(GroupTicket {
            slot: None,
            request,
        });
        let view = self.view.load();
        let result = self.run_and_complete(&mut pipe, view);
        if result.is_ok() {
            // The tombstone is durable and applied: from this retire on, the
            // fence refuses every write to the family.
            families.retire(cf.id());
        }
        self.drain_locked(&mut pipe);
        result.map(|_| ())
    }
}

/// The family a prefixed key belongs to, or `None` for a key too short to
/// carry one.
fn family_of(key: &[u8]) -> Option<u32> {
    key.first_chunk::<CF_PREFIX_LEN>()
        .map(|prefix| u32::from_be_bytes(*prefix))
}

fn fence_key(families: &CfRegistry, last: &mut Option<u32>, key: &[u8]) -> io::Result<()> {
    match family_of(key) {
        Some(id) => fence_id(families, last, id),
        // Every key a `Db` writes carries its family; a shorter one cannot
        // name a family to land in.
        None => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "a write key is shorter than its column-family prefix",
        )),
    }
}

/// Refuse `id` unless it is live. `last` remembers the id just found live,
/// so a run of keys in one family costs one lookup.
fn fence_id(families: &CfRegistry, last: &mut Option<u32>, id: u32) -> io::Result<()> {
    // The default family is never dropped, and the meta family is written
    // only by create and drop themselves (a caller's write to it is refused
    // at the API boundary).
    if *last == Some(id) || id == DEFAULT_CF_ID || id == META_CF_ID {
        return Ok(());
    }
    if !families.contains_id(id) {
        return Err(dropped_family_error(id).into_io_error());
    }
    *last = Some(id);
    Ok(())
}
