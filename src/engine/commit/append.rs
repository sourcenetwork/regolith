//! Numbering a commit's appends in the ordered step.
//!
//! A transaction's `append` calls queue as [`PendingAppend`]s and are not
//! read or validated for. The ordered step, which holds the pipeline mutex
//! and has already validated the commit's reads, gives each one the log's
//! next position and turns it into plain puts of the same atomic commit, so
//! the WAL carries final bytes. These rules follow `CommitOrderedAppend.tla`
//! and `Append.lean`:
//!
//! - Positions are assigned after validation, never before: a commit that
//!   fails validation reaches [`AppendOrder::number`] with nothing, so it
//!   takes no position.
//! - The head and the once keys come from the view plus the appends already
//!   numbered by this [`AppendOrder`], never from the view alone. One
//!   [`AppendOrder`] spans a commit group, so a later member counts from the
//!   head an earlier member left and sees the once keys it set.
//! - Nothing outlives the group: no cached head, no remembered once key. A
//!   group that fails drops its [`AppendOrder`] and the next group reads the
//!   view again, so a failure leaves no hole.
//!
//! A commit that carries no append never reaches this module.

use std::collections::HashSet;
use std::io;
use std::sync::Arc;

use super::super::callback;
use super::super::wal::{RecordLen, check_write_len};
use super::super::{ReadView, RegolithEngine};
use crate::column_family::{DEFAULT_CF_ID, prefix_key};
use crate::{Error, LogLayout, WriteBatchOp};

/// Length of the column-family prefix on the keys the engine stores.
const CF_PREFIX_LEN: usize = 4;

/// One `append` call a transaction queued: the log it names, the entry's
/// bytes, and the once key if the call gave one. Keys are as the caller wrote
/// them, without the column-family prefix.
#[derive(Clone)]
pub(crate) struct PendingAppend {
    pub(crate) log: Arc<dyn LogLayout>,
    pub(crate) entry: Vec<u8>,
    pub(crate) once_key: Option<Vec<u8>>,
}

/// Runs `f`, a call into the caller's [`LogLayout`]. Inside a commit a panic
/// in it is caught and returned as [`Error::CallbackPanicked`], which the
/// commit's boundary turns into the read-only latch.
fn layout<T>(f: impl FnOnce() -> T) -> io::Result<T> {
    callback::contain("LogLayout", f).map_err(Error::into_io_error)
}

/// The head one log has reached in the group being ordered.
struct LogHead {
    /// The log's head key, column-family prefixed.
    key: Vec<u8>,
    /// The newest position the view or an earlier member left.
    position: u64,
    /// A member of this group assigned a position, so the head key is
    /// written. A log nobody appended to is left alone.
    moved: bool,
}

/// The running state of the ordered step across one commit group's appends.
///
/// Create one per group, number every member against it in group order, and
/// drop it with the group.
#[derive(Default)]
pub(crate) struct AppendOrder {
    logs: Vec<LogHead>,
    /// Once keys, prefixed, that hold a position: set by an earlier append
    /// of this group, or found holding one in the view.
    taken: HashSet<Vec<u8>>,
    /// Scratch for the caller's `entry_key`.
    key: Vec<u8>,
}

impl AppendOrder {
    /// Numbers `appends`, in order, against `view` and the appends this
    /// order already numbered, and pushes the puts that write them onto
    /// `ops`: for each numbered append its entry and its once key, then, for
    /// each log that moved, its head key once.
    ///
    /// An append whose once key already holds a position, in the view or
    /// through an earlier append, writes nothing. On error `ops` may hold
    /// puts of appends numbered before it, and the caller drops the whole
    /// commit.
    pub(crate) fn number(
        &mut self,
        engine: &RegolithEngine,
        view: &ReadView,
        appends: Vec<PendingAppend>,
        ops: &mut Vec<WriteBatchOp>,
    ) -> io::Result<()> {
        for PendingAppend {
            log,
            entry,
            once_key,
        } in appends
        {
            let once_key = once_key.map(|key| prefix_key(DEFAULT_CF_ID, &key));
            if let Some(once) = &once_key
                && self.holds_position(engine, view, once)?
            {
                continue;
            }
            let at = self.head_of(engine, view, &*log)?;
            let position = self.logs[at].position.checked_add(1).ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "the log has used every position a 64-bit number can name",
                )
            })?;
            self.key.clear();
            let declared = layout(|| {
                log.entry_key(position, &mut self.key);
                log.max_entry_key_len()
            })?;
            if self.key.len() > declared {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!(
                        "a log layout built an entry key of {} bytes, longer than the {declared} it declared",
                        self.key.len(),
                    ),
                ));
            }
            ops.push(WriteBatchOp::Put {
                key: prefix_key(DEFAULT_CF_ID, &self.key),
                value: entry,
            });
            if let Some(once) = once_key {
                self.taken.insert(once.clone());
                ops.push(WriteBatchOp::Put {
                    key: once,
                    value: position.to_be_bytes().to_vec(),
                });
            }
            let head = &mut self.logs[at];
            head.position = position;
            head.moved = true;
        }
        Ok(())
    }

    /// Pushes the put of each moved log's head key onto `ops`, once per log,
    /// holding the last position this order assigned in it. Call it after the
    /// group's last [`AppendOrder::number`]; a group that assigned nothing
    /// pushes nothing.
    pub(crate) fn finish(self, ops: &mut Vec<WriteBatchOp>) {
        ops.extend(
            self.logs
                .into_iter()
                .filter(|head| head.moved)
                .map(|head| WriteBatchOp::Put {
                    key: head.key,
                    value: head.position.to_be_bytes().to_vec(),
                }),
        );
    }

    /// Whether `once` (prefixed) already holds a position: through an earlier
    /// append of this order, or in the view. A key found in the view is
    /// remembered, so the view is read once per key.
    fn holds_position(
        &mut self,
        engine: &RegolithEngine,
        view: &ReadView,
        once: &[u8],
    ) -> io::Result<bool> {
        if self.taken.contains(once) {
            return Ok(true);
        }
        let held = engine.read_u64_in_view(once, view)?.is_some();
        if held {
            self.taken.insert(once.to_vec());
        }
        Ok(held)
    }

    /// The index in `self.logs` of `log`'s head, read from the view the first
    /// time this order meets the log.
    fn head_of(
        &mut self,
        engine: &RegolithEngine,
        view: &ReadView,
        log: &dyn LogLayout,
    ) -> io::Result<usize> {
        let key = layout(|| prefix_key(DEFAULT_CF_ID, log.head_key()))?;
        // vertexia: linear scan over the logs of one group, which is a
        // handful; a map if a group ever spans thousands of logs.
        if let Some(at) = self.logs.iter().position(|head| head.key == key) {
            return Ok(at);
        }
        let position = engine.read_u64_in_view(&key, view)?.unwrap_or(0);
        self.logs.push(LogHead {
            key,
            position,
            moved: false,
        });
        Ok(self.logs.len() - 1)
    }
}

impl RegolithEngine {
    /// Refuses a commit whose appends cannot fit, before it waits for a place
    /// in the pipeline: a key or entry past the configured limits, or a
    /// record that would pass the WAL limit once the appends are numbered.
    ///
    /// Positions do not exist yet, so each entry key counts at its layout's
    /// declared maximum and each log counts its head put once. The ordered
    /// step re-checks the keys it builds; the bound only makes this answer
    /// early.
    pub(super) fn validate_append_sizes(
        &self,
        ops: &[WriteBatchOp],
        appends: &[PendingAppend],
    ) -> io::Result<()> {
        let mut record = RecordLen::default();
        ops.iter().for_each(|op| record.op(op));
        let mut heads: Vec<&[u8]> = Vec::new();
        for append in appends {
            let log = &*append.log;
            let (head, max_entry_key) = layout(|| (log.head_key(), log.max_entry_key_len()))?;
            self.validate_user_key_len(head.len())?;
            self.validate_user_key_len(max_entry_key)?;
            self.validate_value_size(&append.entry)?;
            record.put_sized(CF_PREFIX_LEN + max_entry_key, append.entry.len());
            if let Some(once) = &append.once_key {
                self.validate_user_key_len(once.len())?;
                record.put_sized(CF_PREFIX_LEN + once.len(), size_of::<u64>());
            }
            // vertexia: linear scan over the distinct logs of one commit;
            // a set if a commit ever spans thousands of logs.
            if !heads.contains(&head) {
                heads.push(head);
                record.put_sized(CF_PREFIX_LEN + head.len(), size_of::<u64>());
            }
        }
        check_write_len(record.framed())
    }
}
