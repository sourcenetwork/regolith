//! `Transaction::append`: queueing entries for a commit-ordered log.
//!
//! The transaction only queues. A position is the log's next number at the
//! moment the commit is ordered, so it cannot exist before commit and the
//! transaction cannot read its own appends. The numbering is in
//! `engine::commit::append`.

use std::sync::Arc;

use super::policy::classifier_for;
use super::{KeyClass, KeyClassifier, Transaction, TransactionError, TxResult};
use crate::engine::PendingAppend;
use crate::txn_buffer::TxnBuffer;
use crate::{Error, LogLayout};

impl Transaction {
    /// Adds `entry` to the commit-ordered log `log` describes, at the
    /// position the commit gives it.
    ///
    /// Nothing is written until commit. In the ordered step of the commit,
    /// after the transaction's reads are validated and before the write-ahead
    /// log is written, regolith:
    ///
    /// 1. skips the append, writing nothing, when `once_key` is given and
    ///    already holds a position, whether from an earlier commit or from an
    ///    earlier `append` of this transaction or of a commit in the same
    ///    group;
    /// 2. otherwise gives the entry the log's next position `p`, one past the
    ///    newest position any earlier commit, or earlier `append` of this
    ///    commit, took: dense from 1; and
    /// 3. writes `entry_key(p) = entry`, `once_key = p` (when given, as an
    ///    8-byte big-endian number) and `head_key = p`, in the same atomic
    ///    commit as the transaction's other writes.
    ///
    /// # Guarantees
    ///
    /// - **Commit order, no holes.** Positions follow commit order. Several
    ///   appends to one log in one transaction take consecutive positions in
    ///   the order they were made. A transaction that aborts, fails
    ///   validation or fails to reach the log takes no position, and the next
    ///   commit reuses it. A reader that reads the head key in a snapshot, and
    ///   then the entries up to it, finds every one of them.
    /// - **Never a conflict.** An append is never validated, so it cannot
    ///   fail a commit and no other commit's write can fail it. The head key
    ///   is not part of the transaction's read or write set, so two
    ///   transactions that append to one log and touch nothing else in
    ///   common both commit. This holds at every isolation level, for an
    ///   optimistic and a pessimistic transaction alike; `append` takes no
    ///   lock.
    /// - **At most once.** Of any number of appends sharing a `once_key`, in
    ///   one transaction or in many, only the first to commit writes an
    ///   entry. The key then holds the entry's position, so a caller can
    ///   look an entry up by it.
    /// - **Own appends are invisible.** The positions do not exist until
    ///   commit, so nothing this transaction reads, a scan of the log
    ///   included, shows its own appends.
    /// - **Rollback.** A savepoint saves the appends made before it, and
    ///   `rollback_to_savepoint` drops those made after.
    ///
    /// Durability is the database's. Under
    /// [`DurabilityMode::Eventual`](crate::DurabilityMode::Eventual) a crash
    /// can lose committed appends, and the next commit then gives their
    /// positions to other entries; the database stays consistent, but a
    /// consumer outside it that recorded a position should use
    /// [`DurabilityMode::Immediate`](crate::DurabilityMode::Immediate).
    ///
    /// # Errors
    ///
    /// Refused here, with the transaction unchanged, as
    /// [`Error::InvalidArgument`]: a layout whose entry key for the largest
    /// position is longer than [`LogLayout::max_entry_key_len`], and, when a
    /// [`KeyClassifier`] is installed and applies to this transaction (an
    /// optimistic transaction at [`IsolationLevel::DefraLevel`]), a layout
    /// whose head or entry key, or a `once_key`, the classifier does not
    /// declare [`KeyClass::Log`]. At commit, a key or entry beyond the
    /// database's size limits, a commit too large to log, a head or once key
    /// that holds anything but eight bytes, or a layout that builds an entry
    /// key longer than it declared fails the commit with
    /// [`Error::InvalidArgument`], and nothing is applied.
    ///
    /// # Preconditions
    ///
    /// Only appends write the keys of a log. A write to them by anything
    /// else, a plain [`Db::put`](crate::Db::put) or a pessimistic
    /// transaction (which consults no classifier) included, can number two
    /// entries alike or leave the head behind its entries, and regolith
    /// cannot tell. The layout must follow the contract of [`LogLayout`], and
    /// a log must be appended to through one layout, and no two logs may
    /// share a key.
    ///
    /// [`IsolationLevel::DefraLevel`]: crate::IsolationLevel::DefraLevel
    pub fn append(
        &self,
        log: &Arc<dyn LogLayout>,
        entry: &[u8],
        once_key: Option<&[u8]>,
    ) -> TxResult<()> {
        check_layout(
            &**log,
            once_key,
            classifier_for(&self.policy, self.isolation),
        )?;
        self.appends
            .get_or_init(|| Box::new(TxnBuffer::new(0)))
            .insert(
                (),
                PendingAppend {
                    log: Arc::clone(log),
                    entry: entry.to_vec(),
                    once_key: once_key.map(<[u8]>::to_vec),
                },
            );
        Ok(())
    }

    /// Refuses a put, delete or merge of `key` when the installed classifier
    /// declares it [`KeyClass::Log`]. A transaction with no classifier to
    /// consult, which is every pessimistic one, accepts it.
    pub(super) fn refuse_log_key(&self, key: &[u8]) -> TxResult<()> {
        match classifier_for(&self.policy, self.isolation) {
            Some(classifier) if classifier.classify(key) == KeyClass::Log => {
                Err(TransactionError::Engine(Error::LogKeyWrite))
            }
            _ => Ok(()),
        }
    }

    /// How many appends the transaction has made: the mark a savepoint keeps.
    pub(super) fn appends_len(&self) -> usize {
        self.appends.get().map_or(0, |appends| appends.len())
    }

    /// Takes back the appends made after a savepoint that marked `len` of them.
    pub(super) fn truncate_appends(&mut self, len: usize) {
        if let Some(appends) = self.appends.get_mut() {
            appends.truncate(len);
        }
    }
}

/// Checks what `append` can know without a position: the longest entry key
/// the layout builds fits what it declared, and, when `classifier` applies,
/// every key of the log is a [`KeyClass::Log`] key.
///
/// The longest position stands for every other: a layout that grows its keys
/// with the position, as a decimal or hexadecimal rendering does, is longest
/// there. The commit checks the keys it actually builds.
fn check_layout(
    log: &dyn LogLayout,
    once_key: Option<&[u8]>,
    classifier: Option<&dyn KeyClassifier>,
) -> TxResult<()> {
    let mut entry_key = Vec::new();
    log.entry_key(u64::MAX, &mut entry_key);
    let declared = log.max_entry_key_len();
    if entry_key.len() > declared {
        return Err(refused(format!(
            "a log layout builds an entry key of {} bytes but declares a maximum of {declared}",
            entry_key.len()
        )));
    }
    if let Some(classifier) = classifier {
        let log_keys = [log.head_key(), entry_key.as_slice()]
            .into_iter()
            .chain(once_key)
            .all(|key| classifier.classify(key) == KeyClass::Log);
        if !log_keys {
            return Err(refused(
                "the installed key classifier does not declare every key of this log \
                 (head, entry and once keys) as a log key"
                    .to_owned(),
            ));
        }
    }
    Ok(())
}

fn refused(message: String) -> TransactionError {
    TransactionError::Engine(Error::InvalidArgument(message))
}
