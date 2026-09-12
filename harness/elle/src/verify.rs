//! A standalone witness detector for the anomaly this harness targets.
//!
//! elle-cli is the authority on whether a history is valid. This module
//! exists so the harness still produces evidence on a machine with no
//! JVM, and so a failure can be pointed at a concrete pair of
//! operations rather than a cycle diagram.
//!
//! Both checks are stated against real time and are therefore sound
//! under strict serializability, which is elle-cli's default
//! consistency model: once a transaction commits at time `t`, a
//! transaction that is *invoked* after `t` must not observe a state
//! older than that commit.

use std::collections::HashMap;
use std::path::Path;

use crate::cli::Model;
use crate::history::{MopVal, Op, OpKind};

/// One committed operation paired with the time its transaction was
/// invoked and the time it completed.
struct Completed {
    op: Op,
    invoked: u64,
}

pub struct Report {
    pub ops: usize,
    pub committed: usize,
    pub witnesses: Vec<String>,
}

impl Report {
    pub fn anomalous(&self) -> bool {
        !self.witnesses.is_empty()
    }
}

pub fn verify(path: &Path, model: Model) -> Result<Report, String> {
    let raw =
        std::fs::read_to_string(path).map_err(|e| format!("read {}: {}", path.display(), e))?;
    let ops: Vec<Op> =
        serde_json::from_str(&raw).map_err(|e| format!("parse {}: {}", path.display(), e))?;

    let mut pending: HashMap<u64, u64> = HashMap::new();
    let mut committed: Vec<Completed> = Vec::new();
    for op in &ops {
        match op.kind {
            OpKind::Invoke => {
                pending.insert(op.process, op.time);
            }
            _ => {
                let invoked = pending.remove(&op.process).unwrap_or(op.time);
                if op.kind == OpKind::Ok {
                    committed.push(Completed {
                        op: op.clone(),
                        invoked,
                    });
                }
            }
        }
    }

    let witnesses = match model {
        Model::ListAppend => lost_appends(&committed),
        Model::RwRegister => stale_reads(&committed),
    };

    Ok(Report {
        ops: ops.len(),
        committed: committed.len(),
        witnesses,
    })
}

/// A committed append that a later transaction failed to observe, plus
/// the append that displaced it. The displacing append proves the read
/// side of a read-modify-write ran against a stale snapshot.
fn lost_appends(committed: &[Completed]) -> Vec<String> {
    let mut appended: Vec<(i64, i64, u64, u64)> = Vec::new();
    for entry in committed {
        for mop in &entry.op.value {
            if let ("append", MopVal::Int(v)) = (mop.0.as_str(), &mop.2) {
                appended.push((mop.1, *v, entry.op.time, entry.op.index));
            }
        }
    }

    let mut witnesses = Vec::new();
    for &(key, value, committed_at, index) in &appended {
        for entry in committed {
            if entry.invoked <= committed_at {
                continue;
            }
            for mop in &entry.op.value {
                let list = match (mop.0.as_str(), mop.1 == key, &mop.2) {
                    ("r", true, MopVal::List(list)) => list,
                    _ => continue,
                };
                if list.contains(&value) {
                    continue;
                }
                let displaced_by = appended
                    .iter()
                    .filter(|(k, v, at, _)| *k == key && *at > committed_at && list.contains(v))
                    .min_by_key(|(_, _, at, _)| *at);
                let blame = match displaced_by {
                    Some((_, v, at, idx)) => format!(
                        "; append {} on the same key committed later at t={} (index {}) \
                         and is present, so its read-modify-write started from a state \
                         that predates value {}",
                        v, at, idx, value
                    ),
                    None => String::new(),
                };
                witnesses.push(format!(
                    "lost update: append {} to key {} committed ok at t={} (index {}), \
                     but the read at index {} (invoked t={}) returned {:?} without it{}",
                    value, key, committed_at, index, entry.op.index, entry.invoked, list, blame
                ));
                break;
            }
            if witnesses.len() >= 32 {
                return witnesses;
            }
        }
    }
    witnesses
}

/// A read that returns a version older than one it was obliged to see.
///
/// "Older" is claimed only when real time proves it: the newer write's
/// transaction was invoked after the observed write's transaction
/// completed, so it cannot have committed first, and it completed before
/// the read's transaction was invoked, so its commit was visible. The
/// order two overlapping transactions record their completions in says
/// nothing about their commit order, since a client can be descheduled
/// between its commit returning and its completion being recorded;
/// comparing completion times alone reports a correct read of the newer
/// version as stale.
fn stale_reads(committed: &[Completed]) -> Vec<String> {
    let mut writes: HashMap<i64, Vec<(i64, u64, u64, u64)>> = HashMap::new();
    for entry in committed {
        for mop in &entry.op.value {
            if let ("w", MopVal::Int(v)) = (mop.0.as_str(), &mop.2) {
                writes.entry(mop.1).or_default().push((
                    *v,
                    entry.invoked,
                    entry.op.time,
                    entry.op.index,
                ));
            }
        }
    }

    let mut witnesses = Vec::new();
    for entry in committed {
        for mop in &entry.op.value {
            if mop.0 != "r" {
                continue;
            }
            let key_writes = match writes.get(&mop.1) {
                Some(w) => w,
                None => continue,
            };
            // `None`: the read saw no version, so every visible write is newer.
            let observed_at = match &mop.2 {
                MopVal::Null => None,
                MopVal::Int(v) => match key_writes.iter().find(|(w, _, _, _)| w == v) {
                    Some((_, _, at, _)) => Some(*at),
                    None => continue,
                },
                MopVal::List(_) => continue,
            };
            let newer = key_writes
                .iter()
                .filter(|(_, invoked, at, _)| {
                    observed_at.is_none_or(|observed| *invoked > observed) && *at < entry.invoked
                })
                .max_by_key(|(_, _, at, _)| *at);
            if let Some((w, invoked, at, idx)) = newer {
                witnesses.push(format!(
                    "stale read: index {} (invoked t={}) read key {} as {:?}, but write {} \
                     to that key (invoked t={}, committed ok at t={}, index {}) is newer and \
                     committed before the read was invoked",
                    entry.op.index, entry.invoked, mop.1, mop.2, w, invoked, at, idx
                ));
                if witnesses.len() >= 32 {
                    return witnesses;
                }
            }
        }
    }
    witnesses
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::history::Mop;

    fn txn(index: u64, invoked: u64, completed: u64, value: Vec<Mop>) -> Completed {
        let mut op = Op::new(OpKind::Ok, index, completed, value);
        op.index = index;
        Completed { op, invoked }
    }

    fn write(key: i64, value: i64) -> Mop {
        Mop("w".into(), key, MopVal::Int(value))
    }

    fn read(key: i64, value: Option<i64>) -> Mop {
        Mop("r".into(), key, value.map_or(MopVal::Null, MopVal::Int))
    }

    #[test]
    fn a_read_older_than_a_write_that_began_after_it_committed_is_stale() {
        let history = [
            txn(0, 10, 20, vec![write(0, 1)]),
            txn(1, 30, 40, vec![write(0, 2)]),
            txn(2, 50, 60, vec![read(0, Some(1))]),
        ];
        let witnesses = stale_reads(&history);
        assert_eq!(witnesses.len(), 1, "{witnesses:?}");
        assert!(
            witnesses[0].contains("read key 0 as Int(1), but write 2"),
            "{}",
            witnesses[0]
        );
    }

    #[test]
    fn overlapping_writes_have_no_real_time_order_so_either_read_is_legal() {
        // Write 1's transaction commits first but its client records the
        // completion late (t=40); write 2's overlapping transaction commits
        // second and records t=30. Reading 2 afterwards is the correct
        // newest value, and reading 1 would be too had 1 committed last.
        let history = [
            txn(0, 10, 40, vec![write(0, 1)]),
            txn(1, 15, 30, vec![write(0, 2)]),
            txn(2, 50, 60, vec![read(0, Some(2))]),
            txn(3, 50, 60, vec![read(0, Some(1))]),
        ];
        assert_eq!(stale_reads(&history), Vec::<String>::new());
    }

    #[test]
    fn a_read_of_nothing_after_a_committed_write_is_stale() {
        let history = [
            txn(0, 10, 20, vec![write(3, 7)]),
            txn(1, 30, 40, vec![read(3, None)]),
        ];
        let witnesses = stale_reads(&history);
        assert_eq!(witnesses.len(), 1, "{witnesses:?}");
        assert!(
            witnesses[0].contains("read key 3 as Null, but write 7"),
            "{}",
            witnesses[0]
        );
    }
}
