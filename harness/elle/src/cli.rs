//! Command-line surface for the generator.

use std::path::PathBuf;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Model {
    ListAppend,
    RwRegister,
}

impl Model {
    pub fn as_str(self) -> &'static str {
        match self {
            Model::ListAppend => "list-append",
            Model::RwRegister => "rw-register",
        }
    }
}

/// Requested isolation level, each an engine level of its own.
///
/// `read-committed` runs the pessimistic flavour, opened at regolith's
/// `ReadCommitted` level so the level the harness claims is the one the
/// engine runs; the other four run the optimistic flavour at the regolith
/// level of the same name. `defra-level` has no key classifier in the `point`
/// shape: there the workloads are point operations, so it validates point
/// reads exactly as `repeatable-read` does, and it differs only in appending
/// to a list by blind merge. The other shapes install one ([`Shape`]). Each
/// is checked against the Elle model it claims; README.md carries the table.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Isolation {
    ReadCommitted,
    Snapshot,
    RepeatableRead,
    Serializable,
    DefraLevel,
}

impl Isolation {
    pub fn as_str(self) -> &'static str {
        match self {
            Isolation::ReadCommitted => "read-committed",
            Isolation::Snapshot => "snapshot-isolation",
            Isolation::RepeatableRead => "repeatable-read",
            Isolation::Serializable => "serializable",
            Isolation::DefraLevel => "defra-level",
        }
    }
}

/// What the transactions of a run do beside or in place of the point
/// operations: the `DefraLevel` mechanisms the Elle models can record.
///
/// Every shape but `point` installs a key classifier when it runs at
/// `defra-level`. README.md says what each records and why its history must
/// hold the model it is checked against.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Shape {
    /// Point reads and writes only, with no classifier: the workload every
    /// level runs.
    Point,
    /// The point workload under a classifier, with every transaction also
    /// storing a content-addressed block, adding a key of its own to a
    /// commutative prefix it scans, and appending to a log.
    Classified,
    /// `list-append` where a key is a commit-ordered log: an append is
    /// `Transaction::append`, and a read is the log read in one snapshot.
    /// A transaction appends or reads, never both.
    Appends,
    /// `list-append` where a key is one part of a document: an append is an
    /// operand on the part, and a read is `get_parts` naming it.
    Parts,
    /// Every read is one validated scan of the whole key prefix, recorded
    /// as a read of every key.
    Scan,
}

impl Shape {
    pub fn as_str(self) -> &'static str {
        match self {
            Shape::Point => "point",
            Shape::Classified => "classified",
            Shape::Appends => "appends",
            Shape::Parts => "parts",
            Shape::Scan => "scan",
        }
    }

    /// The one model a shape records, when it can record only one.
    pub fn model(self) -> Option<Model> {
        match self {
            Shape::Appends | Shape::Parts => Some(Model::ListAppend),
            Shape::Point | Shape::Classified | Shape::Scan => None,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Fault {
    Kill,
    TornWrite,
    TruncateWal,
}

/// Child-process role. The parent re-executes itself to get a process
/// it can kill or crash without taking its own history down with it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum WorkerRole {
    /// Churn until killed from the outside.
    Churn,
    /// Write a bounded batch, then exit without closing the database,
    /// leaving the batch in the write-ahead log only.
    Doomed,
}

pub struct Config {
    pub model: Model,
    pub isolation: Isolation,
    pub shape: Shape,
    pub faults: Vec<Fault>,
    pub dir: PathBuf,
    pub out: PathBuf,
    pub threads: u64,
    pub txns: u64,
    pub keys: i64,
    pub seed: u64,
    pub worker: Option<WorkerRole>,
    pub worker_out: PathBuf,
    pub process_base: u64,
    pub time_base: u64,
    pub value_base: i64,
    pub verify_only: Option<PathBuf>,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            model: Model::ListAppend,
            isolation: Isolation::ReadCommitted,
            shape: Shape::Point,
            faults: Vec::new(),
            dir: PathBuf::from("db"),
            out: PathBuf::from("history.json"),
            threads: 8,
            txns: 50,
            keys: 4,
            seed: 0xA5A5_1234_DEAD_BEEF,
            worker: None,
            worker_out: PathBuf::from("worker.jsonl"),
            process_base: 0,
            time_base: 0,
            value_base: 1,
            verify_only: None,
        }
    }
}

pub const USAGE: &str = "\
elle-gen - generate a Jepsen history from concurrent regolith transactions

Usage: elle-gen [options]

Options:
  --model <list-append|rw-register>   Workload model (default: list-append)
  --isolation <read-committed|snapshot-isolation|repeatable-read|serializable|defra-level>
                                      Requested isolation (default: read-committed)
  --shape <point|classified|appends|parts|scan>
                                      What the transactions do (default: point)
  --faults <kill,torn-write,truncate-wal|all>
                                      Fault injection (default: none)
  --dir <path>                        Database directory (default: db)
  --out <path>                        History output (default: history.json)
  --threads <n>                       Concurrent processes (default: 8)
  --txns <n>                          Transactions per process (default: 50)
  --keys <n>                          Distinct keys (default: 4)
  --seed <n>                          Deterministic workload seed
  --verify <path>                     Analyze an existing history and exit
  --help                              Print this message
";

pub fn parse<I: Iterator<Item = String>>(mut args: I) -> Result<Config, String> {
    let mut cfg = Config::default();

    while let Some(arg) = args.next() {
        let mut value = || {
            args.next()
                .ok_or_else(|| format!("option {} needs a value", arg))
        };
        match arg.as_str() {
            "--model" => {
                cfg.model = match value()?.as_str() {
                    "list-append" => Model::ListAppend,
                    "rw-register" => Model::RwRegister,
                    other => return Err(format!("unknown model {}", other)),
                }
            }
            "--isolation" => {
                cfg.isolation = match value()?.as_str() {
                    "read-committed" => Isolation::ReadCommitted,
                    "snapshot-isolation" => Isolation::Snapshot,
                    "repeatable-read" => Isolation::RepeatableRead,
                    "serializable" => Isolation::Serializable,
                    "defra-level" => Isolation::DefraLevel,
                    other => return Err(format!("unknown isolation level {}", other)),
                }
            }
            "--shape" => {
                cfg.shape = match value()?.as_str() {
                    "point" => Shape::Point,
                    "classified" => Shape::Classified,
                    "appends" => Shape::Appends,
                    "parts" => Shape::Parts,
                    "scan" => Shape::Scan,
                    other => return Err(format!("unknown shape {}", other)),
                }
            }
            "--faults" => cfg.faults = parse_faults(&value()?)?,
            "--dir" => cfg.dir = PathBuf::from(value()?),
            "--out" => cfg.out = PathBuf::from(value()?),
            "--threads" => cfg.threads = parse_num(&value()?, "--threads")?,
            "--txns" => cfg.txns = parse_num(&value()?, "--txns")?,
            "--keys" => cfg.keys = parse_num(&value()?, "--keys")? as i64,
            "--seed" => cfg.seed = parse_num(&value()?, "--seed")?,
            "--verify" => cfg.verify_only = Some(PathBuf::from(value()?)),
            "--worker" => {
                cfg.worker = Some(match value()?.as_str() {
                    "churn" => WorkerRole::Churn,
                    "doomed" => WorkerRole::Doomed,
                    other => return Err(format!("unknown worker role {}", other)),
                })
            }
            "--worker-out" => cfg.worker_out = PathBuf::from(value()?),
            "--process-base" => cfg.process_base = parse_num(&value()?, "--process-base")?,
            "--time-base" => cfg.time_base = parse_num(&value()?, "--time-base")?,
            "--value-base" => cfg.value_base = parse_num(&value()?, "--value-base")? as i64,
            "--help" | "-h" => return Err(USAGE.to_string()),
            other => return Err(format!("unknown option {}\n\n{}", other, USAGE)),
        }
    }

    if cfg.keys < 1 {
        return Err("--keys must be at least 1".to_string());
    }
    if cfg.threads < 1 {
        return Err("--threads must be at least 1".to_string());
    }
    if cfg.shape == Shape::Classified && cfg.isolation != Isolation::DefraLevel {
        return Err(
            "--shape classified needs --isolation defra-level: only that level has a classifier"
                .to_string(),
        );
    }
    if let Some(model) = cfg.shape.model()
        && model != cfg.model
    {
        return Err(format!(
            "--shape {} records a {} history; pass --model {}",
            cfg.shape.as_str(),
            model.as_str(),
            model.as_str()
        ));
    }
    Ok(cfg)
}

fn parse_faults(raw: &str) -> Result<Vec<Fault>, String> {
    if raw == "all" {
        return Ok(vec![Fault::Kill, Fault::TornWrite, Fault::TruncateWal]);
    }
    raw.split(',')
        .filter(|s| !s.is_empty())
        .map(|s| match s {
            "kill" => Ok(Fault::Kill),
            "torn-write" => Ok(Fault::TornWrite),
            "truncate-wal" => Ok(Fault::TruncateWal),
            other => Err(format!("unknown fault {}", other)),
        })
        .collect()
}

fn parse_num(raw: &str, flag: &str) -> Result<u64, String> {
    raw.parse::<u64>()
        .map_err(|_| format!("{} expects a non-negative integer, got {}", flag, raw))
}
