use std::io;

use super::internal_key;
use super::memtable::MemTable;
use super::wal::{self, Wal};

const GROUP_BYTES: usize = 64 * 1024;

pub(super) fn rewrite_recovered_memtable_to_wal(
    memtable: &MemTable,
    wal: &mut Wal,
) -> io::Result<()> {
    let mut groups = RecoveryGroups::new(wal);
    memtable.try_for_each_entry(|internal_key, value| {
        let (user_key, seq, value_type) = internal_key::decode_internal_key(internal_key);
        match value_type {
            internal_key::VALUE_TYPE_VALUE => groups
                .record(wal::put_record_len(user_key, value), |out| {
                    wal::encode_put_record(out, user_key, value, seq)
                }),
            internal_key::VALUE_TYPE_DELETION => groups
                .record(wal::delete_record_len(user_key), |out| {
                    wal::encode_delete_record(out, user_key, seq)
                }),
            internal_key::VALUE_TYPE_MERGE => groups
                .record(wal::merge_record_len(user_key, value), |out| {
                    wal::encode_merge_record(out, user_key, value, seq)
                }),
            other => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("unknown value type {other} in recovered memtable"),
            )),
        }
    })?;

    for tombstone in memtable.clone_range_tombstones() {
        groups.record(
            wal::delete_range_record_len(&tombstone.start, &tombstone.end),
            |out| {
                wal::encode_delete_range_record(
                    out,
                    &tombstone.start,
                    &tombstone.end,
                    tombstone.seq,
                )
            },
        )?;
    }
    groups.finish()
}

struct RecoveryGroups<'a> {
    wal: &'a mut Wal,
    buffer: Vec<u8>,
    wrote_record: bool,
}

impl<'a> RecoveryGroups<'a> {
    fn new(wal: &'a mut Wal) -> Self {
        Self {
            wal,
            buffer: Vec::with_capacity(GROUP_BYTES),
            wrote_record: false,
        }
    }

    fn record(&mut self, len: usize, encode: impl FnOnce(&mut Vec<u8>)) -> io::Result<()> {
        if len > GROUP_BYTES {
            self.flush()?;
            // Keep a large record separate so the reusable group stays bounded.
            let mut record = Vec::with_capacity(len);
            encode(&mut record);
            self.wal.append_group(&record)?;
        } else {
            if len > GROUP_BYTES - self.buffer.len() {
                self.flush()?;
            }
            encode(&mut self.buffer);
        }
        self.wrote_record = true;
        Ok(())
    }

    fn flush(&mut self) -> io::Result<()> {
        if !self.buffer.is_empty() {
            self.wal.append_group(&self.buffer)?;
            self.buffer.clear();
        }
        Ok(())
    }

    fn finish(mut self) -> io::Result<()> {
        if self.wrote_record {
            self.flush()?;
            // The caller retains old WALs until the entire replacement is durable.
            self.wal.sync_data()?;
        }
        Ok(())
    }
}
