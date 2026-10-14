//! What a queue keeps landed for calls run again: a call that needs more
//! than the queue's bound at once holds its blocks until it is seen again,
//! lets them go when it finishes, and a call abandoned after a wait lets
//! them go after `KEEP_ROUNDS` landing polls.

use super::KEEP_ROUNDS;
use crate::{CompressionType, Db, Error, IoBudget, IoQueue, Options, ReadMode, WouldBlock};

/// Two MiB: one value fills a data block, twice the queue's 1 MiB bound.
const BIG: usize = 2 << 20;

/// 4 KiB blocks (a 1 MiB bound), no block cache, no compression: a read run
/// again finds its blocks only where they landed for its queue.
fn big_values(keys: &[&[u8]]) -> (tempfile::TempDir, Db) {
    let dir = tempfile::TempDir::new().unwrap();
    let db = Db::open(
        dir.path(),
        Options::default()
            .block_size(4096)
            .block_cache_size(0)
            .compression(CompressionType::None),
    )
    .unwrap();
    for (i, key) in keys.iter().enumerate() {
        db.put(key, &vec![i as u8; BIG]).unwrap();
    }
    db.flush().unwrap();
    (dir, db)
}

fn waits<T: std::fmt::Debug>(read: crate::Result<T>) -> bool {
    match read {
        Err(Error::WouldBlock(WouldBlock::Io(_))) => true,
        Ok(_) => false,
        other => panic!("{other:?}"),
    }
}

/// Run `get(key)` through `queue` until it answers.
fn get_through(db: &Db, queue: &mut IoQueue, key: &[u8]) {
    let snapshot = db
        .snapshot()
        .with_read_mode(ReadMode::CacheOnly(queue.id()));
    for _ in 0..8 {
        if !waits(snapshot.get(key)) {
            return;
        }
        queue.poll(IoBudget::ALL);
    }
    panic!("the read never finished");
}

#[test]
fn a_call_past_the_bound_holds_its_blocks_until_it_finishes() {
    let (_dir, db) = big_values(&[b"a", b"b", b"c"]);
    let mut queue = db.io_queue();
    let snapshot = db
        .snapshot()
        .with_read_mode(ReadMode::CacheOnly(queue.id()));
    // a misses; then a is read and b misses: the wait holds a.
    assert!(waits(snapshot.multi_get(&[b"a", b"b"])));
    queue.poll(IoBudget::ALL);
    let a = queue.landed_keys()[0];
    assert!(waits(snapshot.multi_get(&[b"a", b"b"])));
    queue.poll(IoBudget::ALL);
    // Both landed and held, past the bound.
    let landed = queue.landed_keys();
    assert_eq!(landed.len(), 2);
    let b = landed[1];
    assert!(queue.holds(&a) && queue.holds(&b));
    assert!(queue.landed_bytes() > 2 * BIG - 1);
    // The run that reads both finishes, and says so.
    assert!(!waits(snapshot.multi_get(&[b"a", b"b"])));
    queue.poll(IoBudget::ALL);
    assert!(!queue.holds(&a) && !queue.holds(&b));
    // The next landing lets both go: nothing holds them past the bound.
    get_through(&db, &mut queue, b"c");
    let landed = queue.landed_keys();
    assert!(!landed.contains(&a) && !landed.contains(&b), "{landed:?}");
    assert_eq!(landed.len(), 1);
}

#[test]
fn a_call_never_run_again_lets_go_after_its_rounds() {
    let (_dir, db) = big_values(&[b"a", b"c0", b"c1", b"c2", b"c3", b"c4", b"c5"]);
    let mut queue = db.io_queue();
    let snapshot = db
        .snapshot()
        .with_read_mode(ReadMode::CacheOnly(queue.id()));
    assert!(waits(snapshot.get(b"a")));
    queue.poll(IoBudget::ALL);
    let a = queue.landed_keys()[0];
    // The call is never run again. Each read below lands in a poll of its
    // own: a round each.
    let mut rounds = 0;
    for key in [b"c0", b"c1", b"c2", b"c3", b"c4", b"c5"] {
        get_through(&db, &mut queue, key);
        rounds += 1;
        let kept = queue.landed_keys().contains(&a);
        if rounds < KEEP_ROUNDS {
            assert!(kept, "a was let go after {rounds} rounds");
        }
    }
    assert!(rounds > KEEP_ROUNDS);
    assert!(!queue.holds(&a));
    assert!(!queue.landed_keys().contains(&a));
}
