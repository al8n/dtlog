use core::num::NonZeroU64;

use super::*;

fn basic(mut log: DiscardLog) {
  assert!(log.is_empty());
  for i in 1..=20u32 {
    log
      .increase(&i, NonZeroU64::new((i * 100) as u64).unwrap())
      .unwrap();
  }

  let mut iter = log.iter();
  for i in 1..=20u32 {
    let (fid, discard) = iter.next().unwrap();
    assert_eq!(fid, i);
    assert_eq!(discard, (i * 100) as u64);
  }

  let mut keys = log.keys();
  assert_eq!(keys.size_hint(), (20, Some(20)));
  for i in 1..=20u32 {
    let fid = keys.next().unwrap();
    assert_eq!(fid, i);
  }

  let mut values = log.values();
  assert_eq!(values.size_hint(), (20, Some(20)));
  for i in 1..=20u32 {
    let discard = values.next().unwrap();
    assert_eq!(discard, (i * 100) as u64);
  }

  for i in 1..=10u32 {
    log.decrease(&i, NonZeroU64::new(1).unwrap()).unwrap();
  }

  let mut iter = log.iter();
  for i in 1..=10u32 {
    let (fid, discard) = iter.next().unwrap();
    assert_eq!(fid, i);
    assert_eq!(discard, (i * 100 - 1) as u64);

    let discard = log.get(&i).unwrap();
    assert_eq!(discard, (i * 100 - 1) as u64);
  }

  for i in 11..=20u32 {
    log.decrease(&i, NonZeroU64::new(1).unwrap()).unwrap();

    let discard = log.get(&i).unwrap();
    assert_eq!(discard, (i * 100 - 1) as u64);
  }

  assert_eq!(log.max_discard().unwrap(), (20, 1999));
  assert_eq!(log.len(), 20);

  let mut iter = log.iter();
  let middle = iter.nth(10).unwrap();
  assert_eq!(middle, (11, 1099));
  assert_eq!(iter.size_hint(), (9, Some(9)));
  assert_eq!(iter.count(), 9);

  let mut iter = log.keys();
  let middle = iter.nth(10).unwrap();
  assert_eq!(middle, 11);
  assert_eq!(iter.count(), 9);

  let mut iter = log.values();
  let middle = iter.nth(10).unwrap();
  assert_eq!(middle, 1099);
  assert_eq!(iter.count(), 9);
}

#[test]
fn test_discard_log_vec() {
  let log = Options::new().with_capacity(100).alloc().unwrap();
  basic(log);
}

#[test]
fn test_discard_log_vec_unify() {
  let log = Options::new()
    .with_capacity(100)
    .with_unify(true)
    .alloc()
    .unwrap();
  basic(log);
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn test_discard_log_map_anon() {
  let log = Options::new().with_capacity(100).map_anon().unwrap();
  basic(log);
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[cfg_attr(miri, ignore)]
fn test_discard_log_map_file() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("DISCARD");

  let log = unsafe {
    Options::new()
      .with_capacity(100)
      .with_unify(true)
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut(&p)
      .unwrap()
  };
  basic(log);

  let log = unsafe { Options::new().with_read(true).map::<u32, _>(&p).unwrap() };

  for i in 11..=20u32 {
    let discard = log.get(&i).unwrap();
    assert_eq!(discard, (i * 100 - 1) as u64);
  }

  assert_eq!(log.max_discard().unwrap(), (20, 1999));

  let mut iter = log.iter();
  let middle = iter.nth(10).unwrap();
  assert_eq!(middle, (11, 1099));
  assert_eq!(iter.size_hint(), (9, Some(9)));

  let mut iter = log.keys();
  let middle = iter.nth(10).unwrap();
  assert_eq!(middle, 11);
  assert_eq!(iter.count(), 9);

  let mut iter = log.values();
  let middle = iter.nth(10).unwrap();
  assert_eq!(middle, 1099);
  assert_eq!(iter.count(), 9);
}
