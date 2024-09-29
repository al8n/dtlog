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
  assert!(iter.next().is_none());

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

  assert!(log.get(&50).is_none());
  assert!(log.clear(&50).is_none());
  assert!(log.decrease(&50, NonZeroU64::new(1).unwrap()).is_none());

  assert_eq!(log.max_discard().unwrap(), (20, 1999));
  assert_eq!(log.len(), 20);

  let mut iter = log.iter();
  let middle = iter.nth(10).unwrap();
  assert_eq!(middle, (11, 1099));
  assert_eq!(iter.size_hint(), (9, Some(9)));
  assert_eq!(iter.count(), 9);
  assert_eq!(log.iter().nth(100), None);

  let mut iter = log.keys();
  let middle = iter.nth(10).unwrap();
  assert_eq!(middle, 11);
  assert_eq!(iter.count(), 9);
  assert_eq!(log.keys().nth(100), None);

  let mut iter = log.values();
  let middle = iter.nth(10).unwrap();
  assert_eq!(middle, 1099);
  assert_eq!(iter.count(), 9);
  assert_eq!(log.values().nth(100), None);

  for i in 1..=20u32 {
    log.clear(&i).unwrap();
  }

  for i in 1..=20u32 {
    log.increase(&i, NonZeroU64::new(1000).unwrap()).unwrap();
  }
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
fn test_discard_log_map_anon_unify() {
  let log = Options::new()
    .with_capacity(100)
    .with_unify(true)
    .map_anon()
    .unwrap();
  basic(log);
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[cfg_attr(miri, ignore)]
fn test_discard_log_map_file() {
  use std::io::{Seek, Write};

  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("DISCARD");

  let log = unsafe {
    Options::new()
      .with_capacity(100)
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut(&p)
      .unwrap()
  };
  basic(log);

  let log = unsafe { Options::new().with_read(true).map::<u32, _>(&p).unwrap() };
  assert!(!log.is_empty());
  assert_eq!(log.len(), 20);
  assert!(log.capacity() > 20);

  for i in 11..=20u32 {
    let discard = log.get(&i).unwrap();
    assert_eq!(discard, 1000);
  }

  assert_eq!(log.max_discard().unwrap(), (20, 1000));

  let mut iter = log.iter();
  let middle = iter.nth(10).unwrap();
  assert_eq!(middle, (11, 1000));
  assert_eq!(iter.size_hint(), (9, Some(9)));
  assert!(iter.nth(100).is_none());
  assert!(iter.next().is_none());

  let mut iter = log.keys();
  let middle = iter.nth(10).unwrap();
  assert_eq!(middle, 11);
  assert!(iter.nth(100).is_none());
  assert!(iter.next().is_none());

  let mut iter = log.values();
  let middle = iter.nth(10).unwrap();
  assert_eq!(middle, 1000);
  assert!(iter.nth(100).is_none());
  assert!(iter.next().is_none());

  drop(log);

  // reopen mut
  let mut log = unsafe {
    Options::new()
      .with_read(true)
      .with_write(true)
      .map_mut::<u32, _>(&p)
      .unwrap()
  };

  log.increase(&21, NonZeroU64::new(2100).unwrap()).unwrap();
  assert_eq!(log.get(&21).unwrap(), 2100);
  assert_eq!(log.max_discard().unwrap(), (21, 2100));

  drop(log);

  // Add some random trailing bytes
  {
    let mut file = std::fs::OpenOptions::new()
      .read(true)
      .write(true)
      .open(&p)
      .unwrap();
    file.seek(std::io::SeekFrom::End(0)).unwrap();
    file.write_all(&[1, 1, 1]).unwrap();
    file.sync_all().unwrap();
  }

  let mut log = unsafe {
    Options::new()
      .with_read(true)
      .with_write(true)
      .map_mut::<u32, _>(&p)
      .unwrap()
  };

  log.increase(&21, NonZeroU64::new(2100).unwrap()).unwrap();
  assert_eq!(log.get(&21).unwrap(), 4200);
  assert_eq!(log.max_discard().unwrap(), (21, 4200));
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[cfg_attr(miri, ignore)]
fn test_discard_log_bad_magic_text() {
  use std::io::Write;

  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("bad_magic.DISCARD");

  let log = unsafe {
    Options::new()
      .with_capacity(100)
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut::<u32, _>(&p)
      .unwrap()
  };

  drop(log);

  // Add some random trailing bytes
  {
    let mut file = std::fs::OpenOptions::new()
      .read(true)
      .write(true)
      .open(&p)
      .unwrap();
    file.write_all(&[1, 1, 1]).unwrap();
    file.sync_all().unwrap();
  }

  let err = unsafe {
    Options::new()
      .with_read(true)
      .with_write(true)
      .map_mut::<u32, _>(&p)
      .unwrap_err()
  };

  assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
  assert!(err.to_string().contains("bad magic text"));
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[cfg_attr(miri, ignore)]
fn test_discard_log_bad_magic_version() {
  use std::io::{Seek, SeekFrom, Write};

  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("bad_magic_version.DISCARD");

  let log = unsafe {
    Options::new()
      .with_capacity(100)
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut::<u32, _>(&p)
      .unwrap()
  };

  drop(log);

  // Add some random trailing bytes
  {
    let mut file = std::fs::OpenOptions::new()
      .read(true)
      .write(true)
      .open(&p)
      .unwrap();
    file.seek(SeekFrom::Start(MAGIC_TEXT_SIZE as u64)).unwrap();
    file.write_all(&[1, 1]).unwrap();
    file.sync_all().unwrap();
  }

  let err = unsafe {
    Options::new()
      .with_read(true)
      .with_write(true)
      .map_mut::<u32, _>(&p)
      .unwrap_err()
  };

  assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
  assert!(err.to_string().contains("bad magic version"), "{err}");
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[cfg_attr(miri, ignore)]
fn test_discard_log_bad_version() {
  use std::io::{Seek, SeekFrom, Write};

  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("bad_version.DISCARD");

  let log = unsafe {
    Options::new()
      .with_capacity(100)
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut::<u32, _>(&p)
      .unwrap()
  };

  drop(log);

  // Add some random trailing bytes
  {
    let mut file = std::fs::OpenOptions::new()
      .read(true)
      .write(true)
      .open(&p)
      .unwrap();
    file
      .seek(SeekFrom::Start(MAGIC_TEXT_SIZE as u64 + 6))
      .unwrap(); // 4 is the offset of the magic version of arena
    file.write_all(&[1, 1]).unwrap();
    file.sync_all().unwrap();
  }

  let err = unsafe {
    Options::new()
      .with_read(true)
      .with_write(true)
      .map_mut::<u32, _>(&p)
      .unwrap_err()
  };

  assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
  assert!(err.to_string().contains("bad version"), "{err}");
}

#[test]
fn test_insufficient_space_vec() {
  let err = Options::new().alloc::<u32>().unwrap_err();
  assert!(matches!(err, crate::error::Error::InsufficientSpace { .. }));
}

#[test]
fn test_insufficient_space_map_anon() {
  let err = Options::new().with_capacity(1).alloc::<u32>().unwrap_err();
  assert!(err.to_string().contains("insufficient space"));
}
