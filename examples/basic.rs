use std::num::NonZeroU64;

use dtlog::Options;

fn main() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("DISCARD");

  let mut log = unsafe {
    Options::new()
      .with_capacity(100)
      .with_unify(true)
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut(&p)
      .unwrap()
  };

  for i in 1..=20u32 {
    log
      .increase(&i, NonZeroU64::new((i * 100) as u64).unwrap())
      .unwrap();
  }

  let log = unsafe { Options::new().with_read(true).map::<u32, _>(&p).unwrap() };

  for i in 1..=20u32 {
    let discard = log.get(&i).unwrap();
    assert_eq!(discard, (i * 100) as u64);
  }

  assert_eq!(log.max_discard().unwrap(), (20, 2000));
}
