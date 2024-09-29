use core::num::NonZeroU64;

use dtlog::Options;

fn main() {
  let mut log = Options::new().with_capacity(100).map_anon().unwrap();

  for i in 1..=20u32 {
    log
      .increase(&i, NonZeroU64::new((i * 100) as u64).unwrap())
      .unwrap();
  }

  assert_eq!(log.max_discard().unwrap(), (20, 2000));
}
