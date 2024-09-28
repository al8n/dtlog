use core::iter::FusedIterator;

use dbutils::traits::TypeRef;
use rarena_allocator::Allocator;

use super::{DiscardLog, Fid, DISCARD_LEN_SIZE};

/// An iterator over the entries of the discard log.
pub struct Iter<'a, I> {
  log: &'a DiscardLog<I>,
  idx: usize,
}

impl<'a, I> Iter<'a, I> {
  #[inline]
  pub(super) const fn new(log: &'a DiscardLog<I>) -> Self {
    Self { log, idx: 0 }
  }
}

impl<'a, I> Iterator for Iter<'a, I>
where
  I: Fid,
{
  type Item = (I::Ref<'a>, u64);

  fn next(&mut self) -> Option<Self::Item> {
    if self.idx < self.log.len {
      let entry_size = I::ENCODED_LEN + DISCARD_LEN_SIZE;
      let data = self.log.arena.data();
      let offset = self.idx * entry_size;
      let fid =
        unsafe { <I::Ref<'_> as TypeRef>::from_slice(&data[offset..offset + I::ENCODED_LEN]) };
      let discard = u64::from_be_bytes(
        (&data[offset + I::ENCODED_LEN..offset + I::ENCODED_LEN + DISCARD_LEN_SIZE])
          .try_into()
          .unwrap(),
      );

      self.idx += 1;

      Some((fid, discard))
    } else {
      None
    }
  }

  #[inline]
  fn nth(&mut self, n: usize) -> Option<Self::Item> {
    let remaining = self.log.len - self.idx;
    if n < remaining {
      self.idx += n;
      self.next()
    } else {
      self.idx = self.log.len;
      None
    }
  }

  #[inline]
  fn count(self) -> usize
  where
    Self: Sized,
  {
    self.log.len - self.idx
  }

  #[inline]
  fn size_hint(&self) -> (usize, Option<usize>) {
    let remaining = self.log.len - self.idx;
    (remaining, Some(remaining))
  }
}

impl<I> ExactSizeIterator for Iter<'_, I> where I: Fid {}

impl<I> FusedIterator for Iter<'_, I> where I: Fid {}
