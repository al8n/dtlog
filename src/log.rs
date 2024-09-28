use core::{cmp, iter::FusedIterator, marker::PhantomData, num::NonZeroU64};

pub use dbutils::{
  equivalent::{Comparable, Equivalent},
  traits::{Type, TypeRef},
};
use indexsort::{search, IndexSort};
use rarena_allocator::{either::Either, unsync::Arena, Allocator, Buffer, Error as ArenaError};

const DISCARD_LEN_SIZE: usize = 8;

/// Options for the discard log.
pub struct Options {
  sync: bool,
}

/// An abstraction of file id.
pub trait Fid: Type {
  /// The fixed encoded length of the fid.
  const ENCODED_LEN: usize;
}

macro_rules! impl_fid {
  ($($t:ty), +$(,)?) => {
    $(
      impl Fid for $t {
        const ENCODED_LEN: usize = core::mem::size_of::<$t>();
      }
    )*
  };
}

impl_fid!(u16, u32, u64, u128);

/// A discard log that stores the discard stats for each file id.
pub struct DiscardLog<I> {
  arena: Arena,
  next_empty_slot: usize,
  opts: Options,
  capacity: usize,
  _marker: PhantomData<I>,
}

impl<I> IndexSort for DiscardLog<I>
where
  I: Fid,
  for<'a> I::Ref<'a>: Ord,
{
  #[inline]
  fn len(&self) -> usize {
    self.next_empty_slot
  }

  #[inline]
  fn less(&self, i: usize, j: usize) -> bool {
    let data = self.data();
    let entry_size = I::ENCODED_LEN + DISCARD_LEN_SIZE;

    let ioffset = i * entry_size;
    let joffset = j * entry_size;

    unsafe {
      let fid1 = <I::Ref<'_> as TypeRef>::from_slice(&data[ioffset..ioffset + I::ENCODED_LEN]);
      let fid2 = <I::Ref<'_> as TypeRef>::from_slice(&data[joffset..joffset + I::ENCODED_LEN]);
      fid1.le(&fid2)
    }
  }

  #[inline]
  fn swap(&mut self, i: usize, j: usize) {
    let entry_size = I::ENCODED_LEN + DISCARD_LEN_SIZE;

    let ioffset = i * entry_size;
    let joffset = j * entry_size;

    unsafe {
      let data_offset = self.arena.data_offset();
      let left = self.arena.get_bytes_mut(data_offset + ioffset, entry_size);
      let right = self.arena.get_bytes_mut(data_offset + joffset, entry_size);
      left.swap_with_slice(right);
    }
  }
}

impl<I> DiscardLog<I> {
  /// Returns the capacity of the discard log.
  ///
  /// The capacity is the maximum number of entries that can be stored in the discard log.
  #[inline]
  pub const fn capacity(&self) -> usize {
    self.capacity
  }

  /// Returns the number of entries in the discard log.
  #[inline]
  pub const fn len(&self) -> usize {
    self.next_empty_slot
  }

  /// Returns `true` if the discard log is empty.
  #[inline]
  pub const fn is_empty(&self) -> bool {
    self.next_empty_slot == 0
  }

  #[inline]
  fn data(&self) -> &[u8] {
    self.arena.data()
  }

  #[inline]
  fn truncate(&mut self) {
    todo!()
  }
}

impl<I> DiscardLog<I>
where
  I: Fid,
{
  /// Returns an iterator over the entries of the discard log.
  #[inline]
  pub const fn iter(&self) -> Iter<'_, I> {
    Iter { log: self, idx: 0 }
  }

  /// Returns the maximum number of discarded bytes and the file id that contains the maximum discard value.
  ///
  /// If the discard log is empty, it would return `None`.
  #[inline]
  pub fn max_discard(&self) -> Option<(I::Ref<'_>, u64)> {
    self.iter().max_by(|(_, a), (_, b)| a.cmp(b))
  }
}

impl<I> DiscardLog<I>
where
  I: Fid,
  for<'a> I::Ref<'a>: Ord,
{
  /// Returns the discarded bytes for the given file id.
  #[inline]
  pub fn get<Q>(&self, fid: &Q) -> Option<u64>
  where
    Q: ?Sized + for<'a> Comparable<I::Ref<'a>>,
  {
    let entry_size = I::ENCODED_LEN + DISCARD_LEN_SIZE;
    let data = self.arena.data();
    let (eq, idx) = self.search(fid);

    if idx < self.next_empty_slot && eq {
      let off = idx * entry_size + I::ENCODED_LEN;
      let cur_disc = u64::from_be_bytes((&data[off..off + DISCARD_LEN_SIZE]).try_into().unwrap());

      return Some(cur_disc);
    }

    // Could not find the fid
    None
  }

  /// Increases the discard stats for the given file id. Returns the old value of discard for the file id. If such file id does not exist, it would add the entry.
  ///
  /// ## Panics
  /// - If the currrent discard value plus the discard value is greater than `u64::MAX`, then it would panic because of overflow.
  pub fn increase(
    &mut self,
    fid: &I,
    discard: NonZeroU64,
  ) -> Result<u64, Either<I::Error, ArenaError>>
  where
    I: for<'a> Comparable<I::Ref<'a>>,
  {
    let entry_size = I::ENCODED_LEN + DISCARD_LEN_SIZE;
    let data = self.arena.data();
    let data_offset = self.arena.data_offset();
    let (eq, idx) = self.search(fid);

    if idx < self.next_empty_slot && eq {
      let off = idx * entry_size + I::ENCODED_LEN;
      let cur_disc = u64::from_be_bytes((&data[off..off + DISCARD_LEN_SIZE]).try_into().unwrap());

      unsafe {
        let buf = self
          .arena
          .get_bytes_mut(data_offset + off, DISCARD_LEN_SIZE);
        let new_discard = discard.get() + cur_disc;
        buf.copy_from_slice(&(new_discard).to_be_bytes());
      }

      return Ok(cur_disc);
    }

    // Could not find the fid, add the entry.

    // Check if there is enough space in the arena, if not increase the size of the arena.
    while self.arena.remaining() < entry_size {
      self.truncate();
    }

    let discard = discard.get();
    unsafe {
      let mut buf = self
        .arena
        .alloc_bytes(entry_size as u32)
        .map_err(Either::Right)?;
      buf.set_len(I::ENCODED_LEN);
      fid.encode(&mut buf).map_err(Either::Left)?;
      buf.put_u64_be_unchecked(discard);
      buf.detach();
    };

    // Move to next slot
    self.next_empty_slot += 1;

    IndexSort::sort(self);

    if self.opts.sync {
      // TODO: error handle
      self.arena.flush().unwrap();
    }

    Ok(0)
  }

  /// Decreases the discard stats for the given file id. Returns the old value of discard for the file if such fid exist in discard log.
  /// Otherwise, it would return `None`.
  ///
  /// ## Panics
  /// - If the discard value is greater than the current discard value, subtracting the discard value would result in overflow.
  pub fn decrease<Q>(&mut self, fid: &Q, discard: NonZeroU64) -> Option<u64>
  where
    Q: ?Sized + for<'a> Comparable<I::Ref<'a>>,
  {
    let entry_size = I::ENCODED_LEN + DISCARD_LEN_SIZE;
    let data = self.arena.data();
    let data_offset = self.arena.data_offset();
    let (eq, idx) = self.search(fid);

    if idx < self.next_empty_slot && eq {
      let off = idx * entry_size + I::ENCODED_LEN;
      let cur_disc = u64::from_be_bytes((&data[off..off + DISCARD_LEN_SIZE]).try_into().unwrap());

      unsafe {
        let buf = self
          .arena
          .get_bytes_mut(data_offset + off, DISCARD_LEN_SIZE);
        let new_discard = discard.get() - cur_disc;
        buf.copy_from_slice(&(new_discard).to_be_bytes());
      }

      return Some(cur_disc);
    }

    // Could not find the fid
    None
  }

  /// Clear the discard stats for the given file id. It would return the
  /// old value of discard for the file id if such file id exist in the discard log.
  ///
  /// If the file id does not exist in the discard log, it would return `None`.
  ///
  /// **Note:** This is not remove semantics, it just clears the discard value for the file id.
  pub fn clear<Q>(&mut self, fid: &Q) -> Option<u64>
  where
    Q: ?Sized + for<'a> Comparable<I::Ref<'a>>,
  {
    let entry_size = I::ENCODED_LEN + DISCARD_LEN_SIZE;
    let data = self.arena.data();
    let data_offset = self.arena.data_offset();
    let (eq, idx) = self.search(fid);

    if idx < self.next_empty_slot && eq {
      let off = idx * entry_size + I::ENCODED_LEN;
      let cur_disc = u64::from_be_bytes((&data[off..off + DISCARD_LEN_SIZE]).try_into().unwrap());

      unsafe {
        let buf = self
          .arena
          .get_bytes_mut(data_offset + off, DISCARD_LEN_SIZE);
        buf.fill(0);
      }

      return Some(cur_disc);
    }

    // Could not find the fid
    None
  }

  #[inline]
  fn search<Q>(&self, fid: &Q) -> (bool, usize)
  where
    Q: ?Sized + for<'a> Comparable<I::Ref<'a>>,
  {
    let entry_size = I::ENCODED_LEN + DISCARD_LEN_SIZE;
    let mut eq = false;
    let data = self.data();
    let idx = search(self.next_empty_slot, |slot| {
      let offset = slot * entry_size;

      unsafe {
        let fid_ref = <I::Ref<'_> as TypeRef>::from_slice(&data[offset..offset + I::ENCODED_LEN]);

        match fid.compare(&fid_ref) {
          cmp::Ordering::Less => true,
          cmp::Ordering::Equal => {
            eq = true;
            true
          }
          cmp::Ordering::Greater => false,
        }
      }
    });
    (eq, idx)
  }
}

/// An iterator over the entries of the discard log.
pub struct Iter<'a, I> {
  log: &'a DiscardLog<I>,
  idx: usize,
}

impl<'a, I> Iterator for Iter<'a, I>
where
  I: Fid,
{
  type Item = (I::Ref<'a>, u64);

  fn next(&mut self) -> Option<Self::Item> {
    if self.idx < self.log.next_empty_slot {
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
    let remaining = self.log.next_empty_slot - self.idx;
    if n < remaining {
      self.idx += n;
      self.next()
    } else {
      self.idx = self.log.next_empty_slot;
      None
    }
  }

  #[inline]
  fn count(self) -> usize
  where
    Self: Sized,
  {
    self.log.next_empty_slot - self.idx
  }

  #[inline]
  fn size_hint(&self) -> (usize, Option<usize>) {
    let remaining = self.log.next_empty_slot - self.idx;
    (remaining, Some(remaining))
  }
}

impl<I> ExactSizeIterator for Iter<'_, I> where I: Fid {}

impl<I> FusedIterator for Iter<'_, I> where I: Fid {}
