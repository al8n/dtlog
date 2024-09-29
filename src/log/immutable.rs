use dbutils::equivalent::Comparable;

use super::{DiscardLog, Fid, Iter, Keys, Values};

/// An immutable discard log that stores the discard stats for each file id.
pub struct ImmutableDiscardLog<I = u32>(DiscardLog<I>);

// Safety: `ImmutableDiscardLog` is immutable, so no data races can occur.
unsafe impl<I: Send> Send for ImmutableDiscardLog<I> {}
unsafe impl<I: Sync> Sync for ImmutableDiscardLog<I> {}

impl<I> ImmutableDiscardLog<I> {
  /// Returns the capacity of the discard log.
  ///
  /// The capacity is the maximum number of entries that can be stored in the discard log.
  #[inline]
  pub const fn capacity(&self) -> usize {
    self.0.capacity()
  }

  /// Returns the number of entries in the discard log.
  #[inline]
  pub const fn len(&self) -> usize {
    self.0.len()
  }

  /// Returns `true` if the discard log is empty.
  #[inline]
  pub const fn is_empty(&self) -> bool {
    self.0.is_empty()
  }

  #[inline]
  pub(crate) const fn construct(log: DiscardLog<I>) -> Self {
    Self(log)
  }
}

impl<I> ImmutableDiscardLog<I>
where
  I: Fid,
{
  /// Returns an iterator over the entries of the discard log.
  ///
  /// See also [`values`] and [`keys`].
  #[inline]
  pub const fn iter(&self) -> Iter<'_, I> {
    self.0.iter()
  }

  /// Returns an iterator over the fid of the discard log.
  ///
  /// The iterator returned by this function is faster than the [`iter`] iterator because it does not need to decode the discard value.
  #[inline]
  pub const fn keys(&self) -> Keys<'_, I> {
    self.0.keys()
  }

  /// Returns an iterator over the discard values of the discard log.
  ///
  /// The iterator returned by this function is faster than the [`iter`] iterator because it does not need to decode the file id.
  #[inline]
  pub const fn values(&self) -> Values<'_, I> {
    self.0.values()
  }

  /// Returns the maximum number of discarded bytes and the file id that contains the maximum discard value.
  ///
  /// If the discard log is empty, it would return `None`.
  #[inline]
  pub fn max_discard(&self) -> Option<(I::Ref<'_>, u64)> {
    self.iter().max_by(|(_, a), (_, b)| a.cmp(b))
  }
}

impl<I> ImmutableDiscardLog<I>
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
    self.0.get(fid)
  }
}
