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

  /// Returns the path of the log.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  ///
  /// let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  ///
  /// # std::fs::remove_file(&path);
  /// # let log = unsafe {
  /// #  Options::new()
  /// #    .with_capacity(100)
  /// #    .with_create(true)
  /// #    .with_write(true)
  /// #    .with_read(true)
  /// #    .map_mut::<u32, _>(&path)
  /// #    .unwrap()
  /// # };
  ///
  /// let log = unsafe {
  ///   Options::new()
  ///     .map::<u32, _>(&path)
  ///     .unwrap()
  /// };
  /// let path: &std::path::Path = path.as_ref();
  /// assert_eq!(log.path().as_path(), path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn path(&self) -> &std::rc::Rc<std::path::PathBuf> {
    self.0.path().unwrap()
  }

  /// Returns the reserved space in the discard log.
  ///
  /// ## Safety
  /// - The writer must ensure that the returned slice is not modified.
  /// - This method is not thread-safe, so be careful when using it.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  ///
  /// let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  /// let log = unsafe {
  ///   Options::new()
  ///     .with_capacity(100)
  ///     .with_create_new(true)
  ///     .with_write(true)
  ///     .with_sync(false)
  ///     .with_read(true)
  ///     .map_mut::<u32, _>(&path)
  ///     .unwrap()
  /// };
  ///
  /// let log = unsafe {
  ///   Options::new()
  ///     .map::<u32, _>(&path)
  ///     .unwrap()
  /// };
  ///
  /// let reserved = unsafe { log.reserved_slice() };
  /// assert!(reserved.is_empty());
  ///
  /// let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  /// let log = unsafe {
  ///   Options::new()
  ///     .with_capacity(100)
  ///     .with_create(true)
  ///     .with_write(true)
  ///     .with_sync(false)
  ///     .with_reserved(8)
  ///     .with_read(true)
  ///     .map_mut::<u32, _>(&path)
  ///     .unwrap()
  /// };
  /// let log = unsafe {
  ///   Options::new()
  ///     .with_reserved(8)
  ///     .map::<u32, _>(&path)
  ///     .unwrap()
  /// };
  ///
  /// let reserved = unsafe { log.reserved_slice() };
  /// assert_eq!(reserved.len(), 8);
  /// ```
  #[inline]
  pub unsafe fn reserved_slice(&self) -> &[u8] {
    self.0.reserved_slice()
  }

  /// Locks the underlying file for exclusive access, only works on mmap with a file backend.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  /// # let log = unsafe {
  /// #  Options::new()
  /// #    .with_capacity(100)
  /// #    .with_create(true)
  /// #    .with_write(true)
  /// #    .with_sync(false)
  /// #    .with_read(true)
  /// #    .map_mut::<u32, _>(&path)
  /// #    .unwrap()
  /// # };
  ///
  /// let log = unsafe {
  ///   Options::new()
  ///     .map::<u32, _>(&path)
  ///     .unwrap()
  /// };
  ///
  /// log.lock_exclusive().unwrap();
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn lock_exclusive(&self) -> std::io::Result<()> {
    self.0.lock_exclusive()
  }

  /// Locks the underlying file for shared access, only works on mmap with a file backend.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  /// # let log = unsafe {
  /// #   Options::new()
  /// #     .with_capacity(100)
  /// #     .with_create(true)
  /// #     .with_write(true)
  /// #     .with_sync(false)
  /// #     .with_read(true)
  /// #     .map_mut::<u32, _>(&path)
  /// #     .unwrap()
  /// # };
  ///
  /// let log = unsafe {
  ///   Options::new()
  ///     .map::<u32, _>(&path)
  ///     .unwrap()
  /// };
  ///
  /// log.lock_shared().unwrap();
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn lock_shared(&self) -> std::io::Result<()> {
    self.0.lock_shared()
  }

  /// Unlocks the underlying file, only works on mmap with a file backend.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  /// # let log = unsafe {
  /// #   Options::new()
  /// #     .with_capacity(100)
  /// #     .with_create(true)
  /// #     .with_write(true)
  /// #     .with_sync(false)
  /// #     .with_read(true)
  /// #     .map_mut::<u32, _>(&path)
  /// #     .unwrap()
  /// # };
  ///
  /// let log = unsafe {
  ///   Options::new()
  ///     .map::<u32, _>(&path)
  ///     .unwrap()
  /// };
  ///
  /// log.lock_exclusive().unwrap();
  ///
  /// log.unlock().unwrap();
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn unlock(&self) -> std::io::Result<()> {
    self.0.unlock()
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
