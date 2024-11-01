use core::{cmp, marker::PhantomData, num::NonZeroU64};

pub use dbutils::{
  equivalent::{Comparable, Equivalent},
  types::{SliceRef, Str, Type, TypeRef},
};
use indexsort::{search, IndexSort};
use rarena_allocator::{either::Either, unsync::Arena, Allocator, Buffer};

use crate::HEADER_SIZE;

use super::{error::Error, Options};

/// Iterators for the discard log.
pub mod iter;
use iter::*;

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
mod immutable;
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
pub use immutable::*;

const DISCARD_LEN_SIZE: usize = 8;

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
#[derive(Debug)]
pub struct DiscardLog<I = u32> {
  arena: Arena,
  len: usize,
  capacity: usize,

  // Once constructed, the below fields are immutable.
  #[allow(dead_code)]
  opts: Options,
  _marker: PhantomData<I>,
}

impl<I> IndexSort for DiscardLog<I>
where
  I: Fid,
  for<'a> I::Ref<'a>: Ord,
{
  #[inline]
  fn len(&self) -> usize {
    self.len
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
    self.len
  }

  /// Returns `true` if the discard log is empty.
  #[inline]
  pub const fn is_empty(&self) -> bool {
    self.len == 0
  }

  /// Returns the path of the log.
  ///
  /// If the log is in memory, this method will return `None`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  ///
  /// let log = Options::new()
  ///   .with_capacity(100)
  ///   .alloc::<u32>()
  ///   .unwrap();
  ///
  /// assert_eq!(log.path(), None);
  ///
  /// let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  /// let log = unsafe {
  ///   Options::new()
  ///     .with_capacity(100)
  ///     .with_create(true)
  ///     .with_write(true)
  ///     .with_read(true)
  ///     .map_mut::<u32, _>(&path)
  ///     .unwrap()
  /// };
  ///
  /// assert_eq!(log.path().map(|p| p.as_path()), Some(path.as_ref()));
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn path(&self) -> Option<&std::rc::Rc<std::path::PathBuf>> {
    self.arena.path()
  }

  /// Returns `true` if the log is in memory.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  ///
  /// let log = Options::new()
  ///   .with_capacity(100)
  ///   .alloc::<u32>()
  ///   .unwrap();
  ///
  /// assert!(log.in_memory());
  ///
  /// # #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  /// # {
  /// let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  /// let log = unsafe {
  ///   Options::new()
  ///     .with_capacity(100)
  ///     .with_create(true)
  ///     .with_write(true)
  ///     .with_read(true)
  ///     .map_mut::<u32, _>(&path)
  ///     .unwrap()
  /// };
  /// assert!(!log.in_memory());
  /// # }
  ///
  /// ```
  #[inline]
  pub fn in_memory(&self) -> bool {
    self.arena.is_inmemory()
  }

  /// Returns `true` if the log is on disk.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  ///
  /// let log = Options::new()
  ///   .with_capacity(100)
  ///   .alloc::<u32>()
  ///   .unwrap();
  ///
  /// assert!(!log.on_disk());
  ///
  /// # #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  /// # {
  /// let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  /// let log = unsafe {
  ///   Options::new()
  ///     .with_capacity(100)
  ///     .with_create(true)
  ///     .with_write(true)
  ///     .with_read(true)
  ///     .map_mut::<u32, _>(&path)
  ///     .unwrap()
  /// };
  /// assert!(log.on_disk());
  /// # }
  /// ```
  #[inline]
  pub fn on_disk(&self) -> bool {
    self.arena.is_ondisk()
  }

  /// Returns `true` if the log is using a memory map backend.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  ///
  /// let log = Options::new()
  ///   .with_capacity(100)
  ///   .alloc::<u32>()
  ///   .unwrap();
  ///
  /// assert!(!log.is_map());
  ///
  /// let log = Options::new()
  ///   .with_capacity(100)
  ///   .map_anon::<u32>()
  ///   .unwrap();
  ///
  /// assert!(log.is_map());
  ///
  /// # #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  /// # {
  /// let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  /// let log = unsafe {
  ///   Options::new()
  ///     .with_capacity(100)
  ///     .with_create(true)
  ///     .with_write(true)
  ///     .with_read(true)
  ///     .map_mut::<u32, _>(&path)
  ///     .unwrap()
  /// };
  /// assert!(log.is_map());
  /// # }
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn is_map(&self) -> bool {
    self.arena.is_map()
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
  /// let log = Options::new()
  ///   .with_capacity(100)
  ///   .alloc::<u32>()
  ///   .unwrap();
  ///
  /// let reserved = unsafe { log.reserved_slice() };
  /// assert!(reserved.is_empty());
  ///
  /// let log = Options::new()
  ///   .with_capacity(100)
  ///   .with_reserved(8)
  ///   .alloc::<u32>()
  ///   .unwrap();
  ///
  /// let reserved = unsafe { log.reserved_slice() };
  /// assert_eq!(reserved.len(), 8);
  /// ```
  #[inline]
  pub unsafe fn reserved_slice(&self) -> &[u8] {
    let reserved = self.opts.reserved();
    if reserved == 0 {
      return &[];
    }

    let reserved_slice = self.arena.reserved_slice();
    &reserved_slice[HEADER_SIZE..]
  }

  /// Locks the underlying file for exclusive access, only works on mmap with a file backend.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  /// /// Create a new file without automatic syncing.
  /// let log = unsafe {
  ///   Options::new()
  ///     .with_sync(false)
  ///     .with_create(true)
  ///     .with_read(true)
  ///     .with_write(true)
  ///     .with_capacity(100)
  ///     .map_mut::<u32, _>(&path).unwrap()
  /// };
  ///
  /// log.lock_exclusive().unwrap();
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn lock_exclusive(&self) -> std::io::Result<()> {
    self.arena.lock_exclusive()
  }

  /// Locks the underlying file for shared access, only works on mmap with a file backend.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  /// /// Create a new file without automatic syncing.
  /// let log = unsafe {
  ///   Options::new()
  ///     .with_sync(false)
  ///     .with_create(true)
  ///     .with_read(true)
  ///     .with_write(true)
  ///     .with_capacity(100)
  ///     .map_mut::<u32, _>(&path).unwrap()
  /// };
  ///
  /// log.lock_shared().unwrap();
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn lock_shared(&self) -> std::io::Result<()> {
    self.arena.lock_shared()
  }

  /// Unlocks the underlying file, only works on mmap with a file backend.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  /// /// Create a new file without automatic syncing.
  /// let log = unsafe {
  ///   Options::new()
  ///     .with_sync(false)
  ///     .with_create(true)
  ///     .with_read(true)
  ///     .with_write(true)
  ///     .with_capacity(100)
  ///     .map_mut::<u32, _>(&path).unwrap()
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
    self.arena.unlock()
  }

  /// Returns the mutable reference to the reserved slice.
  ///
  /// ## Safety
  /// - The caller must ensure that the there is no others accessing reserved slice for either read or write.
  /// - This method is not thread-safe, so be careful when using it.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  ///
  /// let log = Options::new()
  ///   .with_capacity(100)
  ///   .alloc::<u32>()
  ///   .unwrap();
  ///
  /// let reserved = unsafe { log.reserved_slice_mut() };
  /// assert!(reserved.is_empty());
  ///
  /// let log = Options::new()
  ///   .with_capacity(100)
  ///   .with_reserved(8)
  ///   .alloc::<u32>()
  ///   .unwrap();
  ///
  /// let reserved = unsafe { log.reserved_slice_mut() };
  /// assert_eq!(reserved.len(), 8);
  ///
  /// reserved.copy_from_slice(b"mysanity");
  /// assert_eq!(reserved, b"mysanity");
  ///
  /// let reserved = unsafe { log.reserved_slice() };
  /// assert_eq!(reserved, b"mysanity");
  /// ```
  #[allow(clippy::mut_from_ref)]
  #[inline]
  pub unsafe fn reserved_slice_mut(&self) -> &mut [u8] {
    let reserved = self.opts.reserved();
    if reserved == 0 {
      return &mut [];
    }

    let reserved_slice = self.arena.reserved_slice_mut();
    &mut reserved_slice[HEADER_SIZE..]
  }

  /// Flushes the memory-mapped file to disk.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  /// /// Create a new file without automatic syncing.
  /// let arena = unsafe {
  ///   Options::new()
  ///     .with_sync(false)
  ///     .with_create(true)
  ///     .with_read(true)
  ///     .with_write(true)
  ///     .with_capacity(100)
  ///     .map_mut::<u32, _>(&path).unwrap() };
  ///
  /// arena.flush().unwrap();
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn flush(&self) -> std::io::Result<()> {
    self.arena.flush()
  }

  /// Flushes the memory-mapped file to disk asynchronously.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  /// /// Create a new file without automatic syncing.
  /// let log = unsafe {
  ///   Options::new()
  ///     .with_sync(false)
  ///     .with_create(true)
  ///     .with_read(true)
  ///     .with_write(true)
  ///     .with_capacity(100)
  ///     .map_mut::<u32, _>(&path).unwrap()
  /// };
  ///
  /// log.flush_async().unwrap();
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn flush_async(&self) -> std::io::Result<()> {
    self.arena.flush_async()
  }

  /// Flushes outstanding memory map modifications in the range to disk.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// /// Create a new file without automatic syncing.
  /// let log = unsafe {
  ///   Options::new()
  ///     .with_sync(false)
  ///     .with_create(true)
  ///     .with_read(true)
  ///     .with_write(true)
  ///     .with_capacity(100)
  ///     .map_mut::<u32, _>(&path).unwrap()
  /// };
  ///
  /// log.flush_range(0, 50).unwrap();
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn flush_range(&self, offset: usize, len: usize) -> std::io::Result<()> {
    self.arena.flush_header_and_range(offset, len)
  }

  /// Asynchronously flushes outstanding memory map modifications in the range to disk.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  /// /// Create a new file without automatic syncing.
  /// let log = unsafe {
  ///   Options::new()
  ///     .with_sync(false)
  ///     .with_create(true)
  ///     .with_read(true)
  ///     .with_write(true)
  ///     .with_capacity(100)
  ///     .map_mut::<u32, _>(&path).unwrap()
  /// };
  ///
  /// log.flush_async_range(0, 50).unwrap();
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn flush_async_range(&self, offset: usize, len: usize) -> std::io::Result<()> {
    self.arena.flush_async_header_and_range(offset, len)
  }

  #[inline]
  fn data(&self) -> &[u8] {
    self.arena.data()
  }

  pub(crate) fn construct(arena: Arena, opts: Options) -> Self
  where
    I: Fid,
  {
    let data = arena.data();
    let data_len = data.len();
    let entry_size = I::ENCODED_LEN + DISCARD_LEN_SIZE;
    let num_entries = data_len / entry_size;
    let remaining = data_len % entry_size;
    let arena_remaining = arena.remaining();
    let ro = arena.read_only();

    // If there is remaining bytes in the arena, then it should be zero because each entry should be of fixed size.
    if remaining != 0 && !ro {
      let ptr = arena.raw_mut_ptr();
      let offset = arena.allocated();

      unsafe {
        core::ptr::write_bytes(ptr.add(offset), 0, arena_remaining);
      }
    }

    let cap = (arena_remaining / entry_size) + num_entries;

    Self {
      arena,
      len: num_entries,
      opts,
      capacity: cap,
      _marker: PhantomData,
    }
  }
}

impl<I> DiscardLog<I>
where
  I: Fid,
{
  /// Returns an iterator over the entries of the discard log.
  ///
  /// See also [`values`] and [`keys`].
  #[inline]
  pub const fn iter(&self) -> Iter<'_, I> {
    Iter::new(self)
  }

  /// Returns an iterator over the fid of the discard log.
  ///
  /// The iterator returned by this function is faster than the [`iter`] iterator because it does not need to decode the discard value.
  #[inline]
  pub const fn keys(&self) -> Keys<'_, I> {
    Keys::new(self)
  }

  /// Returns an iterator over the discard values of the discard log.
  ///
  /// The iterator returned by this function is faster than the [`iter`] iterator because it does not need to decode the file id.
  #[inline]
  pub const fn values(&self) -> Values<'_, I> {
    Values::new(self)
  }

  /// Returns the maximum number of discarded bytes and the file id that contains the maximum discard value.
  ///
  /// If the discard log is empty, it would return `None`.
  #[inline]
  pub fn max_discard(&self) -> Option<(I::Ref<'_>, u64)> {
    self.iter().max_by(|(_, a), (_, b)| a.cmp(b))
  }

  #[inline]
  fn truncate(&mut self) -> Result<(), Error> {
    let new_cap = ((self.arena.capacity() as u64) * 2).min(u32::MAX as u64) as usize;
    let entry_size = I::ENCODED_LEN + DISCARD_LEN_SIZE;
    #[cfg(not(all(feature = "memmap", not(target_family = "wasm"))))]
    self.arena.truncate(new_cap);

    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    self.arena.truncate(new_cap)?;

    let cap = (self.arena.remaining() / entry_size) + self.len;
    self.capacity = cap;
    Ok(())
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

    if idx < self.len && eq {
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
  pub fn increase(&mut self, fid: &I, discard: NonZeroU64) -> Result<u64, Either<I::Error, Error>>
  where
    I: for<'a> Comparable<I::Ref<'a>>,
  {
    let entry_size = I::ENCODED_LEN + DISCARD_LEN_SIZE;
    let data = self.arena.data();
    let data_offset = self.arena.data_offset();
    let (eq, idx) = self.search(fid);

    if idx < self.len && eq {
      let off = idx * entry_size + I::ENCODED_LEN;
      let cur_disc = u64::from_be_bytes((&data[off..off + DISCARD_LEN_SIZE]).try_into().unwrap());

      unsafe {
        let buf = self
          .arena
          .get_bytes_mut(data_offset + off, DISCARD_LEN_SIZE);
        let new_discard = discard.get() + cur_disc;
        buf.copy_from_slice(&(new_discard).to_be_bytes());

        #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
        {
          if self.opts.sync() {
            self
              .arena
              .flush_header_and_range(off, DISCARD_LEN_SIZE)
              .unwrap();
          }
        }
      }

      return Ok(cur_disc);
    }

    // Could not find the fid, add the entry.

    // Check if there is enough space in the arena, if not increase the size of the arena.
    while self.arena.remaining() < entry_size {
      self.truncate().map_err(Either::Right)?;
    }

    let discard = discard.get();
    unsafe {
      let mut buf = self
        .arena
        .alloc_bytes(entry_size as u32)
        .map_err(|e| Either::Right(Error::from_insufficient_space(e)))?;
      buf.set_len(I::ENCODED_LEN);
      fid.encode(&mut buf).map_err(Either::Left)?;
      buf.put_u64_be_unchecked(discard);
      buf.detach();
    };

    // Move to next slot
    self.len += 1;

    IndexSort::sort(self);

    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    if self.opts.sync() {
      self.arena.flush().map_err(|e| Either::Right(e.into()))?;
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

    if idx < self.len && eq {
      let off = idx * entry_size + I::ENCODED_LEN;
      let cur_disc = u64::from_be_bytes((&data[off..off + DISCARD_LEN_SIZE]).try_into().unwrap());

      unsafe {
        let buf = self
          .arena
          .get_bytes_mut(data_offset + off, DISCARD_LEN_SIZE);
        let new_discard = cur_disc - discard.get();
        buf.copy_from_slice(&(new_discard).to_be_bytes());

        #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
        {
          if self.opts.sync() {
            self
              .arena
              .flush_header_and_range(off, DISCARD_LEN_SIZE)
              .unwrap();
          }
        }
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

    if idx < self.len && eq {
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
    let idx = search(self.len, |slot| {
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
