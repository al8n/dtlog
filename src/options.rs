use rarena_allocator::{unsync::Arena, Allocator, Freelist, Options as ArenaOptions};

use super::{error::Error, DiscardLog, Fid};

pub(super) const CURRENT_VERSION: u16 = 0;

pub(super) const MAGIC_TEXT: [u8; 6] = *b"dtlog!";
pub(super) const MAGIC_TEXT_SIZE: usize = MAGIC_TEXT.len();
pub(super) const MAGIC_VERSION_SIZE: usize = core::mem::size_of::<u16>();
pub(super) const HEADER_SIZE: usize = MAGIC_TEXT_SIZE + MAGIC_VERSION_SIZE;

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
mod open_options;

/// Options for configuring the value log.
#[viewit::viewit(vis_all = "pub(super)", getters(skip), setters(skip))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Options {
  magic_version: u16,
  capacity: Option<u32>,
  unify: bool,
  reserved: u32,
  lock_meta: bool,
  sync: bool,
  validate_checksum: bool,

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  create_new: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  create: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  read: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  write: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  append: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  truncate: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  offset: u64,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  stack: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  huge: Option<u8>,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  populate: bool,
}

impl Default for Options {
  #[inline]
  fn default() -> Options {
    Options::new()
  }
}

impl Options {
  /// Creates a new set of options with the default values.
  #[inline]
  pub const fn new() -> Self {
    Self {
      capacity: None,
      unify: false,
      magic_version: 0,
      reserved: 0,
      lock_meta: false,
      sync: true,
      validate_checksum: true,

      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      create_new: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      create: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      read: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      write: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      append: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      truncate: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      offset: 0,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      stack: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      huge: None,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      populate: false,
    }
  }

  /// Set the reserved bytes of the `Log`.
  ///
  /// The reserved is used to configure the start position of the `Log`. This is useful
  /// when you want to add some bytes before the `Log`, e.g. when using the memory map file backed `Log`,
  /// you can set the reserved to the size to `8` to store a 8 bytes checksum.
  ///
  /// The default reserved is `0`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  ///
  /// let opts = Options::new().with_reserved(8);
  /// ```
  #[inline]
  pub const fn with_reserved(mut self, reserved: u32) -> Self {
    self.reserved = reserved;
    self
  }

  /// Set if flush the data to the disk when new value is inserted.
  ///
  /// Default is `true`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  ///
  /// let opts = Options::new().with_sync(false);
  /// ```
  #[inline]
  pub const fn with_sync(mut self, sync: bool) -> Self {
    self.sync = sync;
    self
  }

  /// Set if validate the checksum of the value when reading the value.
  ///
  /// Default is `true`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  ///
  /// let opts = Options::new().with_validate_checksum(false);
  /// ```
  #[inline]
  pub const fn with_validate_checksum(mut self, validate_checksum: bool) -> Self {
    self.validate_checksum = validate_checksum;
    self
  }

  /// Set if lock the meta of the `Log` in the memory to prevent OS from swapping out the first page of `Log`.
  /// When using memory map backed `Log`, the meta of the `Log`
  /// is in the first page, meta is frequently accessed,
  /// lock (`mlock` on the first page) the meta can reduce the page fault,
  /// but yes, this means that one `Log` will have one page are locked in memory,
  /// and will not be swapped out. So, this is a trade-off between performance and memory usage.
  ///
  /// Default is `true`.
  ///
  /// This configuration has no effect on windows and vec backed `Log`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  ///
  /// let opts = Options::new().with_lock_meta(false);
  /// ```
  #[inline]
  pub const fn with_lock_meta(mut self, lock_meta: bool) -> Self {
    self.lock_meta = lock_meta;
    self
  }

  /// Set the magic version of the value log.
  ///
  /// This is used by the application using value log
  /// to ensure that it doesn't open the value log
  /// with incompatible data format.
  ///  
  /// The default value is `0`.
  ///
  /// ## Example
  ///
  /// ```
  /// use dtlog::Options;
  ///
  /// let opts = Options::new().with_magic_version(1);
  /// ```
  #[inline]
  pub const fn with_magic_version(mut self, magic_version: u16) -> Self {
    self.magic_version = magic_version;
    self
  }

  /// Set if use the unify memory layout of the value log.
  ///
  /// File backed value log has different memory layout with other kind backed value log,
  /// set this value to `true` will unify the memory layout of the value log, which means
  /// all kinds of backed value log will have the same memory layout.
  ///
  /// This value will be ignored if the value log is backed by a file backed memory map.
  ///
  /// The default value is `false`.
  ///
  /// ## Example
  ///
  /// ```
  /// use dtlog::Options;
  ///
  /// let opts = Options::default().with_unify(true);
  /// ```
  #[inline]
  pub const fn with_unify(mut self, unify: bool) -> Self {
    self.unify = unify;
    self
  }

  /// Sets the capacity of the underlying `Log`.
  ///
  /// ## Example
  ///
  /// ```
  /// use dtlog::Options;
  ///
  /// let options = Options::new().with_capacity(1024);
  /// ```
  #[inline]
  pub const fn with_capacity(mut self, capacity: u32) -> Self {
    self.capacity = Some(capacity);
    self
  }

  /// Get the reserved of the `Log`.
  ///
  /// The reserved is used to configure the start position of the `Log`. This is useful
  /// when you want to add some bytes before the `Log`, e.g. when using the memory map file backed `Log`,
  /// you can set the reserved to the size to `8` to store a 8 bytes checksum.
  ///
  /// The default reserved is `0`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  ///
  /// let opts = Options::new().with_reserved(8);
  ///
  /// assert_eq!(opts.reserved(), 8);
  /// ```
  #[inline]
  pub const fn reserved(&self) -> u32 {
    self.reserved
  }

  /// Get if flush the data to the disk when new value is inserted.
  ///
  /// Default is `true`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  ///
  /// let opts = Options::new().with_sync(false);
  ///
  /// assert_eq!(opts.sync(), false);
  /// ```
  #[inline]
  pub const fn sync(&self) -> bool {
    self.sync
  }

  /// Get if validate the checksum of the value when reading the value.
  ///
  /// Default is `true`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  ///
  /// let opts = Options::new().with_validate_checksum(false);
  ///
  /// assert_eq!(opts.validate_checksum(), false);
  /// ```
  #[inline]
  pub const fn validate_checksum(&self) -> bool {
    self.validate_checksum
  }

  /// Get if lock the meta of the `Log` in the memory to prevent OS from swapping out the first page of `Log`.
  /// When using memory map backed `Log`, the meta of the `Log`
  /// is in the first page, meta is frequently accessed,
  /// lock (`mlock` on the first page) the meta can reduce the page fault,
  /// but yes, this means that one `Log` will have one page are locked in memory,
  /// and will not be swapped out. So, this is a trade-off between performance and memory usage.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  ///
  /// let opts = Options::new().with_lock_meta(false);
  ///
  /// assert_eq!(opts.lock_meta(), false);
  /// ```
  #[inline]
  pub const fn lock_meta(&self) -> bool {
    self.lock_meta
  }

  /// Returns the configuration of underlying `Log` size.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  ///
  /// let options = Options::new().with_capacity(1024);
  /// ```
  #[inline]
  pub const fn capacity(&self) -> u32 {
    match self.capacity {
      Some(capacity) => capacity,
      None => 0,
    }
  }

  /// Get if use the unify memory layout of the value log.
  ///
  /// File backed value log has different memory layout with other kind backed value log,
  /// set this value to `true` will unify the memory layout of the value log, which means
  /// all kinds of backed value log will have the same memory layout.
  ///
  /// This value will be ignored if the value log is backed by a file backed memory map.
  ///  
  /// The default value is `false`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  ///
  /// let opts = Options::new().with_unify(true);
  ///
  /// assert_eq!(opts.unify(), true);
  /// ```
  #[inline]
  pub const fn unify(&self) -> bool {
    self.unify
  }

  /// Get the magic version of the value log.
  ///
  /// This is used by the application using value log
  /// to ensure that it doesn't open the value log
  /// with incompatible data format.
  ///
  /// The default value is `0`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  ///
  /// let opts = Options::new().with_magic_version(1);
  ///
  /// assert_eq!(opts.magic_version(), 1);
  /// ```
  #[inline]
  pub const fn magic_version(&self) -> u16 {
    self.magic_version
  }
}

impl Options {
  /// Create a new in-memory value log which is backed by a `AlignedVec`.
  ///
  /// **What the difference between this method and [`Options::map_anon`]?**
  ///
  /// 1. This method will use an `AlignedVec` ensures we are working within Rust's memory safety guarantees.
  ///    Even if we are working with raw pointers with `Box::into_raw`,
  ///    the backend `Log` will reclaim the ownership of this memory by converting it back to a `Box`
  ///    when dropping the backend `Log`. Since `AlignedVec` uses heap memory, the data might be more cache-friendly,
  ///    especially if you're frequently accessing or modifying it.
  ///
  /// 2. Where as [`Options::map_anon`] will use mmap anonymous to require memory from the OS.
  ///    If you require very large contiguous memory regions, `mmap` might be more suitable because
  ///    it's more direct in requesting large chunks of memory from the OS.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use dtlog::Options;
  ///
  /// // Create a new in-memory discard tracking log.
  /// let log = Options::new().with_capacity(1024).alloc::<u32>().unwrap();
  /// ```
  #[inline]
  pub fn alloc<I: Fid>(self) -> Result<DiscardLog<I>, Error> {
    let unify = self.unify;
    let mv = self.magic_version;
    self
      .to_arena_options()
      .alloc::<Arena>()
      .map_err(Error::from_insufficient_space)
      .map(|arena| {
        if unify {
          unsafe {
            let slice = arena.reserved_slice_mut();
            write_header(slice, mv);
          }
        }

        DiscardLog::construct(arena, self)
      })
  }
}

impl Options {
  #[allow(clippy::wrong_self_convention)]
  #[inline]
  pub(super) const fn to_arena_options(&self) -> ArenaOptions {
    let opts = ArenaOptions::new()
      .with_magic_version(CURRENT_VERSION)
      .with_reserved(HEADER_SIZE as u32 + self.reserved())
      .with_unify(self.unify())
      .maybe_capacity(self.capacity)
      .with_freelist(Freelist::None);

    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    {
      opts
        .with_lock_meta(self.lock_meta())
        .with_create(self.create())
        .with_create_new(self.create_new())
        .with_read(self.read())
        .with_write(self.write())
        .with_append(self.append())
        .with_truncate(self.truncate())
        .with_offset(self.offset())
        .with_stack(self.stack())
        .with_huge(self.huge())
        .with_populate(self.populate())
    }

    #[cfg(not(all(feature = "memmap", not(target_family = "wasm"))))]
    opts
  }
}

#[inline]
fn write_header(buf: &mut [u8], magic_version: u16) {
  buf[..MAGIC_TEXT_SIZE].copy_from_slice(&MAGIC_TEXT);
  buf[MAGIC_TEXT_SIZE..MAGIC_TEXT_SIZE + MAGIC_VERSION_SIZE]
    .copy_from_slice(&magic_version.to_le_bytes());
}
