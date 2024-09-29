/// Error type for the value logs.
#[derive(Debug)]
pub enum Error {
  /// Returned there are no more enough space in the value log.
  InsufficientSpace {
    /// The requested size
    requested: u32,
    /// The remaining size
    available: u32,
  },

  /// Returned when an IO error occurs.
  #[cfg(feature = "std")]
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
  IO(std::io::Error),
}

#[cfg(feature = "std")]
impl From<std::io::Error> for Error {
  fn from(err: std::io::Error) -> Self {
    Error::IO(err)
  }
}

impl core::fmt::Display for Error {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Self::InsufficientSpace {
        requested,
        available,
      } => write!(
        f,
        "insufficient space, requested: {}, available: {}",
        requested, available
      ),
      #[cfg(feature = "std")]
      Self::IO(err) => err.fmt(f),
    }
  }
}

impl core::error::Error for Error {}

impl Error {
  #[inline]
  pub(crate) const fn from_insufficient_space(err: rarena_allocator::Error) -> Self {
    match err {
      rarena_allocator::Error::InsufficientSpace {
        requested,
        available,
      } => Self::InsufficientSpace {
        requested,
        available,
      },
      _ => unreachable!(),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub(crate) fn from_arena_io_err(e: std::io::Error) -> std::io::Error {
    if e.to_string().starts_with("ARENA's magic version mismatch") {
      bad_version()
    } else {
      e
    }
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[inline]
pub(crate) fn bad_magic_text() -> std::io::Error {
  std::io::Error::new(std::io::ErrorKind::InvalidData, "bad magic text")
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[inline]
pub(crate) fn bad_magic_version() -> std::io::Error {
  std::io::Error::new(std::io::ErrorKind::InvalidData, "bad magic version")
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[inline]
fn bad_version() -> std::io::Error {
  std::io::Error::new(std::io::ErrorKind::InvalidData, "bad version")
}
