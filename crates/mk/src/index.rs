use std::ffi::CStr;
use std::fmt;
use std::{marker::PhantomData, mem::size_of};
use thiserror::Error;

const INDEX_MAGIC: u32 = 0xB007F457;
const INDEX_VERSION_MAJOR: u32 = 0x02;

const ASCII_MAX: u8 = 127;

pub(crate) struct Index<'a> {
    root: Node<'a>,
}

#[derive(Debug, Error)]
pub(crate) enum IndexErr {
    #[error("unknown magic bytes: {:02x?}", .0.to_le())]
    Magic(u32),
    #[error("incompatible index version: {}", .0)]
    Version(u32),
    #[error(transparent)]
    Ptr(#[from] PtrErr),
    #[error(transparent)]
    Find(#[from] FindErr),
}

impl<'a> Index<'a> {
    pub fn new(buf: &'a [u8]) -> Result<Self, IndexErr> {
        let mut ptr = Ptr::new(buf, 0);
        let magic = ptr.read_u32()?;
        if magic != INDEX_MAGIC {
            return Err(IndexErr::Magic(magic));
        }
        let ver = ptr.read_u32()?;
        if ver >> 16 != INDEX_VERSION_MAJOR {
            return Err(IndexErr::Version(ver));
        }
        let root_offset = ptr.read_u32()?;
        let root = Node::read(buf, root_offset)?;
        Ok(Self { root })
    }

    pub fn find(&self, key: &[u8]) -> Result<&'a CStr, IndexErr> {
        self.root.clone().find(key).map_err(Into::into)
    }
}

/// Represents an offset as read from the index file.
#[derive(Clone, Copy)]
struct Offset(u32);

impl fmt::Debug for Offset {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        f.debug_tuple("Offset")
            .field(&format!("{:02x?}", self.0))
            .finish()
    }
}

/// Flags are stored in the high nibble.
impl Offset {
    /// An offset with the prefix flag set contains a prefix.
    const PREFIX: u32 = 0x80000000;
    /// An offset with the values flag set contains a value count and a pointer.
    const VALUES: u32 = 0x40000000;
    /// An offset with the descendants flag set contains the three child fields.
    const DESC: u32 = 0x20000000;
    /// The remainder of the offset stores the actual index into the file.
    const IDX: u32 = 0x0FFFFFFF;

    const fn new(v: u32) -> Self {
        Self(v)
    }
    const fn idx(&self) -> u32 {
        self.0 & Self::IDX
    }
    const fn has_prefix(&self) -> bool {
        self.0 & Self::PREFIX > 0
    }
    const fn has_desc(&self) -> bool {
        self.0 & Self::DESC > 0
    }
    const fn has_values(&self) -> bool {
        self.0 & Self::VALUES > 0
    }
}

/// A pointer into the index file.
#[derive(Clone)]
struct Ptr<'a> {
    buf: &'a [u8],
    idx: usize,
}

#[derive(Debug, Error)]
pub(crate) enum PtrErr {
    #[error("out of bounds index")]
    Oob,
    #[error("invalid ascii char")]
    Ascii,
    #[error("index overflow")]
    Overflow,
    #[error(transparent)]
    Cstr(#[from] std::ffi::FromBytesUntilNulError),
    #[error(transparent)]
    Slice(#[from] std::array::TryFromSliceError),
}

impl fmt::Debug for Ptr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        f.debug_struct("Ptr")
            .field("buf", &self.buf.as_ptr())
            .field("idx", &format!("{:02x?}", self.idx))
            .finish()
    }
}

impl<'a> Ptr<'a> {
    fn new(buf: &'a [u8], idx: usize) -> Self {
        Self { buf, idx }
    }

    /// Advances the pointer by `count` bytes.
    fn skip(&mut self, count: usize) -> Result<(), PtrErr> {
        self.idx = self.idx.checked_add(count).ok_or(PtrErr::Overflow)?;
        Ok(())
    }

    /// Reads an ascii char from the current pointer index, then advances the
    /// pointer by one byte.
    fn read_char(&mut self) -> Result<u8, PtrErr> {
        let b = *self.buf.get(self.idx).ok_or(PtrErr::Oob)?;
        if b <= ASCII_MAX {
            self.idx += size_of::<u8>();
            Ok(b)
        } else {
            Err(PtrErr::Ascii)
        }
    }

    /// Reads a `u32` from the current pointer index, then advances the pointer
    /// by four bytes.
    fn read_u32(&mut self) -> Result<u32, PtrErr> {
        let end = self.idx + size_of::<u32>();
        let b = self.buf.get(self.idx..end).ok_or(PtrErr::Oob)?.try_into()?;
        self.idx = end;
        Ok(u32::from_be_bytes(b))
    }

    /// Reads a `CStr` from the current pointer index, stopping at the first
    /// null byte and advancing the pointer to the end of the string.
    fn read_cstr(&mut self) -> Result<&'a CStr, PtrErr> {
        let b = self.buf.get(self.idx..).ok_or(PtrErr::Oob)?;
        let s = CStr::from_bytes_until_nul(b)?;
        // make sure we include the null byte
        self.idx += s.count_bytes() + 1;
        Ok(s)
    }
}

/// The descendant fields of a trie node.
#[derive(Debug, Clone, Copy)]
struct Desc<'a> {
    // The ascii char representing the first child stored.
    first: u8,
    // The ascii char representing the last child stored.
    last: u8,
    // The index of the first child.
    idx: usize,
    _ref: PhantomData<&'a ()>,
}

impl Desc<'_> {
    fn new(first: u8, last: u8, idx: usize) -> Self {
        Self {
            first,
            last,
            idx,
            _ref: PhantomData,
        }
    }
}

/// Each value is stored with a priority followed by a null-terminated string.
#[allow(unused)]
#[derive(Debug)]
struct Value<'a> {
    priority: u32,
    v: &'a CStr,
}

/// The value fields of a trie node.
#[derive(Debug, Clone)]
struct Values<'a> {
    // The number of values stored.
    count: u32,
    // The index of the first value.
    idx: usize,
    _ref: PhantomData<&'a ()>,
}

impl Values<'_> {
    fn new(count: u32, idx: usize) -> Self {
        Self {
            count,
            idx,
            _ref: PhantomData,
        }
    }
}

#[derive(Clone)]
struct Node<'a> {
    buf: &'a [u8],
    prefix: Option<&'a CStr>,
    desc: Option<Desc<'a>>,
    values: Option<Values<'a>>,
}

#[derive(Debug, Error)]
pub(crate) enum FindErr {
    #[error("not found")]
    NotFound,
    #[error(transparent)]
    Ptr(#[from] PtrErr),
    #[error("invalid child fields")]
    Desc,
    #[error("no child")]
    NoChild,
    #[error("prefix mismatch")]
    Prefix,
    #[error("no values")]
    NoValues,
}

impl fmt::Debug for Node<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        f.debug_struct("Node")
            .field("buf", &self.buf.as_ptr())
            .field("prefix", &self.prefix)
            .field("desc", &self.desc)
            .field("values", &self.values)
            .finish()
    }
}

impl<'a> Node<'a> {
    fn read(buf: &'a [u8], ost: u32) -> Result<Self, FindErr> {
        let ost = Offset::new(ost);
        let idx = ost.idx() as usize;
        if idx == 0 || buf.len() <= idx {
            return Err(FindErr::NotFound);
        }
        let mut ptr = Ptr::new(buf, idx);

        let prefix = if ost.has_prefix() {
            Some(ptr.read_cstr()?)
        } else {
            None
        };

        let desc = if ost.has_desc() {
            let first = ptr.read_char()?;
            let last = ptr.read_char()?;
            let idx = ptr.idx;
            let child_count = last.checked_sub(first).ok_or(FindErr::Desc)? + 1;
            ptr.skip(size_of::<u32>() * child_count as usize)?;
            Some(Desc::new(first, last, idx))
        } else {
            None
        };

        let values = if ost.has_values() {
            let count = ptr.read_u32()?;
            Some(Values::new(count, ptr.idx))
        } else {
            None
        };
        Ok(Self {
            buf,
            prefix,
            desc,
            values,
        })
    }

    fn chop_prefix<'k>(&self, key: &'k [u8]) -> Option<&'k [u8]> {
        if let Some(prefix) = self.prefix {
            key.strip_prefix(prefix.to_bytes())
        } else {
            Some(key)
        }
    }

    fn read_child(&self, char: u8) -> Result<Node<'a>, FindErr> {
        let desc = self.desc.ok_or(FindErr::NoChild)?;
        if desc.first <= char && char <= desc.last {
            let child_idx = (char - desc.first) as usize;
            let idx = desc.idx + size_of::<u32>() * child_idx;
            let mut ptr = Ptr::new(self.buf, idx);
            let ost = ptr.read_u32()?;
            Self::read(self.buf, ost)
        } else {
            Err(FindErr::NotFound)
        }
    }

    fn find(self, key: &[u8]) -> Result<&'a CStr, FindErr> {
        let key = self.chop_prefix(key).ok_or(FindErr::Prefix)?;
        if let Some((x, xs)) = key.split_first() {
            self.read_child(*x)?.find(xs)
        } else if let Some(vals) = self.values
            && vals.count > 0
        {
            assert_eq!(vals.count, 1, "does this hold?"); //todo: rm debug
            // ignore priority
            let mut ptr = Ptr::new(self.buf, vals.idx + size_of::<u32>());
            ptr.read_cstr().map_err(Into::into)
        } else {
            Err(FindErr::NoValues)
        }
    }
}
