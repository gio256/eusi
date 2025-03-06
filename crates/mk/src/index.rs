//! Tools to read linux kernel module index files written by libkmod.

use std::{ascii::Char, ffi::CStr, fmt, marker::PhantomData, mem::size_of};

use thiserror::Error;

use crate::ascii::{AsciiErr, chars};

/// Magic bytes stored at the beginning of every kernel module index file.
/// See [libkmod] for header details.
///
/// [libkmod]: https://github.com/kmod-project/kmod/blob/2f5f67e689cd374e61b9a3ecb5e3d207e35bdbd0/libkmod/libkmod-index.c#L25-L45
const INDEX_MAGIC: u32 = 0xB007F457;

/// The compatible major version for kernel module index files.
const INDEX_VERSION_MAJOR: u32 = 0x02;

/// Characters that mark the beginning of a wildcard search.
/// These are `b'*'`, `b'?'`, and `b'['`.
const WILD_CHARS: [Char; 3] = [Char::Asterisk, Char::QuestionMark, Char::LeftSquareBracket];

/// A wrapper over a valid in-memory kernel module index file.
pub(crate) struct Index<'a> {
    root: Node<'a>,
}

#[derive(Debug, Error)]
pub(crate) enum IndexErr {
    #[error("unknown magic bytes {:02x?}", .0.to_le())]
    Magic(u32),
    #[error("incompatible index version {0}")]
    Version(u32),
    #[error("index read failed with {0}")]
    Read(#[from] ReadErr),
    #[error("index search failed with {0}")]
    Find(#[from] FindErr),
}

impl<'a> Index<'a> {
    pub fn new(buf: &'a [u8]) -> Result<Self, IndexErr> {
        let mut ptr = Ptr::new(buf, 0);
        let magic = ptr.read()?;
        if magic != INDEX_MAGIC {
            return Err(IndexErr::Magic(magic));
        }
        let ver = ptr.read()?;
        if ver >> 16 != INDEX_VERSION_MAJOR {
            return Err(IndexErr::Version(ver));
        }
        let root = Node::read(buf, ptr.read()?)?;
        Ok(Self { root })
    }

    pub fn find(&self, key: &[Char]) -> Result<&'a CStr, IndexErr> {
        self.root.find(key).map_err(Into::into)
    }

    /// NB: we do not currently sort the returned values by priority.
    pub fn find_wild(&self, key: &[Char]) -> Result<Vec<Value<'a>>, IndexErr> {
        Wild::default().find(&self.root, key).map_err(Into::into)
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
    const CUR: u32 = 0x0FFFFFFF;

    const fn new(v: u32) -> Self {
        Self(v)
    }
    const fn cur(&self) -> u32 {
        self.0 & Self::CUR
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
struct Ptr<'a> {
    buf: &'a [u8],
    cur: usize,
}

#[derive(Debug, Error)]
pub(crate) enum ReadErr {
    #[error("out of bounds index")]
    Oob,
    #[error("invalid ascii char {0}")]
    Ascii(u8),
    #[error("index overflow")]
    Overflow,
    #[error("reading c string failed with {0}")]
    CStr(#[from] std::ffi::FromBytesUntilNulError),
    #[error(transparent)]
    Slice(#[from] std::array::TryFromSliceError),
    #[error("invalid child fields")]
    Desc,
}

impl fmt::Debug for Ptr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        f.debug_struct("Ptr")
            .field("buf", &self.buf.as_ptr())
            .field("cur", &format!("{:02x?}", self.cur))
            .finish()
    }
}

impl<'a> Ptr<'a> {
    /// Creates a new `Ptr` from a slice of bytes and an offset into the slice.
    fn new(buf: &'a [u8], cur: usize) -> Self {
        Self { buf, cur }
    }

    /// Reads a value of type `T` from the buffer and advances the pointer
    /// according to the `Read` implementation of `T`.
    fn read<T>(&mut self) -> Result<T, ReadErr>
    where
        T: Read<'a>,
    {
        T::read_from_ptr(self)
    }

    /// Advances the pointer by `count` bytes.
    fn add(&mut self, count: usize) -> Result<(), ReadErr> {
        self.cur = self.cur.checked_add(count).ok_or(ReadErr::Overflow)?;
        Ok(())
    }

    /// Reads `N` bytes from the buffer and advances the pointer by `N` bytes.
    fn get_and_advance<const N: usize>(&mut self) -> Result<[u8; N], ReadErr> {
        let end = self.cur + N;
        let b = self
            .buf
            .get(self.cur..end)
            .ok_or(ReadErr::Oob)?
            .try_into()?;
        self.cur = end;
        Ok(b)
    }
}

trait Read<'a> {
    fn read_from_ptr(ptr: &mut Ptr<'a>) -> Result<Self, ReadErr>
    where
        Self: Sized;
}

impl Read<'_> for u32 {
    fn read_from_ptr(ptr: &mut Ptr) -> Result<Self, ReadErr> {
        ptr.get_and_advance::<{ size_of::<Self>() }>()
            .map(Self::from_be_bytes)
    }
}

impl<'a> Read<'a> for &'a CStr {
    fn read_from_ptr(ptr: &mut Ptr<'a>) -> Result<Self, ReadErr> {
        let b = ptr.buf.get(ptr.cur..).ok_or(ReadErr::Oob)?;
        let s = CStr::from_bytes_until_nul(b)?;
        // make sure we include the null byte
        ptr.cur += s.count_bytes() + 1;
        Ok(s)
    }
}

impl Read<'_> for Char {
    fn read_from_ptr(ptr: &mut Ptr) -> Result<Self, ReadErr> {
        let &b = ptr.buf.get(ptr.cur).ok_or(ReadErr::Oob)?;
        if let Some(char) = Char::from_u8(b) {
            ptr.cur += size_of::<u8>();
            Ok(char)
        } else {
            Err(ReadErr::Ascii(b))
        }
    }
}

/// The descendant fields of a trie node.
#[derive(Debug, Clone, Copy)]
struct Desc<'a> {
    // The ascii char representing the first child stored.
    first: Char,
    // The ascii char representing the last child stored.
    last: Char,
    // The index of the first child.
    cur: usize,
    _ref: PhantomData<&'a [u8]>,
}

impl Desc<'_> {
    fn new(first: Char, last: Char, cur: usize) -> Self {
        Self {
            first,
            last,
            cur,
            _ref: PhantomData,
        }
    }
}

impl<'a> Read<'a> for Desc<'a> {
    fn read_from_ptr(ptr: &mut Ptr) -> Result<Self, ReadErr> {
        let first: Char = ptr.read()?;
        let last: Char = ptr.read()?;
        let cur = ptr.cur;
        let child_count = last
            .to_u8()
            .checked_sub(first.to_u8())
            .ok_or(ReadErr::Desc)?
            + 1;
        ptr.add(size_of::<u32>() * child_count as usize)?;
        Ok(Self::new(first, last, cur))
    }
}

/// Each value is stored with a priority followed by a null-terminated string.
#[allow(unused)]
#[derive(Debug, Clone)]
pub(crate) struct Value<'a> {
    priority: u32,
    v: &'a CStr,
}

impl<'a> Read<'a> for Value<'a> {
    fn read_from_ptr(ptr: &mut Ptr<'a>) -> Result<Self, ReadErr> {
        let priority = ptr.read()?;
        let v = ptr.read()?;
        Ok(Self { priority, v })
    }
}

/// The value fields of a trie node.
#[derive(Debug, Clone, Copy)]
struct Values<'a> {
    // The number of values stored.
    count: u32,
    // The index of the first value.
    cur: usize,
    _ref: PhantomData<&'a [u8]>,
}

impl Values<'_> {
    fn new(count: u32, cur: usize) -> Self {
        Self {
            count,
            cur,
            _ref: PhantomData,
        }
    }
}

impl<'a> Read<'a> for Values<'a> {
    fn read_from_ptr(ptr: &mut Ptr) -> Result<Self, ReadErr> {
        let count = ptr.read()?;
        Ok(Self::new(count, ptr.cur))
    }
}

#[derive(Debug, Clone, Default)]
struct StrBuf {
    v: Vec<Char>,
}

impl StrBuf {
    fn push_bytes(&mut self, b: &[Char]) -> usize {
        self.v.extend_from_slice(b);
        b.len()
    }
    fn push(&mut self, b: Char) {
        self.v.push(b)
    }
    fn pop(&mut self) {
        self.v.pop();
    }
    fn popn(&mut self, count: usize) {
        self.v.truncate(self.v.len().saturating_sub(count))
    }
    fn str(&self) -> &str {
        self.v.as_str()
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
    #[error("search error: {0}")]
    Read(#[from] ReadErr),
    #[error("no child")]
    NoChild,
    #[error("prefix mismatch")]
    Prefix,
    #[error("no values")]
    NoValues,
    //#[error("could not decode string: {0}")]
    //BadUtf8(#[from] std::str::Utf8Error),
    #[error(transparent)]
    Ascii(#[from] AsciiErr),
    #[error("invalid glob patter: {0}")]
    Pattern(#[from] glob::PatternError),
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
    /// Read a new node from the buffer using offset `ost`.
    fn read(buf: &'a [u8], ost: u32) -> Result<Self, FindErr> {
        let ost = Offset::new(ost);
        let cur = ost.cur() as usize;
        if cur == 0 {
            return Err(FindErr::NotFound);
        }
        let mut ptr = Ptr::new(buf, cur);

        let prefix = ost.has_prefix().then(|| ptr.read()).transpose()?;
        let desc = ost.has_desc().then(|| ptr.read()).transpose()?;
        let values = ost.has_values().then(|| ptr.read()).transpose()?;

        Ok(Self {
            buf,
            prefix,
            desc,
            values,
        })
    }

    fn prefix_bytes(&self) -> Result<&[Char], AsciiErr> {
        if let Some(prefix) = self.prefix {
            chars(prefix.to_bytes())
        } else {
            Ok(Default::default())
        }
    }

    fn children(&self) -> impl Iterator<Item = Result<(Char, Self), FindErr>> {
        self.desc.into_iter().flat_map(move |desc| {
            (desc.first..=desc.last).map(move |char| self.child(char).map(|node| (char, node)))
        })
    }

    fn values(&self) -> impl Iterator<Item = Result<Value<'a>, ReadErr>> {
        self.values.into_iter().flat_map(|v| {
            let mut ptr = Ptr::new(self.buf, v.cur);
            (0..v.count).map(move |_| ptr.read())
        })
    }

    fn chop_prefix<'k>(&self, key: &'k [Char]) -> Result<&'k [Char], FindErr> {
        if let Some(prefix) = self.prefix {
            let prefix = chars(prefix.to_bytes())?;
            key.strip_prefix(prefix).ok_or(FindErr::Prefix)
        } else {
            Ok(key)
        }
    }

    fn child(&self, char: Char) -> Result<Self, FindErr> {
        let desc = self.desc.ok_or(FindErr::NoChild)?;
        //todo
        if desc.first <= char && char <= desc.last {
            let child_cur = (char.to_u8() - desc.first.to_u8()) as usize;
            let cur = desc.cur + size_of::<u32>() * child_cur;
            let mut ptr = Ptr::new(self.buf, cur);
            let ost = ptr.read()?;
            Self::read(self.buf, ost)
        } else {
            Err(FindErr::NotFound)
        }
    }

    fn find(&self, key: &[Char]) -> Result<&'a CStr, FindErr> {
        let key = self.chop_prefix(key)?;
        if let Some((x, xs)) = key.split_first() {
            self.child(*x)?.find(xs)
        } else if let Some(vals) = self.values
            && vals.count > 0
        {
            // ignore priority
            let mut ptr = Ptr::new(self.buf, vals.cur + size_of::<u32>());
            ptr.read().map_err(Into::into)
        } else {
            Err(FindErr::NoValues)
        }
    }
}

#[derive(Debug, Clone, Default)]
struct Wild<'a> {
    v: Vec<Value<'a>>,
    strbuf: StrBuf,
}

impl<'a> Wild<'a> {
    /// The entry point for a wildcard search.
    fn find(mut self, node: &Node<'a>, key: &[Char]) -> Result<Vec<Value<'a>>, FindErr> {
        self.find_all(node, key)?;
        Ok(self.v)
    }

    fn traverse(&mut self, node: &Node<'a>, key: &[Char], prefix: &[Char]) -> Result<(), FindErr> {
        let pushed = self.strbuf.push_bytes(prefix);
        for (char, child) in node.children().filter_map(Result::ok) {
            self.strbuf.push(char);
            self.traverse(&child, key, child.prefix_bytes()?)?;
            self.strbuf.pop();
        }
        let pat = glob::Pattern::new(self.strbuf.str())?;
        if pat.matches(key.as_str()) {
            self.add_values(node)?;
        }
        self.strbuf.popn(pushed);
        Ok(())
    }

    fn traverse_child(&mut self, node: &Node<'a>, key: &[Char], char: Char) -> Result<(), FindErr> {
        if let Ok(child) = node.child(char) {
            self.strbuf.push(char);
            self.traverse(&child, key, child.prefix_bytes()?)?;
            self.strbuf.pop();
        }
        Ok(())
    }

    fn add_values(&mut self, node: &Node<'a>) -> Result<(), ReadErr> {
        node.values()
            .collect::<Result<Vec<_>, _>>()
            .map(|vals| self.v.extend(vals))
    }

    fn find_all(&mut self, node: &Node<'a>, mut key: &[Char]) -> Result<(), FindErr> {
        if let Some(prefix) = node.prefix {
            let mut j = 0;
            let prefix = chars(prefix.to_bytes())?;
            for &b in prefix {
                if WILD_CHARS.into_iter().any(|char| char == b) {
                    return self.traverse(node, &key[j..], &prefix[j..]);
                }
                // if the key is exhausted or we have a prefix mismatch, end
                // the search.
                if key.get(j).is_none_or(|&k| k != b) {
                    return Ok(());
                }
                j += 1;
            }
            key = &key[j..];
        }
        for char in WILD_CHARS {
            self.traverse_child(node, key, char)?;
        }
        if let Some((&x, xs)) = key.split_first() {
            self.find_all(&node.child(x)?, xs)
        } else {
            self.add_values(node).map_err(Into::into)
        }
    }
}
