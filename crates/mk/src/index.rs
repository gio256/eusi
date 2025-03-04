#![allow(unused)]
use std::ffi::CStr;
use std::fmt;
use std::iter::zip;
use std::ops::Deref;
use std::slice::SliceIndex;
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
    #[error("unknown magic bytes {:02x?}", .0.to_le())]
    Magic(u32),
    #[error("incompatible index version {0}")]
    Version(u32),
    #[error("index open failed with {0}")]
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

    pub fn find(&self, key: &[u8]) -> Result<&'a CStr, IndexErr> {
        self.root.clone().find(key).map_err(Into::into)
    }

    pub fn find_wild(&self, key: &[u8]) -> Result<(), IndexErr> {
        let tmp = Wild::default().find(&self.root, key)?;
        dbg!(tmp);
        Ok(())
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
    #[error("invalid ascii char")]
    Ascii,
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

    //fn get<I>(&self, i: I) -> Option<&<I as SliceIndex<[u8]>>::Output>
    //where
    //    I: SliceIndex<[u8]>,
    //{
    //    self.buf.get(self.cur..)?.get(i)
    //}
}

trait Read<'a> {
    fn read_from_ptr(ptr: &mut Ptr<'a>) -> Result<Self, ReadErr>
    where
        Self: Sized;
}

impl Read<'_> for u32 {
    fn read_from_ptr(ptr: &mut Ptr) -> Result<Self, ReadErr> {
        ptr.get_and_advance::<{ size_of::<Self>() }>()
            .map(u32::from_be_bytes)
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

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
struct Char(u8);

impl Deref for Char {
    type Target = u8;

    fn deref(&self) -> &u8 {
        &self.0
    }
}

impl Read<'_> for Char {
    fn read_from_ptr(ptr: &mut Ptr) -> Result<Self, ReadErr> {
        let b = *ptr.buf.get(ptr.cur).ok_or(ReadErr::Oob)?;
        if b <= ASCII_MAX {
            ptr.cur += size_of::<u8>();
            Ok(Self(b))
        } else {
            Err(ReadErr::Ascii)
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
        let child_count = last.checked_sub(*first).ok_or(ReadErr::Desc)? + 1;
        ptr.add(size_of::<u32>() * child_count as usize)?;
        Ok(Self::new(first, last, cur))
    }
}

/// Each value is stored with a priority followed by a null-terminated string.
#[allow(unused)]
#[derive(Debug, Clone)]
struct Value<'a> {
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
    v: Vec<u8>,
}

impl StrBuf {
    fn push_cstr(&mut self, s: &CStr, cur: usize) -> usize {
        s.to_bytes()
            .get(cur..)
            .map(|b| {
                self.v.extend_from_slice(b);
                b.len()
            })
            .unwrap_or_default()
    }
    fn push(&mut self, b: u8) {
        self.v.push(b)
    }
    fn pop(&mut self) {
        self.v.pop();
    }
    fn popn(&mut self, count: usize) {
        self.v.truncate(self.v.len().saturating_sub(count))
    }
    fn str(&self) -> Result<&str, FindErr> {
        std::str::from_utf8(&self.v).map_err(Into::into)
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
    #[error("could not decode string: {0}")]
    BadUtf8(#[from] std::str::Utf8Error),
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
    fn read(buf: &'a [u8], ost: u32) -> Result<Self, FindErr> {
        let ost = Offset::new(ost);
        let cur = ost.cur() as usize;
        if cur == 0 || buf.len() <= cur {
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

    //todo: what happens if the prefix is longer than the key?
    fn chop_prefix<'k>(&self, key: &'k [u8]) -> Option<&'k [u8]> {
        if let Some(prefix) = self.prefix {
            dbg!(prefix);
            key.strip_prefix(prefix.to_bytes())
        } else {
            Some(key)
        }
    }

    fn child(&self, char: u8) -> Result<Self, FindErr> {
        let desc = self.desc.ok_or(FindErr::NoChild)?;
        if *desc.first <= char && char <= *desc.last {
            let child_cur = (char - *desc.first) as usize;
            let cur = desc.cur + size_of::<u32>() * child_cur;
            let mut ptr = Ptr::new(self.buf, cur);
            let ost = ptr.read()?;
            Self::read(self.buf, ost)
        } else {
            Err(FindErr::NotFound)
        }
    }

    fn find_all(&self, key: &[u8], j: usize, state: &mut WildState<'a>) -> Result<(), FindErr> {
        let pushed = state.strbuf.push_cstr(self.prefix.unwrap_or_default(), j);
        for (char, child) in self.children().filter_map(Result::ok) {
            state.strbuf.push(char);
            child.find_all(key, 0, state)?;
            state.strbuf.pop();
        }
        let pat = glob::Pattern::new(state.strbuf.str()?)?;
        let key = std::str::from_utf8(key)?;
        if pat.matches(key) {
            state
                .vals
                .extend(self.values().collect::<Result<Vec<_>, _>>()?);
        }
        state.strbuf.popn(pushed);
        Ok(())
    }

    fn children(&self) -> impl Iterator<Item = Result<(u8, Self), FindErr>> {
        self.desc.into_iter().flat_map(move |desc| {
            (*desc.first..=*desc.last).map(move |char| self.child(char).map(|node| (char, node)))
        })
    }

    //fn values(&self) -> Result<impl Iterator<Item = Value>, ReadErr> {
    //    self.values.into_iter().flat_map(|v| {
    //        let mut ptr = Ptr::new(self.buf, v.cur);
    //        (0..v.count).map(move |_| ptr.read::<Value>())
    //    }).collect()
    //}

    fn values(&self) -> impl Iterator<Item = Result<Value<'a>, ReadErr>> {
        self.values.into_iter().flat_map(|v| {
            let mut ptr = Ptr::new(self.buf, v.cur);
            (0..v.count).map(move |_| ptr.read())
        })
    }

    fn find(self, key: &[u8]) -> Result<&'a CStr, FindErr> {
        let key = self.chop_prefix(key).ok_or(FindErr::Prefix)?;
        if let Some((x, xs)) = key.split_first() {
            self.child(*x)?.find(xs)
        } else if let Some(vals) = self.values
            && vals.count > 0
        {
            //assert_eq!(vals.count, 1, "does this hold?"); //todo: rm debug
            // ignore priority
            let mut ptr = Ptr::new(self.buf, vals.cur + size_of::<u32>());
            ptr.read().map_err(Into::into)
        } else {
            Err(FindErr::NoValues)
        }
    }

    //todo
    fn find_wild(self, key: &[u8], state: &mut WildState<'a>) -> Result<(), FindErr> {
        //todo: this is wrong in the case '*' appears before the end of the prefix
        let prefix_len = self.prefix.map(|p| p.count_bytes()).unwrap_or_default();
        if let Some(prefix) = self.prefix {
            dbg!(prefix);
            for (j, b) in prefix.to_bytes().iter().copied().enumerate() {
                if b == b'*' || b == b'?' || b == b'[' {
                    return self.find_all(&key[j..], j, state);
                }
                if b != key[j] {
                    return Ok(());
                }
            }
        }

        if let Ok(child) = self.child(b'*') {
            eprintln!("child *");
            state.strbuf.push(b'*');
            child.find_all(&key[prefix_len..], 0, state)?;
            state.strbuf.pop();
        }
        if let Ok(child) = self.child(b'?') {
            eprintln!("child ?");
            state.strbuf.push(b'?');
            child.find_all(&key[prefix_len..], 0, state)?;
            state.strbuf.pop();
        }
        if let Ok(child) = self.child(b'[') {
            eprintln!("child [");
            state.strbuf.push(b'[');
            child.find_all(&key[prefix_len..], 0, state)?;
            state.strbuf.pop();
        }
        if key[prefix_len..].is_empty() {
            state
                .vals
                .extend(self.values().collect::<Result<Vec<_>, _>>()?);
            return Ok(());
        }

        self.child(key[prefix_len])?
            .find_wild(&key[prefix_len + 1..], state)
    }
}

#[derive(Debug, Clone, Default)]
struct WildState<'a> {
    vals: Vec<Value<'a>>,
    strbuf: StrBuf,
}

#[derive(Debug, Clone, Default)]
struct Wild<'a> {
    v: Vec<Value<'a>>,
    strbuf: StrBuf,
}

struct SplitFirst<'a, T> {
    v: &'a [T],
}

impl<'a, T> SplitFirst<'a, T> {
    fn new(v: &'a [T]) -> Self {
        Self { v }
    }
}

impl<'a, T> Iterator for SplitFirst<'a, T>
where
    T: Copy,
{
    type Item = (T, &'a [T]);
    fn next(&mut self) -> Option<Self::Item> {
        let (x, xs) = self.v.split_first()?;
        self.v = xs;
        Some((*x, xs))
    }
}

impl<'a> Wild<'a> {
    fn traverse(&mut self, node: &Node<'a>, key: &[u8], j: usize) -> Result<(), FindErr> {
        let pushed = self.strbuf.push_cstr(node.prefix.unwrap_or_default(), j);
        for (char, child) in node.children().filter_map(Result::ok) {
            self.strbuf.push(char);
            self.traverse(&child, key, 0)?;
            self.strbuf.pop();
        }
        let pat = glob::Pattern::new(self.strbuf.str()?)?;
        let key = std::str::from_utf8(key)?;
        if pat.matches(key) {
            self.add_values(node)?;
        }
        self.strbuf.popn(pushed);
        Ok(())
    }

    fn traverse_child(&mut self, node: &Node<'a>, key: &[u8], char: u8) -> Result<(), FindErr> {
        if let Ok(child) = node.child(char) {
            self.strbuf.push(char);
            self.traverse(&child, key, 0)?;
            self.strbuf.pop();
        }
        Ok(())
    }

    fn add_values(&mut self, node: &Node<'a>) -> Result<(), ReadErr> {
        node.values()
            .collect::<Result<Vec<_>, _>>()
            .map(|xs| self.v.extend(xs))
    }

    fn find(mut self, node: &Node<'a>, mut key: &[u8]) -> Result<Vec<Value<'a>>, FindErr> {
        self.find_all(node, key)?;
        Ok(self.v)
    }

    fn find_all(&mut self, node: &Node<'a>, mut key: &[u8]) -> Result<(), FindErr> {
        if let Some(prefix) = node.prefix {
            let mut j = 0;
            for &b in prefix.to_bytes() {
                if b == b'*' || b == b'?' || b == b'[' {
                    return self.traverse(node, &key[j..], j);
                }
                // if the key is exhausted or we have a prefix mismatch, end
                // the search.
                if key.get(j).is_none_or(|&k| k != b) {
                    return Ok(());
                }

                //if let Some(&x) = key.get(j) {
                //    if b != x {
                //        return Ok(())
                //    }
                //} else {
                //    return Ok(())
                //}
                j += 1;
            }
            key = &key[j..];
        }
        self.traverse_child(node, key, b'*')?;
        self.traverse_child(node, key, b'?')?;
        self.traverse_child(node, key, b'[')?;
        if let Some((x, xs)) = key.split_first() {
            self.find_all(&node.child(*x)?, xs)
        } else {
            self.add_values(node).map_err(Into::into)
        }
    }
}
