use eyre::{Result, ensure, eyre};
use rustix::{
    fd::AsFd,
    mm::{MapFlags, ProtFlags, mmap},
};
use std::ffi::{CStr, CString, OsStr};
use std::fmt;
use std::fs::File;
use std::os::unix::ffi::OsStrExt;
use std::path::Path;
use std::{marker::PhantomData, mem::size_of, ops::Range, ptr, slice};

const INDEX_MAGIC: u32 = 0xB007F457;
const INDEX_VERSION_MAJOR: u16 = 0x0002;

const MAGIC_RANGE: Range<usize> = 0..4;
const VERSION_MAJOR_RANGE: Range<usize> = 4..6;
const _VERSION_MINOR_RANGE: Range<usize> = 6..8;
const ROOT_OFFSET_RANGE: Range<usize> = 8..12;

// todo:
// - proper drop impl for calling munmap
// - normalize module names

// ascii char
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
struct Char(u8);

impl Char {
    const MAX: u8 = 127;
    const fn from_u8(b: u8) -> Option<Self> {
        if b <= Self::MAX { Some(Self(b)) } else { None }
    }
    const fn to_u8(self) -> u8 {
        self.0
    }
    const fn sub(self, rhs: Self) -> usize {
        (self.0 - rhs.0) as usize
    }
}

#[derive(Clone)]
struct Ptr<'a> {
    buf: &'a [u8],
    idx: usize,
}

impl fmt::Debug for Ptr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        f.debug_struct("Ptr")
            .field("buf", &self.buf.as_ptr())
            .field("idx", &self.idx)
            //.field("idx", &format!("{:#04x}", self.idx))
            .finish()
    }
}

impl<'a> Ptr<'a> {
    fn new(buf: &'a [u8], idx: usize) -> Self {
        Self { buf, idx }
    }
    fn skip(&mut self, count: usize) {
        self.idx += count;
    }
    fn read_u8(&mut self) -> Result<u8> {
        ensure!(self.idx < self.buf.len(), "oob read byte");
        let byte = self.buf[self.idx];
        self.idx += size_of::<u8>();
        Ok(byte)
    }
    fn read_char(&mut self) -> Result<Char> {
        Char::from_u8(self.read_u8()?).ok_or_else(|| eyre!("invalid char"))
    }
    fn read_u32(&mut self) -> Result<u32> {
        let end = self
            .idx
            .checked_add(size_of::<u32>())
            .ok_or_else(|| eyre!("overflow"))?;
        ensure!(end <= self.buf.len(), "oob read u32");
        let word = u32::from_be_bytes(self.buf[self.idx..end].try_into()?);
        self.idx = end;
        Ok(word)
    }
    fn read_cstr(&mut self) -> Result<&'a CStr> {
        ensure!(self.idx < self.buf.len(), "oob read cstr");
        let s = CStr::from_bytes_until_nul(&self.buf[self.idx..])?;
        self.idx += s.count_bytes() + 1;
        Ok(s)
    }
}

#[derive(Debug, Clone, Copy)]
struct Offset(u32);

//impl fmt::Debug for Offset {
//    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
//        f.debug_tuple("Offset")
//            .field(&self.0)
//            .field(&format!("{:#04x}", self.0))
//            .finish()
//    }
//}

impl Offset {
    //const FLAGS: u32 = 0xF0000000;
    const PREFIX: u32 = 0x80000000;
    const VALUES: u32 = 0x40000000;
    const DESC: u32 = 0x20000000;
    const IDX: u32 = 0x0FFFFFFF;

    pub const fn new(v: u32) -> Self {
        Self(v)
    }
    pub const fn idx(&self) -> u32 {
        self.0 & Self::IDX
    }
    pub const fn has_prefix(&self) -> bool {
        self.0 & Self::PREFIX > 0
    }
    pub const fn has_desc(&self) -> bool {
        self.0 & Self::DESC > 0
    }
    pub const fn has_values(&self) -> bool {
        self.0 & Self::VALUES > 0
    }
}

#[derive(Debug, Clone)]
struct RawNode<'a> {
    ptr: Ptr<'a>,
    ost: Offset,
}

impl<'a> RawNode<'a> {
    pub fn new(buf: &'a [u8], ost: u32) -> Result<Self> {
        let ost = Offset::new(ost);
        let idx: usize = ost.idx().try_into()?;
        if idx == 0 || buf.len() <= idx {
            eyre::bail!("oob ptr")
        }
        let ptr = Ptr::new(buf, idx);
        Ok(Self { ptr, ost })
    }
    fn read_node(mut self) -> Result<Node<'a>> {
        let prefix = if self.ost.has_prefix() {
            Some(self.ptr.read_cstr()?)
        } else {
            None
        };

        let desc = if self.ost.has_desc() {
            let first = self.ptr.read_char()?;
            let last = self.ptr.read_char()?;
            let idx = self.ptr.idx;

            let child_count = last
                .to_u8()
                .checked_sub(first.to_u8())
                .ok_or_else(|| eyre!("invalid desc"))?
                + 1;
            self.ptr.skip(size_of::<u32>() * child_count as usize);
            Some(Desc::new(first, last, idx))
        } else {
            None
        };

        let values = if self.ost.has_values() {
            let count = self.ptr.read_u32()?;
            Some(Values::new(count, self.ptr.idx))
        } else {
            None
        };

        Ok(Node::new(self.ptr.buf, prefix, desc, values))
    }
}

#[derive(Debug, Clone, Copy)]
struct Desc<'a> {
    first: Char,
    last: Char,
    idx: usize,
    _ref: PhantomData<&'a ()>,
}

impl Desc<'_> {
    fn new(first: Char, last: Char, idx: usize) -> Self {
        Self {
            first,
            last,
            idx,
            _ref: PhantomData,
        }
    }
}

#[derive(Debug)]
struct Value<'a> {
    priority: u32,
    v: &'a CStr,
}

#[derive(Debug, Clone)]
struct Values<'a> {
    count: u32,
    idx: usize,
    _ref: PhantomData<&'a ()>,
}

#[derive(Clone)]
struct Node<'a> {
    buf: &'a [u8],
    prefix: Option<&'a CStr>,
    desc: Option<Desc<'a>>,
    values: Option<Values<'a>>,
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

impl Values<'_> {
    pub fn new(count: u32, idx: usize) -> Self {
        Self {
            count,
            idx,
            _ref: PhantomData,
        }
    }
}

impl<'a> Node<'a> {
    pub fn new(
        buf: &'a [u8],
        prefix: Option<&'a CStr>,
        desc: Option<Desc<'a>>,
        values: Option<Values<'a>>,
    ) -> Self {
        Self {
            buf,
            prefix,
            desc,
            values,
        }
    }
    fn chop_prefix<'k>(&self, key: &'k [u8]) -> Option<&'k [u8]> {
        key.strip_prefix(self.prefix.unwrap_or_default().to_bytes())
        //if let Some(prefix) = self.prefix {
        //    eprintln!("stripping prefix: {:?}", prefix);
        //    key.strip_prefix(prefix.to_bytes())
        //} else {
        //    eprintln!("no prefix");
        //    Some(key)
        //}
    }
    fn read_child(&self, char: Char) -> Result<Node<'a>> {
        let desc = self.desc.ok_or_else(|| eyre!("no children"))?;
        if desc.first <= char && char <= desc.last {
            let idx = desc.idx + size_of::<u32>() * char.sub(desc.first);
            let mut ptr = Ptr::new(self.buf, idx);
            let ost = ptr.read_u32()?;
            let raw = RawNode::new(self.buf, ost)?;
            raw.read_node()
        } else {
            Err(eyre!("not found"))
        }
    }
    pub fn search(self, key: &[u8]) -> Result<&'a CStr> {
        eprintln!("splitting key {:?}", std::str::from_utf8(key).unwrap());
        let key = self
            .chop_prefix(key)
            .ok_or_else(|| eyre!("prefix mismatch"))?;
        eprintln!("split: {:?}", std::str::from_utf8(key).unwrap());
        if let Some((x, xs)) = key.split_first() {
            let x = Char::from_u8(*x).unwrap();
            let child = self.read_child(x)?;
            child.search(xs)
        } else if let Some(vals) = self.values
            && vals.count > 0
        {
            //todo: rm debug
            assert_eq!(vals.count, 1, "is this true?");
            // ignore priority
            let mut ptr = Ptr::new(self.buf, vals.idx + size_of::<u32>());
            ptr.read_cstr()
        } else {
            Err(eyre!("no values"))
        }
    }
}

fn read_u32(buf: &[u8], idx: usize) -> u32 {
    let end = idx + size_of::<u32>();
    u32::from_be_bytes(buf[idx..end].try_into().unwrap())
}

pub fn mod_deps() -> Result<()> {
    //let uname = rustix::system::uname();
    //let kver = OsStr::from_bytes(uname.release().to_bytes());
    //let deps = Path::new("/lib/modules").join(kver).join("modules.dep.bin");
    let deps = Path::new("./modules").join("modules.dep.bin");
    let f = File::open(deps)?;
    let len: usize = f.metadata()?.len().try_into()?;

    let p = unsafe {
        mmap(
            ptr::null_mut(),
            len,
            ProtFlags::READ,
            MapFlags::PRIVATE,
            f.as_fd(),
            0,
        )
    }?;
    let buf: &[u8] = unsafe { slice::from_raw_parts(p as *const u8, len) };

    let magic: u32 = u32::from_be_bytes(buf[MAGIC_RANGE].try_into()?);
    ensure!(
        magic == INDEX_MAGIC,
        "unrecognized magic bytes: {:02x?}",
        magic.to_le()
    );
    let ver_major = u16::from_be_bytes(buf[VERSION_MAJOR_RANGE].try_into()?);
    ensure!(
        ver_major == INDEX_VERSION_MAJOR,
        "incompatible index major version: {}",
        ver_major
    );

    let root_offset = u32::from_be_bytes(buf[ROOT_OFFSET_RANGE].try_into()?);
    let root_raw = RawNode::new(buf, root_offset)?;
    let root_node = root_raw.read_node()?;
    //let key = "kernel/arch/x86/kvm/kvm-amd.ko.zst";
    //let key = "kernel/mm/zbud.ko.zst"; // no dependencies
    //let key = "kvm_amd";
    //let key = "zbud"; // no dependencies
    let key = "aesni_intel";
    let res = root_node.search(key.as_bytes())?;
    dbg!(res);
    Ok(())
}
