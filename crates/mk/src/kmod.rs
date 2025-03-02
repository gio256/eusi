use eyre::{Result, ensure, eyre};
use rustix::{
    fd::AsFd,
    mm::{MapFlags, ProtFlags, mmap},
};
use std::ffi::{CStr, CString, OsStr};
use std::fmt;
use std::fs::File;
use std::ops::Deref;
use std::os::unix::ffi::OsStrExt;
use std::path::Path;
use std::{marker::PhantomData, mem::size_of, ops::Range, ptr, slice};

use crate::mmap::Mmap;
use crate::index::Index;


// todo:
// - proper drop impl for calling munmap
// - normalize module names

pub fn mod_deps() -> Result<()> {
    //let uname = rustix::system::uname();
    //let kver = OsStr::from_bytes(uname.release().to_bytes());
    //let deps = Path::new("/lib/modules").join(kver).join("modules.dep.bin");
    let fp = Path::new("./modules").join("modules.dep.bin");
    let f = File::open(fp)?;
    let buf = Mmap::new(f)?;
    let index = Index::new(&buf)?;

    let key = "kvm_amd";
    //let key = "aesni_intel";
    let deps = index.find(key.as_bytes())?;
    dbg!(deps);
    Ok(())
}
