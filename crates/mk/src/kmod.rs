use std::{
    ffi::OsStr,
    fs::File,
    ops::Deref,
    os::unix::ffi::OsStrExt,
    path::{Path, PathBuf},
};

use thiserror::Error;

use crate::{ascii::chars, index::Index, mmap::Mmap};

const KMOD_INDEX: Kmod<&'static str> = Kmod {
    dep: "modules.dep.bin",
    alias: "modules.alias.bin",
    symbols: "modules.symbols.bin",
    builtin: "modules.builtin.bin",
    builtin_alias: "modules.builtin.alias.bin",
};

// todo:
// - normalize module names
// - logging

#[derive(Debug, Error)]
pub(crate) enum KmodErr {
    #[error("index search failed with {0}")]
    Index(#[from] crate::index::IndexErr),
    #[error("error mapping file: {0}")]
    Mmap(#[from] crate::mmap::MmapErr),
    #[error("IO error: {0}")]
    IO(#[from] std::io::Error),
    #[error(transparent)]
    Ascii(#[from] crate::ascii::AsciiErr),
}

struct Kmod<T> {
    dep: T,
    alias: T,
    symbols: T,
    builtin: T,
    builtin_alias: T,
}

impl Kmod<Mmap> {
    fn map(dir: &Path) -> Result<Self, KmodErr> {
        let dep = mmap_open(&dir.join(KMOD_INDEX.dep))?;
        let alias = mmap_open(&dir.join(KMOD_INDEX.alias))?;
        let symbols = mmap_open(&dir.join(KMOD_INDEX.symbols))?;
        let builtin = mmap_open(&dir.join(KMOD_INDEX.builtin))?;
        let builtin_alias = mmap_open(&dir.join(KMOD_INDEX.builtin_alias))?;
        Ok(Self {
            dep,
            alias,
            symbols,
            builtin,
            builtin_alias,
        })
    }
}

impl<'a> Kmod<Index<'a>> {
    fn index<T>(map: &'a Kmod<T>) -> Result<Self, KmodErr>
    where
        T: Deref<Target = [u8]>,
    {
        let dep = Index::new(&map.dep)?;
        let alias = Index::new(&map.alias)?;
        let symbols = Index::new(&map.symbols)?;
        let builtin = Index::new(&map.builtin)?;
        let builtin_alias = Index::new(&map.builtin_alias)?;
        Ok(Self {
            dep,
            alias,
            symbols,
            builtin,
            builtin_alias,
        })
    }
}

// Joins `path` with the output of `uname -r`.
fn join_uname(path: &Path) -> PathBuf {
    let uname = rustix::system::uname();
    let kver = OsStr::from_bytes(uname.release().to_bytes());
    path.join(kver)
}

fn mmap_open(fp: &Path) -> Result<Mmap, KmodErr> {
    let f = File::open(fp)?;
    Mmap::map(f).map_err(Into::into)
}

fn run(dir: &Path) -> Result<(), KmodErr> {
    let maps = Kmod::map(dir)?;
    let kmod = Kmod::index(&maps)?;

    // modprobe --show-depends kvm-amd
    //let key = "kvm_amd";
    //let res = kmod.dep.find(key.as_bytes())?;
    //dbg!(res);

    //// modprobe --resolve-alias "twofish"
    let key = "twofish";
    //let key = "usb:v152Dp0567d011[4-7]dc*dsc*dp*ic*isc*ip*in*";
    let res = kmod.alias.find_wild(chars(key.as_bytes())?)?;
    dbg!(res);
    Ok(())
}

pub fn mod_deps() -> Result<(), KmodErr> {
    //let module_root = join_uname(Path::new("/lib/modules"));
    let module_root = Path::new("./modules");
    run(module_root)
}
