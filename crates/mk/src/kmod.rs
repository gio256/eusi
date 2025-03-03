use std::{fs::File, path::Path};

use crate::{index::Index, mmap::Mmap};

// todo:
// - normalize module names

pub fn mod_deps() -> eyre::Result<()> {
    //let uname = rustix::system::uname();
    //let kver = OsStr::from_bytes(uname.release().to_bytes());
    //let deps = Path::new("/lib/modules").join(kver).join("modules.dep.bin");
    //let fp = Path::new("./modules").join("modules.dep.bin");
    //let fp = Path::new("./modules").join("modules.builtin.bin");
    let fp = Path::new("./modules").join("modules.alias.bin");
    let f = File::open(fp)?;
    let buf = Mmap::new(f)?;
    let index = Index::new(&buf)?;

    //let key = "kvm_amd";
    //let key = "twofish";
    //let key = "virtio:d00000009v*";
    let key = "cpu:type:x86,ven0000fam0006mod007E:feature:*";
    //let res = index.find(key.as_bytes())?;
    index.find_wild(key.as_bytes())?;
    //dbg!(res);

    Ok(())
}
