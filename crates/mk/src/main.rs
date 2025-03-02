#![feature(let_chains)]
use cpio::newc;
use std::fs::File;

mod index;
mod kmod;
mod mmap;

// see man 5 modules.dep, man 8 modinfo
fn main() {
    let mut fs = vec![];
    let builder = newc::Builder::new("/init")
        .mode(0o0755)
        .set_mode_file_type(newc::ModeFileType::Regular);
    let bin = File::open(env!("CARGO_BIN_FILE_EUSI_INIT")).unwrap();
    fs.push((builder, bin));

    let builder = newc::Builder::new("/bin")
        .mode(0o0755)
        .set_mode_file_type(newc::ModeFileType::Directory);
    let bin = File::open("/dev/null").unwrap();
    fs.push((builder, bin));

    let builder = newc::Builder::new("/bin/busybox")
        .mode(0o0755)
        .set_mode_file_type(newc::ModeFileType::Regular);
    let bin = File::open("/bin/busybox").unwrap();
    fs.push((builder, bin));

    kmod::mod_deps().unwrap();

    cpio::write_cpio(fs.into_iter(), std::io::stdout()).unwrap();
}
