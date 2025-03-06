#![feature(let_chains, ascii_char, ascii_char_variants)]
use std::fs::File;

use cpio::newc;

mod ascii;
mod index;
mod kmod;
mod mmap;

// see man 5 modules.dep, man 8 modinfo
fn main() -> eyre::Result<()> {
    let mut fs = vec![];
    let builder = newc::Builder::new("/init")
        .mode(0o0755)
        .set_mode_file_type(newc::ModeFileType::Regular);
    let bin = File::open(env!("CARGO_BIN_FILE_EUSI_INIT"))?;
    fs.push((builder, bin));

    let builder = newc::Builder::new("/bin")
        .mode(0o0755)
        .set_mode_file_type(newc::ModeFileType::Directory);
    let bin = File::open("/dev/null")?;
    fs.push((builder, bin));

    let builder = newc::Builder::new("/bin/busybox")
        .mode(0o0755)
        .set_mode_file_type(newc::ModeFileType::Regular);
    let bin = File::open("/bin/busybox")?;
    fs.push((builder, bin));

    kmod::mod_deps()?;
    cpio::write_cpio(fs.into_iter(), std::io::stdout())?;
    Ok(())
}
