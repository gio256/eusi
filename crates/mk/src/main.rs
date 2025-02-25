use cpio::newc;
use std::fs::File;

fn main() {
    let builder = newc::Builder::new("/init")
        .uid(0)
        .gid(0)
        .mode(0o100755)
        .set_mode_file_type(newc::ModeFileType::Regular);
    let bin = File::open(env!("CARGO_BIN_FILE_EUSI_INIT")).unwrap();
    cpio::write_cpio(std::iter::once((builder, bin)), std::io::stdout()).unwrap();
}
