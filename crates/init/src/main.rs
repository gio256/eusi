use rustix::mount::{MountFlags, mount};
use std::fs;

fn main() {
    println!("starting eusi-init.");

    let tmp_flags = MountFlags::NOSUID | MountFlags::NOEXEC | MountFlags::NODEV;
    fs::create_dir_all("/proc").unwrap();
    mount("proc", "/proc", "proc", tmp_flags, "").unwrap();
    fs::create_dir_all("/sys").unwrap();
    mount("sys", "/sys", "sysfs", tmp_flags, "").unwrap();
    fs::create_dir_all("/dev").unwrap();
    mount("dev", "/dev", "devtmpfs", MountFlags::NOSUID, "mode=0755").unwrap();
    fs::create_dir_all("/run").unwrap();
    mount("run", "/run", "tmpfs", MountFlags::NOSUID | MountFlags::NODEV, "mode=0755").unwrap();

    println!("opened root.");
    std::thread::sleep(std::time::Duration::from_secs(999999999));
}
