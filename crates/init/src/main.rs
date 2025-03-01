use eyre::Result;
use rustix::mount::{MountFlags, mount};
use std::{fs, os::unix::process::CommandExt, process::Command};

fn mkmount(src: &str, tgt: &str, fstype: &str, flags: MountFlags, data: &str) -> Result<()> {
    fs::create_dir_all(tgt)?;
    Ok(mount(src, tgt, fstype, flags, data)?)
}

fn main() -> Result<()> {
    println!("starting eusi-init.");

    let proc_sys_flags = MountFlags::NOSUID | MountFlags::NOEXEC | MountFlags::NODEV;
    let run_flags = MountFlags::NOSUID | MountFlags::NODEV;
    mkmount("proc", "/proc", "proc", proc_sys_flags, "")?;
    mkmount("sys", "/sys", "sysfs", proc_sys_flags, "")?;
    mkmount("dev", "/dev", "devtmpfs", MountFlags::NOSUID, "mode=0755")?;
    mkmount("run", "/run", "tmpfs", run_flags, "mode=0755")?;

    println!("dropping to a shell.");
    dbg!(Command::new("/bin/busybox").arg("sh").exec());
    std::thread::sleep(std::time::Duration::from_secs(9999999));
    Ok(())
}
