# eusi
An experiment in [initramfs](https://en.wikipedia.org/wiki/Initial_ramdisk) (initial RAM file system) generation.

### Usage
```bash
cargo +nightly run -p eusi > target/out
qemu-system-x86_64 -nographic -append "console=ttyS0 nokaslr" -m 512 -kernel /boot/vmlinuz-linux -initrd target/out
```
