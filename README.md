# eusi
Early userspace init.

### Usage
```bash
cargo +nightly run -p eusi > target/out
qemu-system-x86_64 -nographic -append "console=ttyS0 nokaslr" -m 512 -kernel /boot/vmlinuz-linux -initrd target/out
```
