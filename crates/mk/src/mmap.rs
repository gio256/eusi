use rustix::{fd::AsFd, mm};
use std::{fmt, fs::File, ops::Deref, ptr, slice};

pub struct Mmap {
    ptr: *mut std::ffi::c_void,
    len: usize,
}

impl Mmap {
    pub fn new(f: File) -> eyre::Result<Self> {
        let len: usize = f.metadata()?.len().try_into()?;
        let ptr = unsafe {
            mm::mmap(
                ptr::null_mut(),
                len,
                mm::ProtFlags::READ,
                mm::MapFlags::PRIVATE,
                f.as_fd(),
                0,
            )
        }?;
        Ok(Self { ptr, len })
    }
}

impl Drop for Mmap {
    fn drop(&mut self) {
        let _ = unsafe { mm::munmap(self.ptr, self.len) };
    }
}

impl Deref for Mmap {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.ptr as *const u8, self.len) }
    }
}

impl fmt::Debug for Mmap {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        f.debug_struct("Mmap")
            .field("ptr", &self.as_ptr())
            .field("len", &self.len)
            .finish()
    }
}
