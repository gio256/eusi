use std::ascii::Char;

use thiserror::Error;

const ASCII_MAX: u8 = 127;

#[derive(Debug, Error)]
#[error("invalid ascii byte at index {index}")]
pub(crate) struct AsciiErr {
    index: usize,
}

//todo
fn run_ascii_validation(v: &[u8]) -> Result<(), AsciiErr> {
    if let Some(index) = v.iter().position(|&b| b > ASCII_MAX) {
        Err(AsciiErr { index })
    } else {
        Ok(())
    }
}

pub(crate) fn chars(v: &[u8]) -> Result<&[Char], AsciiErr> {
    match run_ascii_validation(v) {
        Ok(_) => Ok(unsafe { chars_unchecked(v) }),
        Err(err) => Err(err),
    }
}

unsafe fn chars_unchecked(v: &[u8]) -> &[Char] {
    unsafe { std::mem::transmute(v) }
}
