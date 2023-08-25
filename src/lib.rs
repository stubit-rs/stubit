//! `stu`pid `bit` library.
//!
//! [![Crates.io](https://img.shields.io/crates/v/stubit)](https://crates.io/crates/stubit)
//! [![Documentation](https://docs.rs/stubit/badge.svg)](https://docs.rs/stubit)
//!
//! *work in progress*
//!

pub trait IntoBit {
    fn into_bit(self) -> usize;
}

impl IntoBit for bool {
    fn into_bit(self) -> usize {
        if self {
            1
        } else {
            0
        }
    }
}

impl IntoBit for usize {
    fn into_bit(self) -> usize {
        self
    }
}

macro_rules! impl_into_bit {
    ($t:ty) => {
        impl IntoBit for $t {
            fn into_bit(self) -> usize {
                if self == 0 {
                    0
                } else {
                    1
                }
            }
        }
    };
}

impl_into_bit!(i8);
impl_into_bit!(i16);
impl_into_bit!(i32);
impl_into_bit!(i64);
impl_into_bit!(i128);
impl_into_bit!(isize);
impl_into_bit!(u8);
impl_into_bit!(u16);
impl_into_bit!(u32);
impl_into_bit!(u64);
impl_into_bit!(u128);

const BITS: usize = usize::BITS as usize;

#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub struct Bits {
    repr: Vec<usize>,
    len: usize,
}

impl Bits {
    pub fn new() -> Self {
        Bits::default()
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn repr(&self) -> &Vec<usize> {
        &self.repr
    }

    pub fn push(&mut self, bit: impl IntoBit) {
        self.len += 1;

        let index = (self.len - 1) / BITS;

        if self.repr.len() < index + 1 {
            self.repr.push(0);
        }

        let mut bit = bit.into_bit();
        if bit == 1 {
            bit <<= (self.len - 1) % BITS;

            if let Some(elem) = self.repr.get_mut(index) {
                *elem |= bit;
            }
        }
    }

    /// Converts [`Bits`] into a [`usize`].
    ///
    /// # Errors
    /// Errors if the conversion would lead to loss of precision.
    ///
    /// [`usize`]: https://doc.rust-lang.org/stable/std/primitive.usize.html
    pub fn try_to_usize(&self) -> Result<usize, ()> {
        if self.repr.len() <= 1 {
            let i = self.repr.first().map(|i| *i);
            Ok(i.unwrap_or(0))
        } else {
            Err(())
        }
    }

    /// Converts [`Bits`] into a [`usize`].
    ///
    /// # Panics
    /// Panics if the conversion would lead to loss of precision.
    ///
    /// [`usize`]: https://doc.rust-lang.org/stable/std/primitive.usize.html
    pub fn to_usize(&self) -> usize {
        self.try_to_usize().expect("loss of precision")
    }
}

impl From<usize> for Bits {
    fn from(value: usize) -> Self {
        Bits {
            repr: vec![value],
            len: 1,
        }
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn it_works() {
//         assert_eq!(4, 4);
//     }
// }
