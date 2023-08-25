//! `stu`pid `bit` library.
//!
//! [![Crates.io](https://img.shields.io/crates/v/stubit)](https://crates.io/crates/stubit)
//! [![Documentation](https://docs.rs/stubit/badge.svg)](https://docs.rs/stubit)
//!
//! Stupid, because it's just a wrapper arround `Vec<bool>` with some helper functions.
//! 
//! ```
//! let mut data = bits![0, 0, 0, 1, 1, 1, 0, 0];
//! assert_eq!(data.to_u8(), Ok(28));
//! 
//! data.push(true);
//! data.push(0);
//! data.push(1);
//! assert_eq!(&data.to_string(), "00011100101");
//! 
//! data.append(vec![1, 1, 0, 1]);
//! assert_eq!(data.to_u8(), Err(93));
//! assert_eq!(data.to_u16(), Ok(3677));
//! ```

use std::{
    fmt::Display,
    ops::{Deref, DerefMut},
};

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub struct Bit(bool);

impl Deref for Bit {
    type Target = bool;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Bit {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl From<bool> for Bit {
    fn from(value: bool) -> Self {
        Bit(value)
    }
}

impl From<Bit> for bool {
    fn from(value: Bit) -> Self {
        value.0
    }
}

macro_rules! impl_from_into_bit {
    ($t:ty) => {
        impl From<$t> for Bit {
            fn from(value: $t) -> Self {
                Bit(if value == 0 { false } else { true })
            }
        }

        impl From<Bit> for $t {
            fn from(value: Bit) -> Self {
                value.0.into()
            }
        }
    };
}

impl_from_into_bit!(i8);
impl_from_into_bit!(i16);
impl_from_into_bit!(i32);
impl_from_into_bit!(i64);
impl_from_into_bit!(i128);
impl_from_into_bit!(isize);
impl_from_into_bit!(u8);
impl_from_into_bit!(u16);
impl_from_into_bit!(u32);
impl_from_into_bit!(u64);
impl_from_into_bit!(u128);
impl_from_into_bit!(usize);

impl Display for Bit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0 {
            write!(f, "1")
        } else {
            write!(f, "0")
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub struct Bits(Vec<Bit>);

impl Bits {
    pub fn new() -> Self {
        Bits::default()
    }
}

impl<T: Into<Bit>> From<Vec<T>> for Bits {
    fn from(value: Vec<T>) -> Self {
        Bits(value.into_iter().map(Into::into).collect())
    }
}

macro_rules! impl_into_bits {
    ($t:ty) => {
        impl From<$t> for Bits {
            fn from(value: $t) -> Self {
                let mut bits = Vec::new();
                for i in 0..<$t>::BITS {
                    let bit = (1 << i) & value;
                    bits.push(bit.into());
                }
                bits.reverse();
                Bits(bits)
            }
        }
    };
}

impl_into_bits!(i8);
impl_into_bits!(i16);
impl_into_bits!(i32);
impl_into_bits!(i64);
impl_into_bits!(i128);
impl_into_bits!(isize);
impl_into_bits!(u8);
impl_into_bits!(u16);
impl_into_bits!(u32);
impl_into_bits!(u64);
impl_into_bits!(u128);
impl_into_bits!(usize);

impl Bits {
    pub fn push(&mut self, value: impl Into<Bit>) {
        self.0.push(value.into());
    }

    pub fn pop(&mut self) -> Option<Bit> {
        self.0.pop()
    }

    pub fn append(&mut self, other: impl Into<Bits>) {
        let mut bits: Bits = other.into();
        self.0.append(&mut bits.0);
    }
}

#[macro_export]
macro_rules! bits {
    ( $( $x:expr ),* ) => {
        {
            let mut bits = Bits::new();
            $(
                bits.push($x);
            )*
            bits
        }
    };
}

impl Deref for Bits {
    type Target = [Bit];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Bits {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Display for Bits {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for i in &self.0 {
            write!(f, "{}", i)?;
        }
        Ok(())
    }
}

macro_rules! convert_bits {
    ($n:ident, $t:ty) => {
        impl Bits {
            /// Converts bits to an integer.
            ///
            /// # Errors
            ///
            /// Returns the value as an error, if there are more bits than fit into the output type.
            pub fn $n(&self) -> Result<$t, $t> {
                let mut val = <$t>::default();
                let mut bits = self.clone();
                bits.reverse();

                for (i, bit) in bits.iter().enumerate() {
                    if i >= <$t>::BITS as usize {
                        return Err(val);
                    }

                    let bit = <$t>::from(*bit);
                    val |= bit << i;
                }
                Ok(val)
            }
        }
    };
}

convert_bits!(to_u8, u8);
convert_bits!(to_u16, u16);
convert_bits!(to_u32, u32);
convert_bits!(to_u64, u64);
convert_bits!(to_u128, u128);
convert_bits!(to_usize, usize);
convert_bits!(to_i8, i8);
convert_bits!(to_i16, i16);
convert_bits!(to_i32, i32);
convert_bits!(to_i64, i64);
convert_bits!(to_i128, i128);
convert_bits!(to_isize, isize);
