//! `stu`pid `bit` library.
//!
//! [![Crates.io](https://img.shields.io/crates/v/stubit)](https://crates.io/crates/stubit)
//! [![Documentation](https://docs.rs/stubit/badge.svg)](https://docs.rs/stubit)
//!
//! Stupid, because it's just a wrapper arround `Vec<bool>` with some helper functions.
//!
//! ```
//! # use stubit::*;
//! let mut data = bits![1, 1, 1, 0];
//! assert_eq!(data.to_u8(), Ok(14));
//!
//! data.push(true);
//! data.push(0);
//! data.push(1);
//! assert_eq!(&data.to_string(), "1110101");
//!
//! let data = Bits::from(255);
//! assert_eq!(data.to_i32(), Ok(255));
//! assert_eq!(data.to_u8(), Err(255));
//! assert_eq!(data.to_i8(), Err(-1));
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

/// Operate on bits.
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
    };
}

/// Convert bits to integer types.
impl Bits {
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_conversions() {
        assert_eq!(Bits::from(u8::MAX).to_u8(), Ok(u8::MAX));
        assert_eq!(Bits::from(u8::MIN).to_u8(), Ok(u8::MIN));
        assert_eq!(Bits::from(0u16).to_u8(), Err(0));

        assert_eq!(Bits::from(u16::MAX).to_u16(), Ok(u16::MAX));
        assert_eq!(Bits::from(u16::MIN).to_u16(), Ok(u16::MIN));
        assert_eq!(Bits::from(0u32).to_u16(), Err(0));

        assert_eq!(Bits::from(u32::MAX).to_u32(), Ok(u32::MAX));
        assert_eq!(Bits::from(u32::MIN).to_u32(), Ok(u32::MIN));
        assert_eq!(Bits::from(0u64).to_u32(), Err(0));

        assert_eq!(Bits::from(u64::MAX).to_u64(), Ok(u64::MAX));
        assert_eq!(Bits::from(u64::MIN).to_u64(), Ok(u64::MIN));
        assert_eq!(Bits::from(0u128).to_u64(), Err(0));

        assert_eq!(Bits::from(u128::MAX).to_u128(), Ok(u128::MAX));
        assert_eq!(Bits::from(u128::MIN).to_u128(), Ok(u128::MIN));

        assert_eq!(Bits::from(usize::MAX).to_usize(), Ok(usize::MAX));
        assert_eq!(Bits::from(usize::MIN).to_usize(), Ok(usize::MIN));
        assert_eq!(Bits::from(0u128).to_usize(), Err(0));

        assert_eq!(Bits::from(i8::MAX).to_i8(), Ok(i8::MAX));
        assert_eq!(Bits::from(i8::MIN).to_i8(), Ok(i8::MIN));
        assert_eq!(Bits::from(0i16).to_i8(), Err(0));

        assert_eq!(Bits::from(i16::MAX).to_i16(), Ok(i16::MAX));
        assert_eq!(Bits::from(i16::MIN).to_i16(), Ok(i16::MIN));
        assert_eq!(Bits::from(0i32).to_i16(), Err(0));

        assert_eq!(Bits::from(i32::MAX).to_i32(), Ok(i32::MAX));
        assert_eq!(Bits::from(i32::MIN).to_i32(), Ok(i32::MIN));
        assert_eq!(Bits::from(0i64).to_i32(), Err(0));

        assert_eq!(Bits::from(i64::MAX).to_i64(), Ok(i64::MAX));
        assert_eq!(Bits::from(i64::MIN).to_i64(), Ok(i64::MIN));
        assert_eq!(Bits::from(0i128).to_i64(), Err(0));

        assert_eq!(Bits::from(i128::MAX).to_i128(), Ok(i128::MAX));
        assert_eq!(Bits::from(i128::MIN).to_i128(), Ok(i128::MIN));

        assert_eq!(Bits::from(isize::MAX).to_isize(), Ok(isize::MAX));
        assert_eq!(Bits::from(isize::MIN).to_isize(), Ok(isize::MIN));
        assert_eq!(Bits::from(0i128).to_isize(), Err(0));
    }

    #[test]
    fn test_bits_macro() {
        assert_eq!(bits![1, 1, 1, 1, 1, 1, 1, 1].to_string(), "11111111");
        assert_eq!(bits![1, 1, 1, 1, 1, 1, 1, 1].to_u8(), Ok(255));
        assert_eq!(bits![1, 1, 1, 1, 1, 1, 1, 1].to_i8(), Ok(-1));
    }
}
