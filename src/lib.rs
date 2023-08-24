//! `stu`pid `bit` library.
//!
//! [![Crates.io](https://img.shields.io/crates/v/stubit)](https://crates.io/crates/stubit)
//! [![Documentation](https://docs.rs/stubit/badge.svg)](https://docs.rs/stubit)
//!
//! *work in progress*
//!

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub struct Bits {
    repr: Box<[usize]>,
}

impl From<usize> for Bits {
    fn from(value: usize) -> Self {
        Bits {
            repr: Box::new([value]),
        }
    }
}

impl Bits {
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

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn it_works() {
//         assert_eq!(4, 4);
//     }
// }
