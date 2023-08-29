# stubit

`stu`pid `bit` library.

[![Crates.io](https://img.shields.io/crates/v/stubit)](https://crates.io/crates/stubit)
[![Documentation](https://docs.rs/stubit/badge.svg)](https://docs.rs/stubit)

Stupid, because it's just a wrapper arround `Vec<bool>` with some helper functions.

```rust
let mut data = bits![1, 1, 1, 0];
assert_eq!(data.to_u8(), Ok(14));

data.push(true);
data.push(0);
data.push(1);
assert_eq!(&data.to_string(), "1110101");

let data = Bits::from(255);
assert_eq!(data.to_i32(), Ok(255));
assert_eq!(data.to_u8(), Err(255));
assert_eq!(data.to_i8(), Err(-1));
```
