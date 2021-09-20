Interval Arithmetic Library
===========================

[![Build Status](https://app.travis-ci.com/ptal/intervallum.svg?branch=master)](https://app.travis-ci.com/ptal/intervallum)

Intervallum is a library for computing over arithmetic intervals which compiles on *Rust stable*.
We provide many set operations such as union and intersection.
The intervals can be represented with the `Interval` type which is just a pair of integers (such as `(0,10)`, representing a value in the range 0 to 10), and with a `IntervalSet` which is a vector of intervals (such as `[(0,10), (15,20)]` for all values between 0 and 10, and between 15 and 20).

This library is usable, thoroughly tested and documented, however it only works on integers (`i8`-`i64`, `u8`-`u64`, `usize` and `isize`).
Examples and more in the [documentation](https://docs.rs/intervallum).

## License

Licensed under either of
 * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)
at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you shall be dual licensed as above, without any additional terms or conditions.
