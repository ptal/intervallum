// Copyright 2015 Pierre Talbot (IRCAM)

// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! This library proposes structures for [interval arithmetic](https://en.wikipedia.org/wiki/Interval_arithmetic), most [set operations](https://en.wikipedia.org/wiki/Set_%28mathematics%29) are implemented.
//!
//! # Overflow behavior
//!
//! Nothing special is done against overflow beside the checks done by Rust in debug mode for arithmetic overflows.
//!
//! # Limits
//!
//! Interval bounds must implement, for most operations, the `Width` trait. This is because the maximum size of an n-bits interval can not fit in an n-bits integer. Consider the interval `[0..1]` with 1-bit bounds, the size `2` can not be represented with only one bit. It needs `n+1` bits, and this is problematic with the largest primitive types such as `u64`. Therefore, the interval bounds must be used within the limits of `Width::min_value()` and `Width::max_value()`, and not by the limits provided by `num::traits::Bounded`.
//!
//! # Examples
//!
//! For examples see the [interval module](interval/index.html), [interval set module](interval_set/index.html).
//!
//! # References
//! * [Boost Interval Arithmetic Library](http://www.boost.org/doc/libs/1_57_0/libs/numeric/interval/doc/interval.html)
//! * [Boost Interval Container Library](http://www.boost.org/doc/libs/1_57_0/libs/icl/doc/html/index.html)
//! * T.J. Hickey, Qun Ju, and M.H. van Emden. Interval arithmetic: from principles to implementation. Journal of the ACM, 48(5):1038-1068, 2001.
//!

#![feature(specialization)]

extern crate num;
#[macro_use]
extern crate gcollections;

pub mod interval;
pub mod interval_set;
pub mod ops;

pub use interval::Interval;
pub use interval_set::IntervalSet;
