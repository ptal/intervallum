// Copyright 2015 Pierre Talbot (IRCAM)

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at

//     http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! This library proposes structures for [interval arithmetic](https://en.wikipedia.org/wiki/Interval_arithmetic), only interval with integer bounds is [currently supported](https://github.com/ptal/rust-interval/issues/5). A second part of this library defines a bunch of traits for programming generic operations on collections. This part might be moved into another library if it proves its usefulness. Or it might be removed when proper generic support will land in the standard collection.
//!
//! # Overflow behavior
//!
//! Nothing special is done against overflow beside the checks done by Rust in debug mode for arithmetic overflows.
//!
//! # Limits
//!
//! Interval bounds must implement, for most operations, the `Width` trait. This is because the maximum size of an n-bits interval can not fit in an n-bits integer. Consider the interval `[0, 1]` with 1-bit bounds, the size `2` can not be represented with only one bit. It needs `n+1` bits, and this is problematic with the largest primitive types such as `u64`. Therefore, the interval bounds must be used within the limits of `Width::min_value()` and `Width::max_value()`, and not by the limits provided by the `Int` trait.
//!
//! # Examples
//!
//! For examples see the [interval module](interval/index.html), [interval set module](interval_set/index.html) or the [ncollections module](ncollections/index.html).
//!
//! # References
//! * [Boost Interval Arithmetic Library](http://www.boost.org/doc/libs/1_57_0/libs/numeric/interval/doc/interval.html)
//! * [Boost Interval Container Library](http://www.boost.org/doc/libs/1_57_0/libs/icl/doc/html/index.html)
//!

#![crate_name = "interval"]
#![unstable]
#![crate_type = "dylib"]

#![feature(core, collections, std_misc)]

extern crate collections;
extern crate num;

pub mod interval;
pub mod interval_set;
pub mod ops;
pub mod ncollections;

pub use interval::Interval;
pub use interval_set::IntervalSet;
