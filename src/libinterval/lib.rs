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

//! This library proposes structures for interval arithmetics, only interval with integer bounds is supported. A second part of this library defines a bunch of traits for programming generic operations on collections. This part might be moved into another library if it revealed useful, or it might be erased when proper generic support will land in the standard collection.
//!
//! # Examples
//!
//! For examples see the [interval module](interval/index.html) or the [ncollections module](ncollections/index.html).
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

pub mod interval;
pub mod interval_set;
pub mod ops;
pub mod ncollections;

pub use interval::Interval;
pub use interval_set::IntervalSet;
