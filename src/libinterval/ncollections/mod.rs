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

//! Wrappers of the standard collection library for generic programming.
//!
//! This module categorizes operations on collections such as sets, tuples, vectors but also interval. The goal is to allow designing generic algorithms by specifying trait bounds on type parameters.
//!
//! It acts as a temporary substitute and will be replaced when proper generic supports will be added on standard collections. To use these operations on standard collections, you must wrap it inside the structure of the same name in `ncollection::*`. This is because some methods have the same name than existing one's.
//!
//! Iteration can't be an operation inside a trait because we'd need higher kinded types (think about `type Output=Iterator<&'a Item>`, `'a` is not defined/accessible inside the trait).
//!
//! # Examples
//!
//! ```rust
//! use interval::ncollections::ops::*;
//! use interval::ncollections::BTreeSet;
//!
//! fn symmetric_difference<A>(a: &A, b: &A) -> A where
//!  A: Intersection<Output=A> + Union<Output=A> + Difference<Output=A>
//! {
//!   let union = a.union(b);
//!   let intersect = a.intersection(b);
//!   union.difference(&intersect)
//! }
//!
//! let a = BTreeSet::wrap([1, 2, 3, 4].iter().cloned().collect());
//! let b = BTreeSet::wrap([3, 4, 5, 6].iter().cloned().collect());
//! let res = BTreeSet::wrap([1, 2, 5, 6].iter().cloned().collect());
//! assert_eq!(*(symmetric_difference(&a, &b)), *res);
//! ```

mod macros;
pub mod hash_set;
pub mod btree_set;
pub mod enum_set;
pub mod bit_set;
pub mod ops;
pub mod optional;
pub mod primitives;

pub use ncollections::hash_set::HashSet;
pub use ncollections::btree_set::BTreeSet;
pub use ncollections::enum_set::EnumSet;
pub use ncollections::bit_set::BitSet;
pub use ncollections::optional::Optional;
