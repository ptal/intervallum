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

//! Interval and bound specific operations.

use num::{Bounded, Unsigned};

pub trait Hull<RHS = Self> {
  type Output;
  fn hull(&self, rhs: &RHS) -> Self::Output;
}

pub trait Range<Bound> {
  fn new(lb: Bound, ub: Bound) -> Self;
}

pub trait Whole {
  fn whole() -> Self;
}

/// Limit of a bound for which the distance between `min_value()` and `max_value()` can be represented in the type `Output`.
pub trait Width : Ord+Clone {
  type Output: Unsigned+PartialOrd+Clone;

  fn max_value() -> Self;
  fn min_value() -> Self;
  /// The result might be infinite depending on the underlying type (think about floating types).
  fn width(lower: &Self, upper: &Self) -> Self::Output;
}

macro_rules! unsigned_width_impl
{
  ( $( $t: ty ),* ) =>
  {$(
    impl Width for $t
    {
      type Output = $t;

      fn max_value() -> $t {
        <$t as Bounded>::max_value() - 1
      }

      fn min_value() -> $t {
        <$t as Bounded>::min_value()
      }

      fn width(lower: &$t, upper: &$t) -> $t {
        let lower = *lower;
        let upper = *upper;
        debug_assert!(upper <= <$t as Width>::max_value(),
          "Width cannot be represented because the value exceeds the maximum value allowed.");
        debug_assert!(lower <= upper);
        upper - lower + 1
      }
    }
  )*}
}

macro_rules! signed_width_impl
{
  ( $( $t: ty, $u: ty ),* ) =>
  {$(
    impl Width for $t
    {
      type Output = $u;

      fn max_value() -> $t {
        <$t as Bounded>::max_value()
      }

      fn min_value() -> $t {
        <$t as Bounded>::min_value() + 1
      }

      fn width(lower: &$t, upper: &$t) -> $u {
        let lower = *lower;
        let upper = *upper;
        debug_assert!(lower >= <$t as Width>::min_value(),
          "Width cannot be represented because the value exceeds the minimum value allowed.");
        debug_assert!(lower <= upper);
        let size =
          // Special case for width that could not be computed within the signed int (it could overflow).
          if lower < 0 && upper > 0 {
            (-lower as $u) + (upper as $u)
          } else {
            (upper - lower) as $u
          };
        size + 1
      }
    }
  )*}
}

unsigned_width_impl!(u8,u16,u32,u64,usize);
signed_width_impl!(i8,u8,i16,u16,i32,u32,i64,u64,isize,usize);
