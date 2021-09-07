// Copyright 2015 Pierre Talbot (IRCAM)

// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Interval and bound specific operations.

use gcollections::kind::*;
use num::{Unsigned, Integer};
use num::Bounded as NumBounded;

pub trait Hull<RHS = Self>
{
  type Output;
  fn hull(&self, rhs: &RHS) -> Self::Output;
}

pub trait Range : Collection
{
  fn new(lb: Self::Item, ub: Self::Item) -> Self;
}

pub trait Whole
{
  fn whole() -> Self;
}

/// Limit of a bound for which the distance between `min_value()` and `max_value()` can be represented in the type `Output`.
pub trait Width : Ord + Clone
{
  type Output: Unsigned + Integer + Clone;

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
        <$t as NumBounded>::max_value() - 1
      }

      fn min_value() -> $t {
        <$t as NumBounded>::min_value()
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
        <$t as NumBounded>::max_value()
      }

      fn min_value() -> $t {
        <$t as NumBounded>::min_value() + 1
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

#[allow(non_upper_case_globals)]
#[cfg(test)]
mod tests {
  use super::*;
  use gcollections::ops::*;
  use crate::interval::*;

  #[test]
  fn strict_shrink_left() {
    let empty: Interval<u32> = Interval::empty();
    let i0_10: Interval<u32> = Interval::new(0, 10);
    let i2_10: Interval<u32> = Interval::new(2, 10);

    let ub = u32::max_value();
    assert_eq!(i0_10.strict_shrink_left(ub), empty);
    assert_eq!(i0_10.strict_shrink_left(10u32), empty);
    assert_eq!(i0_10.strict_shrink_left(1u32), i2_10);
  }

  #[test]
  fn strict_shrink_right() {
    let empty: Interval<u32> = Interval::empty();
    let i0_10: Interval<u32> = Interval::new(0, 10);
    let i0_8: Interval<u32> = Interval::new(0, 8);

    let lb = u32::min_value();
    assert_eq!(i0_10.strict_shrink_right(lb), empty);
    assert_eq!(i0_10.strict_shrink_right(0u32), empty);
    assert_eq!(i0_10.strict_shrink_right(9u32), i0_8);
  }
}
