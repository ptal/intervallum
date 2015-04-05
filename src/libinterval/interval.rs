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

//! Closed and bounded generic interval.
//!
//! The bounds of the interval `[i..j]` represents the set of all elements `x` where `i <= x <= j`. Only interval with bound types implementing `Int` is currently available.
//!
//! Most of the operations in `ncollections::ops::*` are implemented. Intervals specific operations, proposed in `ops::*`, are also implemented. There is no `union` operation since this interval representation is not precise enough, thus an union could result in an over-approximation. Consider `[1..2] U [5..6]`, the only possible representation is `[1..6]` which is not exact by the definition of the set union. So this operation is named `hull`.
//!
//! # Examples
//!
//! ```rust
//! use interval::Interval;
//! use interval::ops::*;
//! use interval::ncollections::ops::*;
//!
//! let a = Interval::new(0, 5);
//! let b = Interval::singleton(10);
//!
//! let c = a.hull(&b);
//! let d = c.difference(&a);
//!
//! assert_eq!(c, Interval::new(0,10));
//! assert_eq!(d, Interval::new(6,10));
//! ```
//!
//! # See also
//! [interval set](../interval_set/index.html), [general operations on collection](../ncollections/ops/index.html).

use ncollections::ops::*;
use ops::*;

use std::cmp::{min, max};
use std::num::Int;
use std::fmt::{Formatter, Display, Error};

/// Closed interval (endpoints included).
#[derive(Debug, Copy, Clone)]
pub struct Interval<Bound> {
  lb: Bound,
  ub: Bound
}

impl<Bound: Width+Int> Eq for Interval<Bound> {}

impl<Bound: Width+Int> PartialEq<Interval<Bound>> for Interval<Bound>
{
  fn eq(&self, other: &Interval<Bound>) -> bool {
    if self.is_empty() && other.is_empty() { true }
    else { self.lb == other.lb && self.ub == other.ub }
  }
}

impl<Bound: Width+Int> Interval<Bound>
{
  fn min_lb(ub: Bound) -> Interval<Bound> {
    Interval::new(<Bound as Width>::min_value(), ub)
  }

  fn max_ub(lb: Bound) -> Interval<Bound> {
    Interval::new(lb, <Bound as Width>::max_value())
  }
}

impl<Bound: Width+Int> Range<Bound> for Interval<Bound>
{
  fn new(lb: Bound, ub: Bound) -> Interval<Bound> {
    debug_assert!(lb >= <Bound as Width>::min_value(),
      "Lower bound exceeds the minimum value of a bound.");
    debug_assert!(ub <= <Bound as Width>::max_value(),
      "Upper bound exceeds the maximum value of a bound.");
    Interval { lb: lb, ub: ub }
  }
}

impl<Bound: Int> Bounded for Interval<Bound>
{
  type Bound = Bound;

  fn lower(&self) -> Bound {
    self.lb
  }

  fn upper(&self) -> Bound {
    self.ub
  }
}

impl <Bound: Width+Int> Singleton<Bound> for Interval<Bound>
{
  fn singleton(x: Bound) -> Interval<Bound> {
    Interval::new(x, x)
  }
}

impl<Bound: Width+Int> Empty for Interval<Bound>
{
  fn empty() -> Interval<Bound> {
    Interval::new(Bound::one(), Bound::zero())
  }
}

impl<Bound: Width+Int> Whole for Interval<Bound>
{
  fn whole() -> Interval<Bound> {
    Interval::new(<Bound as Width>::min_value(), <Bound as Width>::max_value())
  }
}

impl<Bound: Width+Int> Cardinality for Interval<Bound>
{
  type Size = <Bound as Width>::Output;
  fn size(&self) -> <Bound as Width>::Output {
    if self.is_empty() { <<Bound as Width>::Output>::zero() }
    else {
      Bound::width(&self.lb, &self.ub)
    }
  }

  fn is_singleton(&self) -> bool {
    self.lb == self.ub
  }

  fn is_empty(&self) -> bool {
    self.lb > self.ub
  }
}

impl<Bound: Width+Int> Disjoint for Interval<Bound>
{
  fn is_disjoint(&self, other: &Interval<Bound>) -> bool {
       self.is_empty() || other.is_empty()
    || self.lb > other.ub || other.lb > self.ub
  }
}

impl<Bound: Int> Disjoint<Bound> for Interval<Bound>
{
  fn is_disjoint(&self, value: &Bound) -> bool {
    !self.contains(value)
  }
}

impl<Bound: Width+Int> Hull for Interval<Bound>
{
  type Output = Interval<Bound>;
  fn hull(&self, other: &Interval<Bound>) -> Interval<Bound> {
    if self.is_empty() { *other }
    else if other.is_empty() { *self }
    else {
      Interval::new(
        min(self.lb, other.lb),
        max(self.ub, other.ub)
      )
    }
  }
}

impl<Bound: Int> Contains<Bound> for Interval<Bound>
{
  fn contains(&self, value: &Bound) -> bool {
    let value = *value;
    value >= self.lb && value <= self.ub
  }
}

impl<Bound: Width+Int> Subset for Interval<Bound>
{
  fn is_subset(&self, other: &Interval<Bound>) -> bool {
    if self.is_empty() { true }
    else {
      self.lb >= other.lb && self.ub <= other.ub
    }
  }
}

impl<Bound: Width+Int> ProperSubset for Interval<Bound>
{
  fn is_proper_subset(&self, other: &Interval<Bound>) -> bool {
    self.is_subset(other) && self != other
  }
}


impl<Bound: Width+Int> Overlap for Interval<Bound>
{
  fn overlap(&self, other: &Interval<Bound>) -> bool {
    !self.is_disjoint(other)
  }
}

impl<Bound: Width+Int> Intersection for Interval<Bound>
{
  type Output = Interval<Bound>;
  fn intersection(&self, other: &Interval<Bound>) -> Interval<Bound> {
    Interval::new(
      max(self.lb, other.lb),
      min(self.ub, other.ub)
    )
  }
}

impl<Bound: Width+Int> Intersection<Bound> for Interval<Bound>
{
  type Output = Interval<Bound>;
  fn intersection(&self, value: &Bound) -> Interval<Bound> {
    if self.contains(value) {
      Interval::singleton(*value)
    }
    else {
      Interval::empty()
    }
  }
}

impl<Bound: Width+Int> Difference for Interval<Bound>
{
  type Output = Interval<Bound>;
  // A - B is equivalent to A /\ ~B
  // However the complement operation doesn't make sense here
  // because it'd nearly always ends up to the whole integer interval.
  // Instead we use this equivalence:
  //   A - B is equivalent to:
  //      A /\ [inf,B.lb-1]
  //    \/
  //      A /\ [B.ub+1, inf]
  fn difference(&self, other: &Interval<Bound>) -> Interval<Bound> {
    let left = self.intersection(&Interval::min_lb(other.lb - Bound::one()));
    let right = self.intersection(&Interval::max_ub(other.ub + Bound::one()));
    left.hull(&right)
  }
}

impl<Bound: Int> Difference<Bound> for Interval<Bound>
{
  type Output = Interval<Bound>;
  fn difference(&self, value: &Bound) -> Interval<Bound> {
    let mut this = *self;
    if *value == this.lb {
      this.lb = this.lb + Bound::one();
    }
    else if *value == this.ub {
      this.ub = this.ub - Bound::one();
    }
    this
  }
}

impl<Bound: Int> ShrinkLeft<Bound> for Interval<Bound>
{
  fn shrink_left(&self, lb: Bound) -> Interval<Bound> {
    let mut this = *self;
    if lb > this.lb {
      this.lb = lb;
    }
    this
  }
}

impl<Bound: Int> ShrinkRight<Bound> for Interval<Bound>
{
  fn shrink_right(&self, ub: Bound) -> Interval<Bound> {
    let mut this = *self;
    if ub < this.ub {
      this.ub = ub;
    }
    this
  }
}

impl<Bound: Display+Width+Int> Display for Interval<Bound>
{
  fn fmt(&self, formatter: &mut Formatter) -> Result<(), Error> {
    if self.is_empty() {
      formatter.write_str("{}")
    } else {
      formatter.write_fmt(format_args!("[{}..{}]", self.lb, self.ub))
    }
  }
}

pub trait ToInterval<Bound> {
  fn to_interval(self) -> Interval<Bound>;
}

impl<Bound> ToInterval<Bound> for Interval<Bound> {
  fn to_interval(self) -> Interval<Bound> { self }
}

impl<Bound: Width+Int> ToInterval<Bound> for (Bound, Bound) {
  fn to_interval(self) -> Interval<Bound> {
    let (a, b) = self;
    Interval::new(a, b)
  }
}

impl<Bound: Width+Int> ToInterval<Bound> for () {
  fn to_interval(self) -> Interval<Bound> {
    Interval::empty()
  }
}

impl<Bound: Width+Int> ToInterval<Bound> for Bound {
  fn to_interval(self) -> Interval<Bound> {
    Interval::singleton(self)
  }
}

#[allow(non_upper_case_globals)]
#[cfg(test)]
mod tests {
  use super::*;
  use ncollections::ops::*;
  use ops::*;

  const empty: Interval<i32> = Interval {lb: 1, ub: 0};
  const invalid: Interval<i32> = Interval {lb: 10, ub: -10};
  const zero: Interval<i32> = Interval {lb: 0, ub: 0};
  const one: Interval<i32> = Interval {lb: 1, ub: 1};
  const ten: Interval<i32> = Interval {lb: 10, ub: 10};

  const i1_2: Interval<i32> = Interval {lb: 1, ub: 2};
  const i0_10: Interval<i32> = Interval {lb: 0, ub: 10};
  const i1_10: Interval<i32> = Interval {lb: 1, ub: 10};
  const i0_9: Interval<i32> = Interval {lb: 0, ub: 9};
  const i0_15: Interval<i32> = Interval {lb: 0, ub: 15};
  const im5_10: Interval<i32> = Interval {lb: -5, ub: 10};
  const im5_m1: Interval<i32> = Interval {lb: -5, ub: -1};
  const i5_10: Interval<i32> = Interval {lb: 5, ub: 10};
  const i6_10: Interval<i32> = Interval {lb: 6, ub: 10};
  const i0_5: Interval<i32> = Interval {lb: 0, ub: 5};
  const i0_4: Interval<i32> = Interval {lb: 0, ub: 4};
  const im5_5: Interval<i32> = Interval {lb: -5, ub: 5};
  const i20_30: Interval<i32> = Interval {lb: 20, ub: 30};
  const im30_m20: Interval<i32> = Interval {lb: -30, ub: -20};

  #[test]
  fn to_interval_id_test() {
    let id = i1_2.clone().to_interval();
    assert_eq!(i1_2, id);
    assert_eq!(i1_2, Interval::new(1, 2));
  }

  #[test]
  fn equality_test() {
    assert_eq!(empty, empty);
    assert_eq!(empty, invalid);
    assert_eq!(invalid, empty);
    assert_eq!(i1_2, i1_2);
  }

  #[test]
  fn size_test() {
    let whole_i32: Interval<i32> = Interval::whole();
    let whole_u32: Interval<u32> = Interval::whole();

    assert_eq!(zero.size(), 1);
    assert_eq!(one.size(), 1);
    assert_eq!(empty.size(), 0);
    assert_eq!(invalid.size(), 0);

    assert_eq!(i1_2.size(), 2);
    assert_eq!(i0_10.size(), 11);
    assert_eq!(im30_m20.size(), 11);

    assert_eq!(whole_i32.size(), u32::max_value());
    assert_eq!(whole_u32.size(), u32::max_value());
  }

  #[test]
  fn contains_test() {
    assert!(i1_2.contains(&1));
    assert!(i1_2.contains(&2));
    assert!(!i1_2.contains(&0));
    assert!(!i1_2.contains(&3));

    assert!(zero.contains(&0));
    assert!(!zero.contains(&1));

    assert!(!empty.contains(&0));
    assert!(!empty.contains(&1));
    assert!(!empty.contains(&5));
    assert!(!empty.contains(&-5));

    assert!(!invalid.contains(&0));
    assert!(!invalid.contains(&-11));
    assert!(!invalid.contains(&11));
  }

  #[test]
  fn is_subset_test() {
    let cases = vec![
      (zero, zero,          true),
      (i1_2, i1_2,          true),
      (empty, empty,        true),
      (invalid, invalid,    true)
    ];

    // For each cases (x, y, res)
    // * x and y are the values
    // * res is a tuple (r, sym) where
    //    * r is true if x is a subset of y
    //    * sym is true if y is a subset of x
    let sym_cases = vec![
      // ||
      // |-|
      (empty, zero,         (true, false)),
      (invalid, zero,       (true, false)),
      (empty, invalid,      (true, true)),
      // ||
      //|--|
      (empty, i1_2,         (true, false)),
      (empty, i0_10,        (true, false)),
      (invalid, i1_2,       (true, false)),
      //  |--|
      // |----|
      (i1_2, i0_10,         (true, false)),
      // |--|
      //     |--|
      (i0_4, i5_10,         (false, false)),
      // |--|
      //    |--|
      (i0_5, i5_10,         (false, false)),
      // |---|
      //   |---|
      (im5_5, i0_10,        (false, false)),
      // |--|
      //         |--|
      (i0_10, i20_30,       (false, false)),
      // |--|
      // |---|
      (i0_10, i0_15,        (true, false)),
      // |---|
      //  |--|
      (im5_10, i0_10,       (false, true))
    ];

    for (x,y,r) in cases.into_iter() {
      assert!(x.is_subset(&y) == r, "{:?} is subset of {:?} is not equal to {:?}", x, y, r);
    }

    for (x,y,(r1,r2)) in sym_cases.into_iter() {
      assert!(x.is_subset(&y) == r1, "{:?} is subset of {:?} is not equal to {:?}", x, y, r1);
      assert!(y.is_subset(&x) == r2, "{:?} is subset of {:?} is not equal to {:?}", y, x, r2);
    }
  }

  #[test]
  fn is_proper_subset_test() {
    let cases = vec![
      (zero, zero,          false),
      (i1_2, i1_2,          false),
      (empty, empty,        false),
      (invalid, invalid,    false)
    ];

    // For each cases (x, y, res)
    // * x and y are the values
    // * res is a tuple (r, sym) where
    //    * r is true if x is a proper subset of y
    //    * sym is true if y is a proper subset of x
    let sym_cases = vec![
      // ||
      // |-|
      (empty, zero,         (true, false)),
      (invalid, zero,       (true, false)),
      (empty, invalid,      (false, false)),
      // ||
      //|--|
      (empty, i1_2,         (true, false)),
      (empty, i0_10,        (true, false)),
      (invalid, i1_2,       (true, false)),
      //  |--|
      // |----|
      (i1_2, i0_10,         (true, false)),
      // |--|
      //     |--|
      (i0_4, i5_10,         (false, false)),
      // |--|
      //    |--|
      (i0_5, i5_10,         (false, false)),
      // |---|
      //   |---|
      (im5_5, i0_10,        (false, false)),
      // |--|
      //         |--|
      (i0_10, i20_30,       (false, false)),
      // |--|
      // |---|
      (i0_10, i0_15,        (true, false)),
      // |---|
      //  |--|
      (im5_10, i0_10,       (false, true))
    ];

    for (x,y,r) in cases.into_iter() {
      assert!(x.is_proper_subset(&y) == r, "{:?} is proper subset of {:?} is not equal to {:?}", x, y, r);
    }

    for (x,y,(r1,r2)) in sym_cases.into_iter() {
      assert!(x.is_proper_subset(&y) == r1, "{:?} is proper subset of {:?} is not equal to {:?}", x, y, r1);
      assert!(y.is_proper_subset(&x) == r2, "{:?} is proper subset of {:?} is not equal to {:?}", y, x, r2);
    }
  }

  #[test]
  fn intersection_test() {
    let cases = vec![
      (zero, zero,          zero),
      (i1_2, i1_2,          i1_2),
      (empty, empty,        empty),
      (invalid, invalid,    invalid)
    ];

    // For each cases (x, y, res)
    // * x and y are the values
    // * res is the expected result, which should be the same
    // for x intersect y and y intersect x since the intersection
    // is commutative.
    let sym_cases = vec![
      // ||
      // |-|
      (empty, zero,         empty),
      (invalid, zero,       empty),
      (empty, invalid,      empty),
      // ||
      //|--|
      (empty, i1_2,         empty),
      (empty, i0_10,        empty),
      (invalid, i1_2,       empty),
      //  |--|
      // |----|
      (i1_2, i0_10,         i1_2),
      // |--|
      //     |--|
      (i0_4, i5_10,         empty),
      // |--|
      //    |--|
      (i0_5, i5_10,         5.to_interval()),
      // |---|
      //   |---|
      (im5_5, i0_10,        (0,5).to_interval()),
      // |--|
      //         |--|
      (i0_10, i20_30,       empty),
      // |--|
      // |---|
      (i0_10, i0_15,        i0_10),
      // |---|
      //  |--|
      (im5_10, i0_10,       i0_10)
    ];

    for (x,y,r) in cases.into_iter() {
      assert!(x.intersection(&y) == r, "{:?} intersection {:?} is not equal to {:?}", x, y, r);
    }

    for (x,y,r) in sym_cases.into_iter() {
      assert!(x.intersection(&y) == r, "{:?} intersection {:?} is not equal to {:?}", x, y, r);
      assert!(y.intersection(&x) == r, "{:?} intersection {:?} is not equal to {:?}", y, x, r);
    }
  }

  #[test]
  fn intersection_value_test() {
    let cases = vec![
      (i0_10, 0, zero),
      (i0_10, 10, ten),
      (i0_10, 1, one),
      (i0_10, 11, empty),
      (i0_10, -1, empty),
      (one, 1, one),
      (one, 0, empty)
    ];
    for (x,y,r) in cases.into_iter() {
      assert!(x.intersection(&y) == r, "{:?} intersection {:?} is not equal to {:?}", x, y, r);
    }
  }

  #[test]
  fn hull_test() {
    let cases = vec![
      (zero, zero,          zero),
      (i1_2, i1_2,          i1_2),
      (empty, empty,        empty),
      (invalid, invalid,    invalid)
    ];

    // For each cases (x, y, res)
    // * x and y are the values
    // * res is the expected result, which should be the same
    // for the union hull of (x,y) or (y,x) since the union hull
    // is commutative.
    let sym_cases = vec![
      // ||
      // |-|
      (empty, zero,         zero),
      (invalid, zero,       zero),
      (empty, invalid,      empty),
      // ||
      //|--|
      (empty, i1_2,         i1_2),
      (empty, i0_10,        i0_10),
      (invalid, i1_2,       i1_2),
      //  |--|
      // |----|
      (i1_2, i0_10,         i0_10),
      // |--|
      //     |--|
      (i0_4, i5_10,         i0_10),
      // |--|
      //    |--|
      (i0_5, i5_10,         i0_10),
      // |---|
      //   |---|
      (im5_5, i0_10,        (-5,10).to_interval()),
      // |--|
      //         |--|
      (i0_10, i20_30,       (0,30).to_interval()),
      // |--|
      // |---|
      (i0_10, i0_15,        i0_15),
      // |---|
      //  |--|
      (im5_10, i0_10,       im5_10)
    ];

    for (x,y,r) in cases.into_iter() {
      assert!(x.hull(&y) == r, "{:?} hull {:?} is not equal to {:?}", x, y, r);
    }

    for (x,y,r) in sym_cases.into_iter() {
      assert!(x.hull(&y) == r, "{:?} hull {:?} is not equal to {:?}", x, y, r);
      assert!(y.hull(&x) == r, "{:?} hull {:?} is not equal to {:?}", y, x, r);
    }
  }

  #[test]
  fn is_disjoint_test() {
    let cases = vec![
      (zero, zero,          false),
      (i1_2, i1_2,          false),
      (empty, empty,        true),
      (invalid, invalid,    true)
    ];

    // For each cases (x, y, res)
    // * x and y are the values
    // * res is the expected result, which should be the same
    // for x is disjoint of y and y is disjoint of x since the
    // disjoint operation is commutative.
    let sym_cases = vec![
      // ||
      // |-|
      (empty, zero,         true),
      (invalid, zero,       true),
      (empty, invalid,      true),
      // ||
      //|--|
      (empty, i1_2,         true),
      (empty, i0_10,        true),
      (invalid, i1_2,       true),
      //  |--|
      // |----|
      (i1_2, i0_10,         false),
      // |--|
      //     |--|
      (i0_4, i5_10,         true),
      // |--|
      //    |--|
      (i0_5, i5_10,         false),
      // |---|
      //   |---|
      (im5_5, i0_10,        false),
      // |--|
      //         |--|
      (i0_10, i20_30,       true),
      // |--|
      // |---|
      (i0_10, i0_15,        false),
      // |---|
      //  |--|
      (im5_10, i0_10,       false)
    ];

    for (x,y,r) in cases.into_iter() {
      assert!(x.is_disjoint(&y) == r, "{:?} is disjoint of {:?} is not equal to {:?}", x, y, r);
      assert!(x.overlap(&y) == !r, "{:?} overlap {:?} is not equal to {:?}", x, y, r);
    }

    for (x,y,r) in sym_cases.into_iter() {
      assert!(x.is_disjoint(&y) == r, "{:?} is disjoint of {:?} is not equal to {:?}", x, y, r);
      assert!(y.is_disjoint(&x) == r, "{:?} is disjoint of {:?} is not equal to {:?}", y, x, r);
      assert!(x.overlap(&y) == !r, "{:?} overlap {:?} is not equal to {:?}", x, y, r);
      assert!(y.overlap(&x) == !r, "{:?} overlap {:?} is not equal to {:?}", y, x, r);
    }
  }

  #[test]
  fn difference_test() {
    let cases = vec![
      (zero, zero,          empty),
      (i1_2, i1_2,          empty),
      (empty, empty,        empty),
      (invalid, invalid,    empty)
    ];

    // For each cases (x, y, res)
    // * x and y are the values
    // * res is a tuple (r, sym) where
    //    * x diff y == r
    //    * y diff x == sym
    let sym_cases = vec![
      // ||
      // |-|
      (empty, zero,         (empty, zero)),
      (invalid, zero,       (empty, zero)),
      (empty, invalid,      (empty, empty)),
      // ||
      //|--|
      (empty, i1_2,         (empty, i1_2)),
      (empty, i0_10,        (empty, i0_10)),
      (invalid, i1_2,       (empty, i1_2)),
      //  |--|
      // |----|
      (i1_2, i0_10,         (empty, i0_10)),
      // |--|
      //     |--|
      (i0_4, i5_10,         (i0_4, i5_10)),
      // |--|
      //    |--|
      (i0_5, i5_10,         ((0,4).to_interval(), i6_10)),
      // |---|
      //   |---|
      (im5_5, i0_10,        (im5_m1, i6_10)),
      // |--|
      //         |--|
      (i0_10, i20_30,       (i0_10, i20_30)),
      // |--|
      // |---|
      (i0_10, i0_15,        (empty, (11,15).to_interval())),
      // |---|
      //  |--|
      (im5_10, i0_10,       (im5_m1, empty))
    ];

    for (x,y,r) in cases.into_iter() {
      assert!(x.difference(&y) == r, "{:?} difference {:?} is not equal to {:?}", x, y, r);
    }

    for (x,y,(r1,r2)) in sym_cases.into_iter() {
      assert!(x.difference(&y) == r1, "{:?} difference {:?} is not equal to {:?}", x, y, r1);
      assert!(y.difference(&x) == r2, "{:?} difference {:?} is not equal to {:?}", y, x, r2);
    }
  }

  #[test]
  fn difference_value_test() {
    let cases = vec![
      (i0_10, 0, i1_10),
      (i0_10, 10, i0_9),
      (i0_10, 1, i0_10),
      (i0_10, 9, i0_10),
      (i0_10, -1, i0_10),
      (i0_10, 11, i0_10),
      (i0_10, 100, i0_10),
      (one, 1, empty)
    ];
    for (x,y,r) in cases.into_iter() {
      assert!(x.difference(&y) == r, "{:?} difference {:?} is not equal to {:?}", x, y, r);
    }
  }

  #[test]
  fn shrink_left_test() {
    let cases = vec![
      (i0_10, -5, i0_10),
      (i0_10, 0, i0_10),
      (i0_10, 1, i1_10),
      (i0_10, 5, i5_10),
      (i0_10, 10, ten),
      (i0_10, 11, empty),
      (i0_10, 100, empty),
      (empty, 0, empty)
    ];
    for (x,y,r) in cases.into_iter() {
      assert!(x.shrink_left(y) == r, "{:?} shrink_left {:?} is not equal to {:?}", x, y, r);
    }
  }

  #[test]
  fn shrink_right_test() {
    let cases = vec![
      (i0_10, 15, i0_10),
      (i0_10, 10, i0_10),
      (i0_10, 9, i0_9),
      (i0_10, 5, i0_5),
      (i0_10, 0, zero),
      (i0_10, -1, empty),
      (i0_10, -100, empty),
      (empty, 0, empty)
    ];
    for (x,y,r) in cases.into_iter() {
      assert!(x.shrink_right(y) == r, "{:?} shrink_right {:?} is not equal to {:?}", x, y, r);
    }
  }
}