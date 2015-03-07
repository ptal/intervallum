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

use std::cmp::{min, max};
use std::num::Int;
use std::fmt::{Formatter, Display, Error};

// Closed interval (endpoints included).
#[derive(Debug, Copy, Clone)]
pub struct Interval<Bound> {
  lb: Bound,
  ub: Bound
}

impl<Bound: Int> Eq for Interval<Bound> {}

impl<Bound: Int> PartialEq<Interval<Bound>> for Interval<Bound>
{
  fn eq(&self, other: &Interval<Bound>) -> bool {
    if self.is_empty() && other.is_empty() { true }
    else { self.lb == other.lb && self.ub == other.ub }
  }
}

impl<Bound: Int> Interval<Bound>
{
  pub fn new(lb: Bound, ub: Bound) -> Interval<Bound> {
    Interval { lb: lb, ub: ub }
  }

  pub fn lower(self) -> Bound { self.lb }

  pub fn upper(self) -> Bound { self.ub }

  pub fn empty() -> Interval<Bound> {
    Interval::new(<Bound as Int>::one(), <Bound as Int>::zero())
  }

  pub fn singleton(x: Bound) -> Interval<Bound> {
    Interval::new(x, x)
  }

  pub fn left_open(ub: Bound) -> Interval<Bound> {
    Interval::new(Int::min_value(), ub)
  }

  pub fn right_open(lb: Bound) -> Interval<Bound> {
    Interval::new(lb, Int::max_value())
  }

  // FIX: Rust limitation, cannot specialize Interval for unsigned types.
  //      Error: multiple declaration of size.
  // Because `abs` is only defined for signed type, we "hardcode" it.
  // TODO: Handle overflow.
  pub fn size(self) -> Bound {
    if self.is_empty() { <Bound as Int>::zero() }
    else {
      let res = self.ub - self.lb + <Bound as Int>::one();
      if res >= <Bound as Int>::zero() { res }
      else { <Bound as Int>::zero() - res }
    }
  }

  pub fn is_singleton(self) -> bool {
    self.lb == self.ub
  }

  pub fn is_empty(self) -> bool {
    self.lb > self.ub
  }

  pub fn has_member(self, x: Bound) -> bool {
    x >= self.lb && x <= self.ub
  }

  pub fn is_subset_of(self, i: Interval<Bound>) -> bool {
    if self.is_empty() { true }
    else {
      self.lb >= i.lb && self.ub <= i.ub
    }
  }

  pub fn is_proper_subset_of(self, i: Interval<Bound>) -> bool {
    self.is_subset_of(i) && self != i
  }

  pub fn intersection(self, i: Interval<Bound>) -> Interval<Bound> {
    Interval::new(
      max(self.lb, i.lb),
      min(self.ub, i.ub)
    )
  }

  pub fn join(self, i: Interval<Bound>) -> Interval<Bound> {
    if self.is_empty() { i }
    else if i.is_empty() { self }
    else {
      Interval::new(
        min(self.lb, i.lb),
        max(self.ub, i.ub)
      )
    }
  }

  // A - B is equivalent to A /\ ~B
  // However the complement operation doesn't make sense here
  // because it'd nearly always ends up to the whole integer interval.
  // Instead we use this equivalence:
  //   A - B is equivalent to:
  //      A /\ [inf,B.lb-1]
  //    \/
  //      A /\ [B.ub+1, inf]
  pub fn difference(self, i: Interval<Bound>) -> Interval<Bound> {
    let left = self.intersection(Interval::left_open(i.lb - <Bound as Int>::one()));
    let right = self.intersection(Interval::right_open(i.ub + <Bound as Int>::one()));
    left.join(right)
  }

  pub fn is_disjoint(self, i: Interval<Bound>) -> bool {
    self.is_empty() || i.is_empty() || self.lb > i.ub || i.lb > self.ub
  }
}

impl<Bound: Display+Int> Display for Interval<Bound> {
  fn fmt(&self, formatter: &mut Formatter) -> Result<(), Error> {
    if self.is_empty() {
      formatter.write_str("{}")
    } else {
      formatter.write_fmt(format_args!("[{}..{}]", self.lb, self.ub))
    }
  }
}

pub trait ToInterval<Bound: Int> {
  fn to_interval(self) -> Interval<Bound>;
}

impl<Bound: Int> ToInterval<Bound> for Interval<Bound> {
  fn to_interval(self) -> Interval<Bound> { self }
}

impl<Bound: Int> ToInterval<Bound> for (Bound, Bound) {
  fn to_interval(self) -> Interval<Bound> {
    let (a, b) = self;
    Interval::new(a, b)
  }
}

impl<Bound: Int> ToInterval<Bound> for () {
  fn to_interval(self) -> Interval<Bound> {
    Interval::empty()
  }
}

impl<Bound: Int> ToInterval<Bound> for Bound {
  fn to_interval(self) -> Interval<Bound> {
    Interval::singleton(self)
  }
}

#[allow(non_upper_case_globals)]
#[cfg(test)]
mod tests {
  use super::*;

  const empty: Interval<i32> = Interval {lb: 1, ub: 0};
  const invalid: Interval<i32> = Interval {lb: 10, ub: -10};
  const zero: Interval<i32> = Interval {lb: 0, ub: 0};
  const one: Interval<i32> = Interval {lb: 1, ub: 1};

  const i1_2: Interval<i32> = Interval {lb: 1, ub: 2};
  const i0_10: Interval<i32> = Interval {lb: 0, ub: 10};
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
    assert_eq!(zero.size(), 1);
    assert_eq!(one.size(), 1);
    assert_eq!(empty.size(), 0);
    assert_eq!(invalid.size(), 0);

    assert_eq!(i1_2.size(), 2);
    assert_eq!(i0_10.size(), 11);
    assert_eq!(im30_m20.size(), 11);
  }

  #[test]
  fn member_test() {
    assert!(i1_2.has_member(1));
    assert!(i1_2.has_member(2));
    assert!(!i1_2.has_member(0));
    assert!(!i1_2.has_member(3));

    assert!(zero.has_member(0));
    assert!(!zero.has_member(1));

    assert!(!empty.has_member(0));
    assert!(!empty.has_member(1));
    assert!(!empty.has_member(5));
    assert!(!empty.has_member(-5));

    assert!(!invalid.has_member(0));
    assert!(!invalid.has_member(-11));
    assert!(!invalid.has_member(11));
  }

  #[test]
  fn is_subset_of_test() {
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
      assert!(x.is_subset_of(y) == r, "{:?} is subset of {:?} is not equal to {:?}", x, y, r);
    }

    for (x,y,(r1,r2)) in sym_cases.into_iter() {
      assert!(x.is_subset_of(y) == r1, "{:?} is subset of {:?} is not equal to {:?}", x, y, r1);
      assert!(y.is_subset_of(x) == r2, "{:?} is subset of {:?} is not equal to {:?}", y, x, r2);
    }
  }

  #[test]
  fn is_proper_subset_of_test() {
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
      assert!(x.is_proper_subset_of(y) == r, "{:?} is proper subset of {:?} is not equal to {:?}", x, y, r);
    }

    for (x,y,(r1,r2)) in sym_cases.into_iter() {
      assert!(x.is_proper_subset_of(y) == r1, "{:?} is proper subset of {:?} is not equal to {:?}", x, y, r1);
      assert!(y.is_proper_subset_of(x) == r2, "{:?} is proper subset of {:?} is not equal to {:?}", y, x, r2);
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
      assert!(x.intersection(y) == r, "{:?} intersection {:?} is not equal to {:?}", x, y, r);
    }

    for (x,y,r) in sym_cases.into_iter() {
      assert!(x.intersection(y) == r, "{:?} intersection {:?} is not equal to {:?}", x, y, r);
      assert!(y.intersection(x) == r, "{:?} intersection {:?} is not equal to {:?}", y, x, r);
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
      assert!(x.join(y) == r, "{:?} join {:?} is not equal to {:?}", x, y, r);
    }

    for (x,y,r) in sym_cases.into_iter() {
      assert!(x.join(y) == r, "{:?} join {:?} is not equal to {:?}", x, y, r);
      assert!(y.join(x) == r, "{:?} join {:?} is not equal to {:?}", y, x, r);
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
      assert!(x.is_disjoint(y) == r, "{:?} is disjoint of {:?} is not equal to {:?}", x, y, r);
    }

    for (x,y,r) in sym_cases.into_iter() {
      assert!(x.is_disjoint(y) == r, "{:?} is disjoint of {:?} is not equal to {:?}", x, y, r);
      assert!(y.is_disjoint(x) == r, "{:?} is disjoint of {:?} is not equal to {:?}", y, x, r);
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
      assert!(x.difference(y) == r, "{:?} diff {:?} is not equal to {:?}", x, y, r);
    }

    for (x,y,(r1,r2)) in sym_cases.into_iter() {
      assert!(x.difference(y) == r1, "{:?} diff {:?} is not equal to {:?}", x, y, r1);
      assert!(y.difference(x) == r2, "{:?} diff {:?} is not equal to {:?}", y, x, r2);
    }
  }

}