// Copyright 2015 Pierre Talbot (IRCAM)

// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Closed and bounded generic interval.
//!
//! Let `D` be an ordered set and `{i,j} ∈ D`. The interval `I` whose bounds are `{i,j}` is defined as `I = {x ∈ D | i <= x <= j}` and is denoted as `[i..j]`. Only interval with bound types implementing `Num` and `Width` is currently available.
//!
//! Most of the operations in `gcollections::ops::*` are implemented. Intervals specific operations, proposed in `ops::*`, are also implemented. There is no `union` operation since this interval representation is not precise enough, and so an union could be over-approximated. For example, consider `[1..2] U [5..6]`, the only possible representation is `[1..6]` which is not exact by the definition of union of sets. However, this operation exists and is named `hull`.
//!
//! # Examples
//!
//! ```rust
//! extern crate gcollections;
//! extern crate interval;
//!
//! use crate::interval::Interval;
//! use crate::interval::ops::*;
//! use gcollections::ops::*;
//!
//! # fn main() {
//! let a = Interval::new(0, 5);
//! let b = Interval::singleton(10);
//!
//! let c = a.hull(&b);
//! let d = c.difference(&a);
//!
//! assert_eq!(c, Interval::new(0,10));
//! assert_eq!(d, Interval::new(6,10));
//! # }
//! ```
//!
//! # See also
//! [interval set](../interval_set/index.html).

use gcollections::*;
use gcollections::ops::*;
use trilean::SKleene;
use crate::ops::*;

use std::ops::{Add, Sub, Mul};
use std::cmp::{min, max};
use std::fmt::{Formatter, Display, Error};
use num_traits::{Zero, Num};

/// Closed interval (endpoints included).
#[derive(Debug, Copy, Clone)]
pub struct Interval<Bound>
{
  lb: Bound,
  ub: Bound
}

impl<Bound> IntervalKind for Interval<Bound> {}

impl<Bound> Collection for Interval<Bound>
{
  type Item = Bound;
}

impl<Bound> Interval<Bound> where
 Bound: Width + Num
{
  fn into_optional(self) -> Optional<Bound> {
    if self.is_empty() { Optional::empty() }
    else if self.is_singleton() { Optional::singleton(self.lb) }
    else {
      panic!("Only empty interval or singleton can be transformed into an option.");
    }
  }
}

impl<Bound: Width + Num> Eq for Interval<Bound> {}

impl<Bound> PartialEq<Interval<Bound>> for Interval<Bound> where
 Bound: Width + Num
{
  fn eq(&self, other: &Interval<Bound>) -> bool {
    if self.is_empty() && other.is_empty() { true }
    else { self.lb == other.lb && self.ub == other.ub }
  }
}

impl<Bound> Interval<Bound> where
 Bound: Clone
{
  fn low(&self) -> Bound {
    self.lb.clone()
  }
  fn up(&self) -> Bound {
    self.ub.clone()
  }
}

impl<Bound> Interval<Bound> where
 Bound: Width + Num
{
  fn min_lb(ub: Bound) -> Interval<Bound> {
    Interval::new(<Bound as Width>::min_value(), ub)
  }

  fn max_ub(lb: Bound) -> Interval<Bound> {
    Interval::new(lb, <Bound as Width>::max_value())
  }
}

impl<Bound> Range for Interval<Bound> where
 Bound: Width
{
  fn new(lb: Bound, ub: Bound) -> Interval<Bound> {
    debug_assert!(lb >= <Bound as Width>::min_value(),
      "Lower bound exceeds the minimum value of a bound.");
    debug_assert!(ub <= <Bound as Width>::max_value(),
      "Upper bound exceeds the maximum value of a bound.");
    Interval { lb: lb, ub: ub }
  }
}

impl<Bound> Bounded for Interval<Bound> where
 Bound: Num + Width + Clone
{
  fn lower(&self) -> Bound {
    debug_assert!(!self.is_empty(), "Cannot access lower bound on empty interval.");
    self.low()
  }

  fn upper(&self) -> Bound {
    debug_assert!(!self.is_empty(), "Cannot access upper bound on empty interval.");
    self.up()
  }
}

impl<Bound> Singleton for Interval<Bound> where
 Bound: Width + Clone
{
  fn singleton(x: Bound) -> Interval<Bound> {
    Interval::new(x.clone(), x)
  }
}

impl<Bound> Empty for Interval<Bound> where
 Bound: Width + Num
{
  fn empty() -> Interval<Bound> {
    Interval::new(Bound::one(), Bound::zero())
  }
}

impl<Bound> Whole for Interval<Bound> where
 Bound: Width + Num
{
  fn whole() -> Interval<Bound> {
    Interval::new(<Bound as Width>::min_value(), <Bound as Width>::max_value())
  }
}

/// `IsSingleton` and `IsEmpty` are defined automatically in `gcollections`.
impl<Bound> Cardinality for Interval<Bound> where
 Bound: Width + Num
{
  type Size = <Bound as Width>::Output;

  fn size(&self) -> <Bound as Width>::Output {
    if self.lb > self.ub { <<Bound as Width>::Output>::zero() }
    else {
      Bound::width(&self.lb, &self.ub)
    }
  }
}

impl<Bound> Disjoint for Interval<Bound> where
 Bound: Width + Num
{
  fn is_disjoint(&self, other: &Interval<Bound>) -> bool {
       self.is_empty() || other.is_empty()
    || self.lb > other.ub || other.lb > self.ub
  }
}

impl<Bound> Disjoint<Bound> for Interval<Bound> where
 Bound: Num + Ord
{
  fn is_disjoint(&self, value: &Bound) -> bool {
    !self.contains(value)
  }
}

macro_rules! primitive_interval_disjoint
{
  ( $( $source:ty ),* ) =>
  {$(
    impl Disjoint<Interval<$source>> for $source
    {
      fn is_disjoint(&self, value: &Interval<$source>) -> bool {
        value.is_disjoint(self)
      }
    }
  )*}
}

primitive_interval_disjoint!(i8,u8,i16,u16,i32,u32,i64,u64,isize,usize);

impl<Bound> Disjoint<Optional<Bound>> for Interval<Bound> where
 Bound: Num + Ord
{
  fn is_disjoint(&self, value: &Optional<Bound>) -> bool {
    value.as_ref().map_or(true, |x| self.is_disjoint(x))
  }
}

macro_rules! optional_interval_disjoint
{
  ( $( $source:ty ),* ) =>
  {$(
    impl Disjoint<Interval<$source>> for Optional<$source>
    {
      fn is_disjoint(&self, value: &Interval<$source>) -> bool {
        value.is_disjoint(self)
      }
    }
  )*}
}

optional_interval_disjoint!(i8,u8,i16,u16,i32,u32,i64,u64,isize,usize);

impl<Bound> Overlap for Interval<Bound> where
 Bound: Width + Num
{
  fn overlap(&self, other: &Interval<Bound>) -> bool {
    !self.is_disjoint(other)
  }
}

impl<Bound> Overlap<Bound> for Interval<Bound> where
 Bound: Width + Num
{
  fn overlap(&self, other: &Bound) -> bool {
    !self.is_disjoint(other)
  }
}

impl<Bound> Overlap<Optional<Bound>> for Interval<Bound> where
 Bound: Width + Num
{
  fn overlap(&self, other: &Optional<Bound>) -> bool {
    !self.is_disjoint(other)
  }
}

macro_rules! primitive_interval_overlap
{
  ( $( $source:ty ),* ) =>
  {$(
    impl Overlap<Interval<$source>> for $source
    {
      fn overlap(&self, other: &Interval<$source>) -> bool {
        !self.is_disjoint(other)
      }
    }
  )*}
}

primitive_interval_overlap!(i8,u8,i16,u16,i32,u32,i64,u64,isize,usize);

macro_rules! optional_interval_overlap
{
  ( $( $source:ty ),* ) =>
  {$(
    impl Overlap<Interval<$source>> for Optional<$source>
    {
      fn overlap(&self, other: &Interval<$source>) -> bool {
        !self.is_disjoint(other)
      }
    }
  )*}
}

optional_interval_overlap!(i8,u8,i16,u16,i32,u32,i64,u64,isize,usize);

impl<Bound> Hull for Interval<Bound> where
 Bound: Width + Num
{
  type Output = Interval<Bound>;

  fn hull(&self, other: &Interval<Bound>) -> Interval<Bound> {
    if self.is_empty() { other.clone() }
    else if other.is_empty() { self.clone() }
    else {
      Interval::new(
        min(self.low(), other.low()),
        max(self.up(), other.up())
      )
    }
  }
}

impl<Bound> Hull<Bound> for Interval<Bound> where
 Bound: Width + Num
{
  type Output = Interval<Bound>;

  fn hull(&self, other: &Bound) -> Interval<Bound> {
    self.hull(&Interval::singleton(other.clone()))
  }
}

macro_rules! primitive_interval_hull
{
  ( $( $source:ty ),* ) =>
  {$(
    impl Hull<Interval<$source>> for $source
    {
      type Output = Interval<$source>;

      fn hull(&self, other: &Interval<$source>) -> Interval<$source> {
        other.hull(self)
      }
    }
  )*}
}

primitive_interval_hull!(i8,u8,i16,u16,i32,u32,i64,u64,isize,usize);

impl<Bound> Contains for Interval<Bound> where
 Bound: Ord
{
  fn contains(&self, value: &Bound) -> bool {
    value >= &self.lb && value <= &self.ub
  }
}

impl<Bound> Subset for Interval<Bound> where
 Bound: Width + Num
{
  fn is_subset(&self, other: &Interval<Bound>) -> bool {
    if self.is_empty() { true }
    else {
      self.lb >= other.lb && self.ub <= other.ub
    }
  }
}

impl<Bound> ProperSubset for Interval<Bound> where
 Bound: Width + Num
{
  fn is_proper_subset(&self, other: &Interval<Bound>) -> bool {
    self.is_subset(other) && self != other
  }
}

impl<Bound> Intersection for Interval<Bound> where
 Bound: Width + Num
{
  type Output = Interval<Bound>;

  fn intersection(&self, other: &Interval<Bound>) -> Interval<Bound> {
    Interval::new(
      max(self.low(), other.low()),
      min(self.up(), other.up())
    )
  }
}

impl<Bound> Intersection<Bound> for Interval<Bound> where
 Bound: Width + Num
{
  type Output = Interval<Bound>;

  fn intersection(&self, value: &Bound) -> Interval<Bound> {
    if self.contains(value) {
      Interval::singleton(value.clone())
    }
    else {
      Interval::empty()
    }
  }
}

impl<Bound> Intersection<Optional<Bound>> for Interval<Bound> where
 Bound: Width + Num
{
  type Output = Interval<Bound>;

  fn intersection(&self, value: &Optional<Bound>) -> Interval<Bound> {
    value.as_ref().map_or(Interval::empty(), |x| self.intersection(x))
  }
}

macro_rules! optional_interval_intersection
{
  ( $( $source:ty ),* ) =>
  {$(
    impl Intersection<Interval<$source>> for Optional<$source>
    {
      type Output = Optional<$source>;

      fn intersection(&self, other: &Interval<$source>) -> Optional<$source> {
        self.as_ref().map_or(Optional::empty(), |x| other.intersection(x).into_optional())
      }
    }
  )*}
}

optional_interval_intersection!(i8,u8,i16,u16,i32,u32,i64,u64,isize,usize);

impl<Bound> Difference for Interval<Bound> where
 Bound: Width + Num
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
    let left = self.intersection(&Interval::min_lb(other.low() - Bound::one()));
    let right = self.intersection(&Interval::max_ub(other.up() + Bound::one()));
    left.hull(&right)
  }
}

impl<Bound> Difference<Bound> for Interval<Bound> where
 Bound: Num + Clone
{
  type Output = Interval<Bound>;

  fn difference(&self, value: &Bound) -> Interval<Bound> {
    let mut this = self.clone();
    if value == &this.lb {
      this.lb = this.lb + Bound::one();
    }
    else if value == &this.ub {
      this.ub = this.ub - Bound::one();
    }
    this
  }
}

impl<Bound> Difference<Optional<Bound>> for Interval<Bound> where
 Bound: Ord + Num + Clone
{
  type Output = Interval<Bound>;

  fn difference(&self, value: &Optional<Bound>) -> Interval<Bound> {
    value.as_ref().map_or_else(|| self.clone(), |x| self.difference(x))
  }
}

macro_rules! optional_interval_difference
{
  ( $( $source:ty ),* ) =>
  {$(
    impl Difference<Interval<$source>> for Optional<$source>
    {
      type Output = Optional<$source>;

      fn difference(&self, other: &Interval<$source>) -> Optional<$source> {
        self.as_ref().map_or(Optional::empty(), |x|
          if other.contains(x) { Optional::empty() }
          else { Optional::singleton(x.clone()) }
        )
      }
    }
  )*}
}

optional_interval_difference!(i8,u8,i16,u16,i32,u32,i64,u64,isize,usize);

impl<Bound> ShrinkLeft for Interval<Bound> where
 Bound: Num + Width
{
  fn shrink_left(&self, lb: Bound) -> Interval<Bound> {
    let mut this = self.clone();
    if lb > this.lb {
      this.lb = lb;
    }
    this
  }
}

impl<Bound> ShrinkRight for Interval<Bound> where
 Bound: Num + Width
{
  fn shrink_right(&self, ub: Bound) -> Interval<Bound> {
    let mut this = self.clone();
    if ub < this.ub {
      this.ub = ub;
    }
    this
  }
}

forward_all_binop!(impl<Bound: +Num+Width> Add for Interval<Bound>, add);

impl<'a, 'b, Bound> Add<&'b Interval<Bound>> for &'a Interval<Bound> where
 Bound: Num + Width
{
  type Output = Interval<Bound>;

  fn add(self, other: &Interval<Bound>) -> Interval<Bound> {
    if self.is_empty() || other.is_empty() {
      Interval::empty()
    } else {
      Interval::new(self.lower() + other.lower(), self.upper() + other.upper())
    }
  }
}

forward_all_binop!(impl<Bound: +Num+Width+Clone> Add for Interval<Bound>, add, Bound);

impl<'a, 'b, Bound> Add<&'b Bound> for &'a Interval<Bound> where
 Bound: Num + Width + Clone
{
  type Output = Interval<Bound>;

  fn add(self, other: &Bound) -> Interval<Bound> {
    if self.is_empty() {
      Interval::empty()
    }
    else {
      Interval::new(self.lower() + other.clone(), self.upper() + other.clone())
    }
  }
}

forward_all_binop!(impl<Bound: +Num+Width> Sub for Interval<Bound>, sub);

impl<'a, 'b, Bound> Sub<&'b Interval<Bound>> for &'a Interval<Bound> where
 Bound: Num + Width
{
  type Output = Interval<Bound>;

  fn sub(self, other: &Interval<Bound>) -> Interval<Bound> {
    if self.is_empty() || other.is_empty() {
      Interval::empty()
    } else {
      Interval::new(self.lower() - other.upper(), self.upper() - other.lower())
    }
  }
}

forward_all_binop!(impl<Bound: +Num+Width+Clone> Sub for Interval<Bound>, sub, Bound);

impl<'a, 'b, Bound> Sub<&'b Bound> for &'a Interval<Bound> where
 Bound: Num + Width + Clone
{
  type Output = Interval<Bound>;

  fn sub(self, other: &Bound) -> Interval<Bound> {
    if self.is_empty() {
      Interval::empty()
    } else {
      Interval::new(self.lower() - other.clone(), self.upper() - other.clone())
    }
  }
}

forward_all_binop!(impl<Bound: +Num+Width> Mul for Interval<Bound>, mul);

// Adapted from the code found in the Rust compiler sources.
// Rational: min_max was removed.
fn min_max<Iter, Item>(mut iter: Iter) -> (Item, Item) where
 Iter: Iterator<Item=Item>,
 Item: Ord
{
  debug_assert!(iter.size_hint().0 > 2,
    "`min_max` expects an iterator (`iter`) yielding at least two elements.");
  let (mut min, mut max) = {
    let x = iter.next().unwrap();
    let y = iter.next().unwrap();
    if x <= y {(x, y)} else {(y, x)}
  };

  loop {
      // `first` and `second` are the two next elements we want to look
      // at.  We first compare `first` and `second` (#1). The smaller one
      // is then compared to current minimum (#2). The larger one is
      // compared to current maximum (#3). This way we do 3 comparisons
      // for 2 elements.
      let first = match iter.next() {
          None => break,
          Some(x) => x
      };
      let second = match iter.next() {
          None => {
              if first < min {
                  min = first;
              } else if first >= max {
                  max = first;
              }
              break;
          }
          Some(x) => x
      };
      if first <= second {
          if first < min { min = first }
          if second >= max { max = second }
      } else {
          if second < min { min = second }
          if first >= max { max = first }
      }
  }
  (min, max)
}

impl<'a, 'b, Bound> Mul<&'b Interval<Bound>> for &'a Interval<Bound> where
 Bound: Num + Width
{
  type Output = Interval<Bound>;

  // Caution: Consider `[0,1] * [3,5]`, the result `[0,5]` is an over-approximation.
  fn mul(self, other: &Interval<Bound>) -> Interval<Bound> {
    if self.is_empty() || other.is_empty() {
      Interval::empty()
    } else {
      let (min, max) = min_max(vec![
        self.lower() * other.lower(),
        self.lower() * other.upper(),
        self.upper() * other.lower(),
        self.upper() * other.upper()].into_iter());
      Interval::new(min, max)
    }
  }
}

forward_all_binop!(impl<Bound: +Num+Width+Clone> Mul for Interval<Bound>, mul, Bound);

impl<'a, 'b, Bound> Mul<&'b Bound> for &'a Interval<Bound> where
 Bound: Num + Width + Clone
{
  type Output = Interval<Bound>;

  // Caution: Consider `[0,1] * 3`, the result `[0,3]` is an over-approximation.
  fn mul(self, other: &Bound) -> Interval<Bound> {
    if self.is_empty() {
      Interval::empty()
    } else {
      Interval::new(self.lower() * other.clone(), self.upper() * other.clone())
    }
  }
}

impl<Bound> Display for Interval<Bound> where
 Bound: Display + Width + Num
{
  fn fmt(&self, formatter: &mut Formatter) -> Result<(), Error> {
    if self.is_empty() {
      formatter.write_str("{}")
    } else {
      formatter.write_fmt(format_args!("[{}..{}]", self.lb, self.ub))
    }
  }
}

pub trait ToInterval<Bound>
{
  fn to_interval(self) -> Interval<Bound>;
}

impl<Bound> ToInterval<Bound> for Interval<Bound>
{
  fn to_interval(self) -> Interval<Bound> { self }
}

impl<Bound: Width+Num> ToInterval<Bound> for (Bound, Bound)
{
  fn to_interval(self) -> Interval<Bound> {
    let (a, b) = self;
    Interval::new(a, b)
  }
}

impl<Bound: Width+Num> ToInterval<Bound> for ()
{
  fn to_interval(self) -> Interval<Bound> {
    Interval::empty()
  }
}

impl<Bound: Width+Num> ToInterval<Bound> for Bound
{
  fn to_interval(self) -> Interval<Bound> {
    Interval::singleton(self)
  }
}

impl<Bound> Join for Interval<Bound> where
 Bound: Width + Num
{
  fn join(self, other: Interval<Bound>) -> Interval<Bound> {
    self.intersection(&other)
  }
}

impl<Bound> Meet for Interval<Bound> where
 Bound: Width + Num
{
  fn meet(self, other: Interval<Bound>) -> Interval<Bound> {
    self.hull(&other)
  }
}

impl<Bound> Entailment for Interval<Bound> where
 Bound: Width + Num
{
  fn entail(&self, other: &Interval<Bound>) -> SKleene {
    if self.is_subset(other) {
      SKleene::True
    }
    else if other.is_subset(self) {
      SKleene::False
    }
    else {
      SKleene::Unknown
    }
  }
}

impl<Bound> Top for Interval<Bound> where
 Bound: Width + Num
{
  fn top() -> Interval<Bound> {
    Interval::empty()
  }
}

impl<Bound> Bot for Interval<Bound> where
 Bound: Width + Num
{
  fn bot() -> Interval<Bound> {
    Interval::whole()
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
  const ten: Interval<i32> = Interval {lb: 10, ub: 10};

  const i0_1: Interval<i32> = Interval {lb: 0, ub: 1};
  const i0_2: Interval<i32> = Interval {lb: 0, ub: 2};
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
  fn intersection_value_optional_test() {
    let cases = vec![
      (1, empty, None,      empty, None),
      (2, invalid, None,    empty, None),
      (3, empty, Some(1),   empty, None),
      (4, i0_10, None,      empty, None),
      (5, i0_10, Some(0),   zero, Some(0)),
      (6, i0_10, Some(10),  ten, Some(10)),
      (7, i0_10, Some(1),   one, Some(1)),
      (8, i0_10, Some(-1),  empty, None),
      (9, i0_10, Some(11),  empty, None),
      (10, one, Some(0),    empty, None),
      (11, one, Some(1),    one, Some(1)),
    ];
    for (id,x,y,r1,r2) in cases.into_iter() {
      let y = y.map_or(Optional::empty(), |y| Optional::singleton(y));
      let r2 = r2.map_or(Optional::empty(), |r2| Optional::singleton(r2));
      // Interval /\ Value.
      if !y.is_empty() {
        assert!(x.intersection(y.as_ref().unwrap()) == r1,
          "Test#{}: {:?} intersection {:?} is not equal to {:?}", id, x, y.as_ref().unwrap(), r1);
      }
      // Interval /\ Option<T>
      assert!(x.intersection(&y) == r1, "Test#{}: {:?} intersection {:?} is not equal to {:?}", id, x, y, r1);
      // Option<T> /\ Interval
      assert!(y.intersection(&x) == r2, "Test#{}: {:?} intersection {:?} is not equal to {:?}", id, y, x, r2);
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

  fn is_disjoint_cases() -> Vec<(u32, Interval<i32>, i32, bool)> {
    vec![
      (1, empty, 0, true),
      (2, invalid, 0, true),
      (3, i0_4, -1, true),
      (4, i0_4, 0, false),
      (5, i0_4, 2, false),
      (6, i0_4, 3, false),
      (7, i0_4, 5, true)
    ]
  }

  #[test]
  fn is_disjoint_bound_test() {
    let cases = is_disjoint_cases();
    for (id, x,y,r) in cases.into_iter() {
      assert!(x.is_disjoint(&y) == r, "Test#{}: {:?} is disjoint of {:?} is not equal to {:?}", id, x, y, r);
      assert!(y.is_disjoint(&x) == r, "Test#{}: {:?} is disjoint of {:?} is not equal to {:?}", id, y, x, r);
      assert!(x.overlap(&y) == !r, "Test#{}: {:?} overlap {:?} is not equal to {:?}", id, x, y, !r);
      assert!(y.overlap(&x) == !r, "Test#{}: {:?} overlap {:?} is not equal to {:?}", id, y, x, !r);
    }
  }

  #[test]
  fn is_disjoint_option_test() {
    let mut cases: Vec<(u32, Interval<i32>, Optional<i32>, bool)> = is_disjoint_cases().into_iter()
      .map(|(id,a,b,e)| (id, a, Optional::singleton(b), e))
      .collect();
    cases.extend(vec![
      (8, empty, Optional::empty(), true),
      (9, invalid, Optional::empty(), true),
      (10, i0_4, Optional::empty(), true)
    ]);
    for (id, x,y,r) in cases.into_iter() {
      assert!(x.is_disjoint(&y) == r, "Test#{}: {:?} is disjoint of {:?} is not equal to {:?}", id, x, y, r);
      assert!(y.is_disjoint(&x) == r, "Test#{}: {:?} is disjoint of {:?} is not equal to {:?}", id, y, x, r);
      assert!(x.overlap(&y) == !r, "Test#{}: {:?} overlap {:?} is not equal to {:?}", id, x, y, !r);
      assert!(y.overlap(&x) == !r, "Test#{}: {:?} overlap {:?} is not equal to {:?}", id, y, x, !r);
    }
  }

  #[test]
  fn difference_test() {
    let cases = vec![
      (1, zero, zero,          empty),
      (2, i1_2, i1_2,          empty),
      (3, empty, empty,        empty),
      (4, invalid, invalid,    empty)
    ];

    // For each cases (x, y, res)
    // * x and y are the values
    // * res is a tuple (r, sym) where
    //    * x diff y == r
    //    * y diff x == sym
    let sym_cases = vec![
      // ||
      // |-|
      (5, empty, zero,         (empty, zero)),
      (6, invalid, zero,       (empty, zero)),
      (7, empty, invalid,      (empty, empty)),
      // ||
      //|--|
      (8, empty, i1_2,         (empty, i1_2)),
      (9, empty, i0_10,        (empty, i0_10)),
      (10, invalid, i1_2,       (empty, i1_2)),
      //  |--|
      // |----|
      (11, i1_2, i0_10,         (empty, i0_10)),
      // |--|
      //     |--|
      (12, i0_4, i5_10,         (i0_4, i5_10)),
      // |--|
      //    |--|
      (13, i0_5, i5_10,         ((0,4).to_interval(), i6_10)),
      // |---|
      //   |---|
      (14, im5_5, i0_10,        (im5_m1, i6_10)),
      // |--|
      //         |--|
      (15, i0_10, i20_30,       (i0_10, i20_30)),
      // |--|
      // |---|
      (16, i0_10, i0_15,        (empty, (11,15).to_interval())),
      // |---|
      //  |--|
      (17, im5_10, i0_10,       (im5_m1, empty))
    ];

    for (id,x,y,r) in cases.into_iter() {
      println!("Test #{}", id);
      assert!(x.difference(&y) == r, "{:?} difference {:?} is not equal to {:?}", x, y, r);
    }

    for (id,x,y,(r1,r2)) in sym_cases.into_iter() {
      println!("Test #{}", id);
      assert!(x.difference(&y) == r1, "{:?} difference {:?} is not equal to {:?}", x, y, r1);
      assert!(y.difference(&x) == r2, "{:?} difference {:?} is not equal to {:?}", y, x, r2);
    }
  }

  #[test]
  fn difference_value_option_test() {
    let cases = vec![
      (1, empty, None,      empty, None),
      (2, invalid, None,    empty, None),
      (3, empty, Some(1),   empty, Some(1)),
      (4, i0_10, None,      i0_10, None),
      (5, i0_10, Some(0),   i1_10, None),
      (6, i0_10, Some(10),  i0_9, None),
      (7, i0_10, Some(1),   i0_10, None),
      (8, i0_10, Some(9),   i0_10, None),
      (9, i0_10, Some(-1),  i0_10, Some(-1)),
      (10, i0_10, Some(11), i0_10, Some(11)),
      (11, i0_10, Some(100),i0_10, Some(100)),
      (12, one, Some(1),    empty, None),
    ];
    for (id,x,y,r1,r2) in cases.into_iter() {
      let y = y.map_or(Optional::empty(), |y| Optional::singleton(y));
      let r2 = r2.map_or(Optional::empty(), |r2| Optional::singleton(r2));
      // Interval - Value.
      if y.is_some() {
        assert!(x.difference(y.as_ref().unwrap()) == r1,
          "Test#{}: {:?} difference {:?} is not equal to {:?}", id, x, y.as_ref().unwrap(), r1);
      }
      // Interval - Option<T>
      assert!(x.difference(&y) == r1, "Test#{}: {:?} difference {:?} is not equal to {:?}", id, x, y, r1);
      // Option<T> - Interval
      assert!(y.difference(&x) == r2, "Test#{}: {:?} difference {:?} is not equal to {:?}", id, y, x, r2);
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

  #[test]
  fn add_sub_mul_bound_test() {
    // For each cases (x, y, r1, r2, r3)
    // * x and y are the values
    // * r1,r2 and r3 are the results of `x + y`, `x - y` and `x * y`
    let cases = vec![
      (zero, 0,      zero, zero, zero),
      (i1_2, 0,      i1_2, i1_2, zero),
      (empty, 0,     empty, empty, empty),
      (invalid, 0,   empty, empty, empty),
      (zero, 1,      one, (-1,-1).to_interval(), zero),
      (i1_2, 1,      (2,3).to_interval(), (0,1).to_interval(), i1_2),
      (empty, 1,     empty, empty, empty),
      (invalid, 1,   empty, empty, empty),
      (zero, 3,      (3,3).to_interval(), (-3,-3).to_interval(), zero),
      (i1_2, 3,      (4,5).to_interval(), (-2,-1).to_interval(), (3, 6).to_interval()),
      (empty, 3,     empty, empty, empty),
      (invalid, 3,   empty, empty, empty),
    ];

    for &(x,y,r1,r2,r3) in &cases {
      assert!(x + y == r1, "{:?} + {:?} is not equal to {:?}", x, y, r1);
      assert!(x - y == r2, "{:?} - {:?} is not equal to {:?}", x, y, r2);
      assert!(x * y == r3, "{:?} * {:?} is not equal to {:?}", x, y, r3);
    }
  }


  #[test]
  fn add_test() {
    // For each cases (x, y, res)
    // * x and y are the values
    // * res is the result of `x + y`
    let sym_cases = vec![
      (zero, zero,          zero),
      (i1_2, i1_2,          (2, 4).to_interval()),
      (empty, empty,        empty),
      (invalid, invalid,    empty),
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
      (zero, i0_10,         i0_10),
      (i1_2, i0_10,         (1,12).to_interval()),
      (im5_10, i0_10,       (-5,20).to_interval()),
      (im5_10, im30_m20,    (-35,-10).to_interval())
    ];

    for &(x,y,r) in &sym_cases {
      assert!(x + y == r, "{:?} + {:?} is not equal to {:?}", x, y, r);
      assert!(y + x == r, "{:?} + {:?} is not equal to {:?}", y, x, r);
    }
  }

  #[test]
  fn sub_test() {
    // For each cases (x, y, res)
    // * x and y are the values
    // * res is the result of `x - y`
    let cases = vec![
      (zero, zero,          zero),
      (i1_2, i1_2,          (-1, 1).to_interval()),
      (empty, empty,        empty),
      (invalid, invalid,    empty),
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
    ];

    // For each cases (x, y, (res1, res2))
    // * x and y are the values
    // * res1 is the result of `x - y` and res2 of `y - x`
    let sym_cases = vec![
      (zero, i0_10,       ((-10,0), (0,10))),
      (i1_2, i0_10,       ((-9,2), (-2, 9))),
      (im5_10, i0_10,     ((-15,10), (-10, 15))),
      (im5_10, im30_m20,  ((15,40), (-40,-15)))
    ];

    for &(x,y,r) in &cases {
      assert!(x - y == r, "{:?} - {:?} is not equal to {:?}", x, y, r);
      assert!(y - x == r, "{:?} - {:?} is not equal to {:?}", y, x, r);
    }

    for &(x,y,(r1, r2)) in &sym_cases {
      let r1 = r1.to_interval();
      let r2 = r2.to_interval();
      assert!(x - y == r1, "{:?} - {:?} is not equal to {:?}", x, y, r1);
      assert!(y - x == r2, "{:?} - {:?} is not equal to {:?}", y, x, r2);
    }
  }

  #[test]
  fn mul_test() {
    // For each cases (x, y, res)
    // * x and y are the values
    // * res is the result of `x * y`
    let sym_cases = vec![
      (zero, zero,          zero),
      (i1_2, i1_2,          (1, 4).to_interval()),
      (empty, empty,        empty),
      (invalid, invalid,    empty),
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
      (zero, i0_10,         zero),
      (one, i0_10,          i0_10),
      (i1_2, i0_10,         (0,20).to_interval()),
      (im5_10, i0_10,       (-50,100).to_interval()),
      (im5_10, im30_m20,    (-300,150).to_interval())
    ];

    for &(x,y,r) in &sym_cases {
      assert!(x * y == r, "{:?} * {:?} is not equal to {:?}", x, y, r);
      assert!(y * x == r, "{:?} * {:?} is not equal to {:?}", y, x, r);
    }
  }

  #[test]
  fn test_lattice() {
    use gcollections::ops::lattice::test::*;
    use trilean::SKleene::*;
    let whole = Interval::<i32>::whole();
    let tester = LatticeTester::new(
      0,
      /* data_a */  vec![empty, empty, whole, zero, zero,    zero,   i1_2, i0_10,  im5_5],
      /* data_b */  vec![zero,  whole, empty, zero, one,     i1_2,   i0_10,im5_5,  i6_10],
      /* a |= b*/   vec![True,  True,  False, True, Unknown, Unknown,True, Unknown,Unknown],
      /* a |_| b */ vec![empty, empty, empty, zero, empty,   empty,  i1_2, i0_5,   empty],
      /* a |-| b */ vec![zero,  whole, whole, zero, i0_1,    i0_2,   i0_10,im5_10, im5_10]
    );
    tester.test_all();
  }
}
