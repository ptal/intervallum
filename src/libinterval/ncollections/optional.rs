// Copyright 2015 Pierre Talbot (IRCAM)

// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use ncollections::ops::*;
use std::ops::*;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Optional<T>
{
  value: Option<T>
}

impl<T> Optional<T>
{
  pub fn wrap(value: Option<T>) -> Optional<T> {
    Optional {
      value: value
    }
  }

  pub fn unwrap(self) -> Option<T> {
    self.value
  }
}

impl<T> Deref for Optional<T>
{
  type Target = Option<T>;

  fn deref<'a>(&'a self) -> &'a Option<T> {
    &self.value
  }
}

impl<T> DerefMut for Optional<T>
{
  fn deref_mut<'a>(&'a mut self) -> &'a mut Option<T> {
    &mut self.value
  }
}


impl<T> Cardinality for Optional<T>
{
  type Size = usize;
  fn size(&self) -> usize {
    self.is_some() as usize
  }
}

impl<T> Singleton<T> for Optional<T> {
  fn singleton(value: T) -> Optional<T> {
    Optional::wrap(Some(value))
  }
}

impl<T> Empty for Optional<T> {
  fn empty() -> Optional<T> {
    Optional::wrap(None)
  }
}

impl<T: Bounded> Bounded for Optional<T> {
  type Bound = T::Bound;
  fn lower(&self) -> T::Bound {
    debug_assert!(!self.is_empty(), "Cannot access lower bound on empty `Option` type.");
    self.as_ref().unwrap().lower()
  }
  fn upper(&self) -> T::Bound {
    debug_assert!(!self.is_empty(), "Cannot access upper bound on empty `Option` type.");
    self.as_ref().unwrap().upper()
  }
}

impl<T: PartialEq+Clone> Intersection for Optional<T> {
  type Output = Optional<T>;
  fn intersection(&self, other: &Optional<T>) -> Optional<T> {
    if self.is_empty() || other.is_empty() || self != other {
      Optional::empty()
    }
    else {
      self.clone()
    }
  }
}

impl<T: PartialEq+Clone> Difference for Optional<T> {
  type Output = Optional<T>;
  fn difference(&self, other: &Optional<T>) -> Optional<T> {
    if self.is_empty() || self == other {
      Optional::empty()
    }
    else {
      self.clone()
    }
  }
}

impl<T: PartialEq+Clone> Intersection<T> for Optional<T> {
  type Output = Optional<T>;
  fn intersection(&self, other: &T) -> Optional<T> {
    if self.is_empty() || self.as_ref().unwrap() != other {
      Optional::empty()
    }
    else {
      self.clone()
    }
  }
}

impl<T: PartialEq+Clone> Difference<T> for Optional<T> {
  type Output = Optional<T>;
  fn difference(&self, other: &T) -> Optional<T> {
    if self.is_empty() || self.as_ref().unwrap() == other {
      Optional::empty()
    }
    else {
      self.clone()
    }
  }
}

macro_rules! integer_optional_set_operations
{
  ( $( $source:ty ),* ) =>
  {$(
    impl Intersection<Optional<$source>> for $source
    {
      type Output = Optional<$source>;
      fn intersection(&self, other: &Optional<$source>) -> Optional<$source> {
        other.intersection(self)
      }
    }

    impl Difference<Optional<$source>> for $source
    {
      type Output = Optional<$source>;

      fn difference(&self, other: &Optional<$source>) -> Optional<$source> {
        if other.is_empty() || self != other.as_ref().unwrap() {
          Optional::singleton(self.clone())
        }
        else {
          Optional::empty()
        }
      }
    }
  )*}
}

integer_optional_set_operations!(i8,u8,i16,u16,i32,u32,i64,u64,isize,usize);

impl<T, U> Disjoint<Optional<U>> for Optional<T> where
  T: Disjoint<U>
{
  fn is_disjoint(&self, other: &Optional<U>) -> bool {
    self.is_empty() || other.is_empty() ||
    self.as_ref().unwrap().is_disjoint(other.as_ref().unwrap())
  }
}

impl<U, T> Contains<U> for Optional<T> where
  T: Contains<U>
{
  fn contains(&self, value: &U) -> bool {
    self.as_ref().map_or(false, |x| x.contains(value))
  }
}

impl<T, U> Subset<Optional<U>> for Optional<T> where
  T: Subset<U>
{
  fn is_subset(&self, other: &Optional<U>) -> bool {
    if self.is_empty() { true }
    else if other.is_empty() { false }
    else {
      self.as_ref().unwrap().is_subset(other.as_ref().unwrap())
    }
  }
}

impl<T> ProperSubset for Optional<T> where
  T: Subset + PartialEq
{
  fn is_proper_subset(&self, other: &Optional<T>) -> bool {
    self.is_subset(other) && self != other
  }
}

impl<T> Overlap for Optional<T> where
  T: Overlap
{
  fn overlap(&self, other: &Optional<T>) -> bool {
    if self.is_empty() || other.is_empty() { false }
    else {
      self.as_ref().unwrap().overlap(other.as_ref().unwrap())
    }
  }
}

fn shrink_if<T, F>(value: &Optional<T>, bound: T, cond: F) -> Optional<T> where
  T: Ord+Clone,
  F: FnOnce(&T, &T) -> bool
{
  match &value.value {
    &Some(ref x) if cond(x, &bound) => Optional::singleton(x.clone()),
    _ => Optional::empty()
  }
}

impl<T> ShrinkLeft<T> for Optional<T> where
  T: Ord+Clone
{
  fn shrink_left(&self, lb: T) -> Self {
    shrink_if(self, lb, |x, lb| x >= lb)
  }
}

impl<T> ShrinkRight<T> for Optional<T> where
  T: Ord+Clone
{
  fn shrink_right(&self, ub: T) -> Self {
    shrink_if(self, ub, |x, ub| x <= ub)
  }
}

impl<T> StrictShrinkLeft<T> for Optional<T> where
  T: Ord+Clone
{
  fn strict_shrink_left(&self, lb: T) -> Self {
    shrink_if(self, lb, |x, lb| x > lb)
  }
}

impl<T> StrictShrinkRight<T> for Optional<T> where
  T: Ord+Clone
{
  fn strict_shrink_right(&self, ub: T) -> Self {
    shrink_if(self, ub, |x, ub| x < ub)
  }
}

fn binary_map<T, F>(x: Optional<T>, y: Optional<T>, f: F) -> Optional<T> where
  F: FnOnce(T, T) -> T
{
  x.unwrap().map_or(Optional::empty(), |x|
    y.unwrap().map_or(Optional::empty(), |y|
      Optional::singleton(f(x, y))))
}

impl<T> Add<Optional<T>> for Optional<T> where
  T: Add<T, Output=T>
{
  type Output = Optional<T>;

  fn add(self, other: Optional<T>) -> Optional<T> {
    binary_map(self, other, T::add)
  }
}

impl<T> Sub<Optional<T>> for Optional<T> where
  T: Sub<T, Output=T>
{
  type Output = Optional<T>;

  fn sub(self, other: Optional<T>) -> Optional<T> {
    binary_map(self, other, T::sub)
  }
}

impl<T> Mul<Optional<T>> for Optional<T> where
  T: Mul<T, Output=T>
{
  type Output = Optional<T>;

  fn mul(self, other: Optional<T>) -> Optional<T> {
    binary_map(self, other, T::mul)
  }
}

fn binary_value_map<T, F>(x: Optional<T>, y: T, f: F) -> Optional<T> where
  F: FnOnce(T, T) -> T
{
  x.unwrap().map_or(Optional::empty(), |x|
      Optional::singleton(f(x, y)))
}

impl<T> Add<T> for Optional<T> where
  T: Add<T, Output=T>
{
  type Output = Optional<T>;

  fn add(self, other: T) -> Optional<T> {
    binary_value_map(self, other, T::add)
  }
}

impl<T> Sub<T> for Optional<T> where
  T: Sub<T, Output=T>
{
  type Output = Optional<T>;

  fn sub(self, other: T) -> Optional<T> {
    binary_value_map(self, other, T::sub)
  }
}

impl<T> Mul<T> for Optional<T> where
  T: Mul<T, Output=T>
{
  type Output = Optional<T>;

  fn mul(self, other: T) -> Optional<T> {
    binary_value_map(self, other, T::mul)
  }
}

macro_rules! integer_optional_arithmetics
{
  ( $( $source:ty ),* ) =>
  {$(
    impl Add<Optional<$source>> for $source
    {
      type Output = Optional<$source>;

      fn add(self, other: Optional<$source>) -> Optional<$source> {
        other.add(self)
      }
    }

    impl Sub<Optional<$source>> for $source
    {
      type Output = Optional<$source>;

      fn sub(self, other: Optional<$source>) -> Optional<$source> {
        binary_value_map(other, self, |x, y| y - x)
      }
    }

    impl Mul<Optional<$source>> for $source
    {
      type Output = Optional<$source>;

      fn mul(self, other: Optional<$source>) -> Optional<$source> {
        other.mul(self)
      }
    }
  )*}
}

integer_optional_arithmetics!(i8,u8,i16,u16,i32,u32,i64,u64,isize,usize);

#[allow(non_upper_case_globals)]
#[cfg(test)]
mod tests {
  use super::*;
  use ncollections::ops::*;

  const empty: Optional<i32> = Optional { value: None };
  const zero: Optional<i32> = Optional { value: Some(0) };
  const ten: Optional<i32> = Optional { value: Some(10) };

  #[test]
  fn cardinality_test() {
    assert_eq!(empty.size(), 0);
    assert_eq!(zero.size(), 1);
    assert_eq!(ten.size(), 1);
    assert!(empty.is_empty());
    assert!(!empty.is_singleton());
    assert!(!zero.is_empty());
    assert!(zero.is_singleton());
  }

  #[test]
  fn constructors_test() {
    assert_eq!(empty, Empty::empty());
    assert_eq!(zero, Singleton::singleton(0));
  }

  #[test]
  fn bound_test() {
    assert_eq!(zero.lower(), 0);
    assert_eq!(zero.upper(), 0);
    assert_eq!(ten.lower(), 10);
    assert_eq!(ten.upper(), 10);
  }

  #[test]
  #[should_panic]
  fn bound_upper_panic_test() {
    empty.upper();
  }

  #[test]
  #[should_panic]
  fn bound_lower_panic_test() {
    empty.lower();
  }

  #[test]
  fn intersection_test() {
    let sym_cases = vec![
      (empty, empty, empty),
      (empty, zero, empty),
      (zero, zero, zero),
      (zero, ten, empty),
      (ten, ten, ten)
    ];

    for (x,y,r) in sym_cases.into_iter() {
      assert!(x.intersection(&y) == r, "{:?} intersection {:?} is not equal to {:?}", x, y, r);
      assert!(y.intersection(&x) == r, "{:?} intersection {:?} is not equal to {:?}", y, x, r);
    }
  }

  #[test]
  fn difference_test() {
    let cases = vec![
      (empty, empty,  empty, empty),
      (empty, zero,   empty, zero),
      (zero, zero,    empty, empty),
      (zero, ten,     zero, ten),
      (ten, ten,      empty, empty)
    ];

    for (x,y,r1,r2) in cases.into_iter() {
      assert!(x.difference(&y) == r1, "{:?} difference {:?} is not equal to {:?}", x, y, r1);
      assert!(y.difference(&x) == r2, "{:?} difference {:?} is not equal to {:?}", y, x, r2);
    }
  }

  #[test]
  fn intersection_value_test() {
    let sym_cases = vec![
      (empty, 0, empty),
      (empty, 1, empty),
      (zero, 0, zero),
      (zero, 1, empty),
      (ten, 10, ten)
    ];

    for (x,y,r) in sym_cases.into_iter() {
      assert!(x.intersection(&y) == r, "{:?} intersection {:?} is not equal to {:?}", x, y, r);
      assert!(y.intersection(&x) == r, "{:?} intersection {:?} is not equal to {:?}", y, x, r);
    }
  }

  #[test]
  fn difference_value_test() {
    let cases = vec![
      (empty, 0,  empty, zero),
      (zero, 0,   empty, empty),
      (zero, 10,  zero, ten),
      (ten,  10,  empty, empty)
    ];

    for (x,y,r1,r2) in cases.into_iter() {
      assert!(x.difference(&y) == r1, "{:?} difference {:?} is not equal to {:?}", x, y, r1);
      assert!(y.difference(&x) == r2, "{:?} difference {:?} is not equal to {:?}", y, x, r2);
    }
  }

  #[test]
  fn is_disjoint_and_overlap_test() {
    let sym_cases = vec![
      (empty, empty, true),
      (empty, zero, true),
      (zero, zero, false),
      (zero, ten, true),
      (ten, ten, false)
    ];

    for (x,y,r) in sym_cases.into_iter() {
      assert!(x.is_disjoint(&y) == r, "{:?} disjoint {:?} is not equal to {:?}", x, y, r);
      assert!(y.is_disjoint(&x) == r, "{:?} disjoint {:?} is not equal to {:?}", y, x, r);
      assert!(x.overlap(&y) == !r, "{:?} overlap {:?} is not equal to {:?}", x, y, !r);
      assert!(y.overlap(&x) == !r, "{:?} overlap {:?} is not equal to {:?}", y, x, !r);
    }
  }

  #[test]
  fn contains_test() {
    let cases = vec![
      (empty, 0, false),
      (empty, 1, false),
      (zero, 0, true),
      (zero, 1, false),
      (ten, 9, false),
      (ten, 10, true)
    ];

    for (x,y,r) in cases.into_iter() {
      assert!(x.contains(&y) == r, "{:?} contains {:?} is not equal to {:?}", x, y, r);
    }
  }

  #[test]
  fn subset_test() {
    let cases = vec![
      (empty, empty,  true, true),
      (empty, zero,   true, false),
      (zero, zero,    true, true),
      (zero, ten,     false, false),
      (ten, ten,      true, true)
    ];

    for (x,y,r1,r2) in cases.into_iter() {
      assert!(x.is_subset(&y) == r1, "{:?} subset {:?} is not equal to {:?}", x, y, r1);
      assert!(y.is_subset(&x) == r2, "{:?} subset {:?} is not equal to {:?}", y, x, r2);
    }
  }

  #[test]
  fn proper_subset_test() {
    let cases = vec![
      (empty, empty,  false, false),
      (empty, zero,   true, false),
      (zero, zero,    false, false),
      (zero, ten,     false, false),
      (ten, ten,      false, false)
    ];

    for (x,y,r1,r2) in cases.into_iter() {
      assert!(x.is_proper_subset(&y) == r1, "{:?} proper_subset {:?} is not equal to {:?}", x, y, r1);
      assert!(y.is_proper_subset(&x) == r2, "{:?} proper_subset {:?} is not equal to {:?}", y, x, r2);
    }
  }

  #[test]
  fn shrink_tests() {
    // First two elements are data. The next are resp. for shrink_left, shrink_right,
    // strict_shrink_left and strict_shrink_right.
    let cases = vec![
      (empty, 0, empty, empty, empty, empty),
      (empty, 1, empty, empty, empty, empty),
      (zero, 0, zero, zero, empty, empty),
      (zero, 1, empty, zero, empty, zero),
      (ten, 9, ten, empty, ten, empty),
      (ten, 10, ten, ten, empty, empty),
      (ten, 11, empty, ten, empty, ten),
    ];

    for (x,y,r1,r2,r3,r4) in cases.into_iter() {
      assert!(x.shrink_left(y) == r1, "{:?} shrink_left {:?} is not equal to {:?}", x, y, r1);
      assert!(x.shrink_right(y) == r2, "{:?} shrink_right {:?} is not equal to {:?}", x, y, r2);
      assert!(x.strict_shrink_left(y) == r3, "{:?} strict_shrink_left {:?} is not equal to {:?}", x, y, r3);
      assert!(x.strict_shrink_right(y) == r4, "{:?} strict_shrink_right {:?} is not equal to {:?}", x, y, r4);
    }
  }

  #[test]
  fn arithmetics_tests() {
    let twenty = Optional::singleton(20);
    let one_hundred = Optional::singleton(100);
    let cases = vec![
      // x,     y,    x+y,   x-y,   x*y
      (empty, empty, empty, empty, empty),
      (empty, ten,   empty, empty, empty),
      (ten,   empty, empty, empty, empty),
      (ten,   zero,  ten,   ten,   zero),
      (ten,   ten,   twenty,zero,  one_hundred)
    ];
    for (x,y,add,sub,mul) in cases.into_iter() {
      assert!(x + y == add, "{:?} + {:?} is not equal to {:?}", x, y, add);
      assert!(x - y == sub, "{:?} - {:?} is not equal to {:?}", x, y, sub);
      assert!(x * y == mul, "{:?} * {:?} is not equal to {:?}", x, y, mul);
    }
  }
}
