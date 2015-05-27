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

use ncollections::ops::*;

impl<T> Cardinality for Option<T>
{
  type Size = usize;
  fn size(&self) -> usize {
    self.is_some() as usize
  }
}

impl<T> Singleton<T> for Option<T> {
  fn singleton(value: T) -> Option<T> {
    Some(value)
  }
}

impl<T> Empty for Option<T> {
  fn empty() -> Option<T> {
    None
  }
}

impl<T: Bounded> Bounded for Option<T> {
  type Bound = T::Bound;
  fn lower(&self) -> T::Bound {
    debug_assert!(self.is_some(), "Cannot access lower bound on empty `Option` type.");
    self.as_ref().unwrap().lower()
  }
  fn upper(&self) -> T::Bound {
    debug_assert!(self.is_some(), "Cannot access upper bound on empty `Option` type.");
    self.as_ref().unwrap().upper()
  }
}

impl<T: PartialEq+Clone> Intersection for Option<T> {
  type Output = Option<T>;
  fn intersection(&self, other: &Option<T>) -> Option<T> {
    if self.is_empty() || other.is_empty() || self != other {
      None
    }
    else {
      self.clone()
    }
  }
}

impl<T: PartialEq+Clone> Difference for Option<T> {
  type Output = Option<T>;
  fn difference(&self, other: &Option<T>) -> Option<T> {
    if self.is_empty() || self == other {
      None
    }
    else {
      self.clone()
    }
  }
}

impl<T, U> Disjoint<Option<U>> for Option<T> where
  T: Disjoint<U>
{
  fn is_disjoint(&self, other: &Option<U>) -> bool {
    self.is_empty() || other.is_empty() ||
    self.as_ref().unwrap().is_disjoint(other.as_ref().unwrap())
  }
}

impl<U, T> Contains<U> for Option<T> where
  T: Contains<U>
{
  fn contains(&self, value: &U) -> bool {
    self.as_ref().map_or(false, |x| x.contains(value))
  }
}

impl<T, U> Subset<Option<U>> for Option<T> where
  T: Subset<U>
{
  fn is_subset(&self, other: &Option<U>) -> bool {
    if self.is_empty() { true }
    else if other.is_empty() { false }
    else {
      self.as_ref().unwrap().is_subset(other.as_ref().unwrap())
    }
  }
}

impl<T> ProperSubset for Option<T> where
  T: Subset + PartialEq
{
  fn is_proper_subset(&self, other: &Option<T>) -> bool {
    self.is_subset(other) && self != other
  }
}

impl<T> Overlap for Option<T> where
  T: Overlap
{
  fn overlap(&self, other: &Option<T>) -> bool {
    if self.is_empty() || other.is_empty() { false }
    else {
      self.as_ref().unwrap().overlap(other.as_ref().unwrap())
    }
  }
}

fn shrink_if<T, F>(value: &Option<T>, bound: T, cond: F) -> Option<T> where
  T: Ord+Clone,
  F: FnOnce(&T, &T) -> bool
{
  match value {
    &Some(ref x) if cond(x, &bound) => Some(x.clone()),
    _ => None
  }
}

impl<T> ShrinkLeft<T> for Option<T> where
  T: Ord+Clone
{
  fn shrink_left(&self, lb: T) -> Self {
    shrink_if(self, lb, |x, lb| x >= lb)
  }
}

impl<T> ShrinkRight<T> for Option<T> where
  T: Ord+Clone
{
  fn shrink_right(&self, ub: T) -> Self {
    shrink_if(self, ub, |x, ub| x <= ub)
  }
}

impl<T> StrictShrinkLeft<T> for Option<T> where
  T: Ord+Clone
{
  fn strict_shrink_left(&self, lb: T) -> Self {
    shrink_if(self, lb, |x, lb| x > lb)
  }
}

impl<T> StrictShrinkRight<T> for Option<T> where
  T: Ord+Clone
{
  fn strict_shrink_right(&self, ub: T) -> Self {
    shrink_if(self, ub, |x, ub| x < ub)
  }
}

#[allow(non_upper_case_globals)]
#[cfg(test)]
mod tests {
  use ncollections::ops::*;

  const empty: Option<i32> = None;
  const zero: Option<i32> = Some(0);
  const ten: Option<i32> = Some(10);

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
}
