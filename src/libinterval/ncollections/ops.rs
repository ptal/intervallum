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

//! Generic operations on collection of elements.
//!
//! For general informations, see the [module documentation](../index.html).

use collections::enum_set::CLike;
use std::collections::hash_state::HashState;
use std::hash::Hash;
use std::iter::FromIterator;
use std::default::Default;
use ncollections::{HashSet, BTreeSet, BitSet, EnumSet};
use std::ops::Deref;
use num::{One, Zero, Unsigned};
use num;

// Markers

pub trait IntervalKind {}

// Basic set operations

pub trait Intersection<RHS = Self> {
  type Output;
  fn intersection(&self, rhs: &RHS) -> Self::Output;
}

pub trait Union<RHS = Self> {
  type Output;
  fn union(&self, rhs: &RHS) -> Self::Output;
}

pub trait Difference<RHS = Self> {
  type Output;
  fn difference(&self, rhs: &RHS) -> Self::Output;
}

pub trait SymmetricDifference<RHS = Self> {
  type Output;
  fn symmetric_difference(&self, rhs: &RHS) -> Self::Output;
}

pub trait Complement {
  fn complement(&self) -> Self;
}

macro_rules! set_op_impl
{
  ( $( $t: ident, $m:ident, $v:ident );* ) =>
  {$(
    impl<T> $t for BTreeSet<T>
    where T: Ord+Clone
    {
      type Output = BTreeSet<T>;

      fn $m(&self, other: &BTreeSet<T>) -> BTreeSet<T> {
        BTreeSet::wrap(FromIterator::from_iter(self.deref().$m(other).cloned()))
      }
    }

    impl $t for BitSet {
      type Output = BitSet;

      fn $m(&self, other: &BitSet) -> BitSet {
        let mut new = self.deref().clone();
        new.$v(other);
        BitSet::wrap(new)
      }
    }

    impl<T, S> $t for HashSet<T, S>
    where T: Eq + Hash + Clone,
          S: HashState + Default
    {
      type Output = HashSet<T, S>;

      fn $m(&self, other: &HashSet<T, S>) -> HashSet<T, S> {
        HashSet::wrap(FromIterator::from_iter(self.deref().$m(other).cloned()))
      }
    }
  )*}
}

macro_rules! set_enum_op_impl
{
  ( $( $t: ident, $m:ident, $v:ident );* ) =>
  {$(
    set_op_impl! {$t, $m, $v}

    impl<E: CLike> $t for EnumSet<E>
    {
      type Output = EnumSet<E>;

      fn $m(&self, other: &EnumSet<E>) -> EnumSet<E> {
        EnumSet::wrap(self.deref().$m(**other))
      }
    }
  )*}
}

set_enum_op_impl! {
  Intersection, intersection, intersect_with;
  Union, union, union_with
}

set_op_impl! {
  Difference, difference, difference_with;
  SymmetricDifference, symmetric_difference, symmetric_difference_with
}


// Membership

pub trait Contains<Item> {
  fn contains(&self, value: &Item) -> bool;
}

macro_rules! contains_impl {
  ($t:ty) => {
    fn contains(&self, value: &$t) -> bool {
      self.deref().contains(value)
    }
  }
}

impl<T, S> Contains<T> for HashSet<T, S>
where T: Eq + Hash,
      S: HashState
{
  contains_impl!(T);
}

impl<T: Ord> Contains<T> for BTreeSet<T> {
  contains_impl!(T);
}

impl Contains<usize> for BitSet {
  contains_impl!(usize);
}

impl<E: CLike> Contains<E> for EnumSet<E> {
  contains_impl!(E);
}

pub trait Disjoint<RHS = Self> {
  fn is_disjoint(&self, rhs: &RHS) -> bool;
}

pub trait Subset<RHS = Self> {
  fn is_subset(&self, rhs: &RHS) -> bool;
}

pub trait ProperSubset<RHS = Self> {
  fn is_proper_subset(&self, rhs: &RHS) -> bool;
}

pub trait Overlap<RHS = Self> {
  fn overlap(&self, rhs: &RHS) -> bool;
}

// Other operations

pub trait ShrinkLeft<Bound> {
  fn shrink_left(&self, lb: Bound) -> Self;
}

pub trait ShrinkRight<Bound> {
  fn shrink_right(&self, ub: Bound) -> Self;
}

pub trait StrictShrinkLeft<Bound> {
  fn strict_shrink_left(&self, lb: Bound) -> Self;
}

pub trait StrictShrinkRight<Bound> {
  fn strict_shrink_right(&self, ub: Bound) -> Self;
}

impl<Bound, R> StrictShrinkLeft<Bound> for R where
  Bound: num::PrimInt,
  R: ShrinkLeft<Bound> + Empty + IntervalKind
{
  fn strict_shrink_left(&self, lb: Bound) -> R {
    if lb == Bound::max_value() {
      R::empty()
    } else {
      self.shrink_left(lb + Bound::one())
    }
  }
}

impl<Bound, R> StrictShrinkRight<Bound> for R where
  Bound: num::PrimInt,
  R: ShrinkRight<Bound> + Empty + IntervalKind
{
  fn strict_shrink_right(&self, ub: Bound) -> R {
    if ub == Bound::min_value() {
      R::empty()
    } else {
      self.shrink_right(ub - Bound::one())
    }
  }
}

// Cardinality

pub trait Cardinality {
  type Size : Unsigned;
  fn size(&self) -> Self::Size;

  fn is_singleton(&self) -> bool {
    self.size() == <Self::Size as One>::one()
  }

  fn is_empty(&self) -> bool {
    self.size().is_zero()
  }
}

// Construction

pub trait Empty {
  fn empty() -> Self;
}

pub trait Singleton<Item> {
  fn singleton(value: Item) -> Self;
}

// Bound access

pub trait Bounded
{
  type Bound: PartialOrd;
  fn lower(&self) -> Self::Bound;
  fn upper(&self) -> Self::Bound;
}

#[allow(non_upper_case_globals)]
#[cfg(test)]
mod tests {
  use super::*;
  use interval::*;
  use ops::*;

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