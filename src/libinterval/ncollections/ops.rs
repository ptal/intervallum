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

use collections::enum_set::CLike;
use std::collections::hash_state::HashState;
use std::hash::Hash;
use std::iter::FromIterator;
use std::default::Default;
use std::num::Int;
use ncollections::{HashSet, BTreeSet, BitSet, EnumSet};
use std::ops::{Deref, DerefMut};

// Basic set operations

pub trait Intersection<RHS = Self> {
  type Output;
  fn intersection(self, rhs: RHS) -> Self::Output;
}

pub trait Union<RHS = Self> {
  type Output;
  fn union(self, rhs: RHS) -> Self::Output;
}

pub trait Difference<RHS = Self> {
  type Output;
  fn difference(self, rhs: RHS) -> Self::Output;
}

pub trait SymmetricDifference<RHS = Self> {
  type Output;
  fn symmetric_difference(self, rhs: RHS) -> Self::Output;
}

macro_rules! set_op_impl
{
  ( $( $t: ident, $m:ident, $v:ident );* ) =>
  {$(
    impl<T> $t for BTreeSet<T>
    where T: Ord+Clone
    {
      type Output = BTreeSet<T>;

      fn $m(self, other: BTreeSet<T>) -> BTreeSet<T> {
        BTreeSet::wrap(FromIterator::from_iter(self.deref().$m(&other).cloned()))
      }
    }

    impl $t for BitSet {
      type Output = BitSet;

      fn $m(mut self, other: BitSet) -> BitSet {
        self.deref_mut().$v(&other);
        self
      }
    }

    impl<T, S> $t for HashSet<T, S>
    where T: Eq + Hash + Clone,
          S: HashState + Default
    {
      type Output = HashSet<T, S>;

      fn $m(self, other: HashSet<T, S>) -> HashSet<T, S> {
        HashSet::wrap(FromIterator::from_iter(self.deref().$m(&other).cloned()))
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

      fn $m(self, other: EnumSet<E>) -> EnumSet<E> {
        EnumSet::wrap(self.deref().$m(*other))
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

// Cardinality

pub trait Cardinality {
  type Size : Int;
  fn size(&self) -> Self::Size;

  fn is_singleton(&self) -> bool {
    self.size() == <Self::Size as Int>::one()
  }

  fn is_empty(&self) -> bool {
    self.size() == <Self::Size as Int>::zero()
  }
}

// Construction

pub trait Empty {
  fn empty() -> Self;
}

pub trait Singleton<Item> {
  fn singleton(value: Item) -> Self;
}

pub trait Bounded
{
  type Bound: PartialOrd;
  fn lower(&self) -> Self::Bound;
  fn upper(&self) -> Self::Bound;
}
