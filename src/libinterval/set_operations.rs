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

use std::num::Int;
use std::collections::BTreeSet;
use std::collections::BitSet;
use std::collections::HashSet;
use std::collections::hash_state::HashState;
use collections::enum_set::{CLike, EnumSet};
use std::hash::Hash;
use std::iter::FromIterator;
use std::default::Default;

pub trait Intersection<RHS = Self> {
  type Output;
  fn intersection_of(self, rhs: RHS) -> Self::Output;
}

pub trait Union<RHS = Self> {
  type Output;
  fn union_of(self, rhs: RHS) -> Self::Output;
}

pub trait Difference<RHS = Self> {
  type Output;
  fn difference_of(self, rhs: RHS) -> Self::Output;
}

pub trait SymmetricDifference<RHS = Self> {
  type Output;
  fn symmetric_difference_of(self, rhs: RHS) -> Self::Output;
}

pub trait Membership<Item, RHS = Self> {
  fn contains(&self, value: &Item) -> bool;
  fn is_subset(&self, rhs: &RHS) -> bool;
  fn is_proper_subset(&self, rhs: &RHS) -> bool;
}

pub trait Disjoint<RHS = Self> {
  fn is_disjoint(&self, rhs: &RHS) -> bool;
}

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

pub trait Empty {
  fn empty() -> Self;
}

macro_rules! set_op_impl
{
  ( $( $t: ident, $m:ident, $m_of:ident, $v:ident );* ) =>
  {$(
    impl<T> $t for BTreeSet<T>
    where T: Ord+Clone
    {
      type Output = BTreeSet<T>;

      fn $m_of(self, other: BTreeSet<T>) -> BTreeSet<T> {
        FromIterator::from_iter(self.$m(&other).cloned())
      }
    }

    impl $t for BitSet {
      type Output = BitSet;

      fn $m_of(mut self, other: BitSet) -> BitSet {
        self.$v(&other);
        self
      }
    }

    impl<T, S> $t for HashSet<T, S>
    where T: Eq + Hash + Clone,
          S: HashState + Default
    {
      type Output = HashSet<T, S>;

      fn $m_of(self, other: HashSet<T, S>) -> HashSet<T, S> {
        FromIterator::from_iter(self.$m(&other).cloned())
      }
    }
  )*}
}

macro_rules! set_enum_op_impl
{
  ( $( $t: ident, $m:ident, $m_of:ident, $v:ident );* ) =>
  {$(
    set_op_impl! {$t, $m, $m_of, $v}

    impl<E: CLike> $t for EnumSet<E>
    {
      type Output = EnumSet<E>;

      fn $m_of(self, other: EnumSet<E>) -> EnumSet<E> {
        self.$m(other)
      }
    }
  )*}
}

set_enum_op_impl! {
  Intersection, intersection, intersection_of, intersect_with;
  Union, union, union_of, union_with
}

set_op_impl! {
  Difference, difference, difference_of, difference_with;
  SymmetricDifference, symmetric_difference, symmetric_difference_of, symmetric_difference_with
}
