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

pub trait Intersection<RHS = Self> {
  type Output;
  fn intersect(self, rhs: RHS) -> Self::Output;
}

pub trait Union<RHS = Self> {
  type Output;
  fn union(self, rhs: RHS) -> Self::Output;
}

pub trait Difference<RHS = Self> {
  type Output;
  fn difference(self, rhs: RHS) -> Self::Output;
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
