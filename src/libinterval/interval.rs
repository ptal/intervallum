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
use std::num::SignedInt;

#[derive(PartialEq, Eq, Show, Copy, Clone)]
pub struct Interval {
  lb: int,
  ub: int
}

impl Interval
{
  pub fn new(lb: int, ub: int) -> Interval {
    Interval { lb: lb, ub: ub }
  }

  pub fn empty() -> Interval {
    Interval::new(1, 0)
  }

  pub fn singleton(x: int) -> Interval {
    Interval::new(x, x)
  }

  pub fn is_singleton(self) -> bool {
    self.lb == self.ub
  }

  pub fn size(self) -> uint {
    if self.is_empty() { 0 }
    else { (self.ub - self.lb + 1).abs() as uint }
  }

  pub fn is_empty(self) -> bool {
    self.lb > self.ub
  }

  pub fn member(self, x: int) -> bool {
    x >= self.lb && x <= self.ub
  }

  pub fn is_subset_of(self, i: Interval) -> bool {
    if self.is_empty() { true }
    else {
      self.lb >= i.lb && self.ub <= i.ub
    }
  }

  pub fn intersection(self, i: Interval) -> Interval {
    Interval::new(
      max(self.lb, i.lb),
      min(self.ub, i.ub)
    )
  }

  pub fn hull(self, i: Interval) -> Interval {
    if self.is_empty() { i }
    else if i.is_empty() { self }
    else {
      Interval::new(
        min(self.lb, i.lb),
        max(self.ub, i.ub)
      )
    }
  }

  fn disjoint(self, i: Interval) -> bool {
    self.lb > i.ub || i.lb > self.ub
  }
}

pub trait ToInterval {
  fn to_interval(self) -> Interval;
}

impl ToInterval for Interval {
  fn to_interval(self) -> Interval { self }
}

impl ToInterval for (int, int) {
  fn to_interval(self) -> Interval {
    let (a, b) = self;
    Interval::new(a, b)
  }
}

impl ToInterval for () {
  fn to_interval(self) -> Interval {
    Interval::empty()
  }
}

impl ToInterval for int {
  fn to_interval(self) -> Interval {
    Interval::singleton(self)
  }
}


#[allow(non_upper_case_globals)]
#[cfg(test)]
mod tests {
  use super::*;

  const empty: Interval = Interval {lb: 1, ub: 0};
  const invalid: Interval = Interval {lb: 10, ub: -10};
  const zero: Interval = Interval {lb: 0, ub: 0};
  const one: Interval = Interval {lb: 1, ub: 1};

  const i1_2: Interval = Interval {lb: 1, ub: 2};
  const i0_10: Interval = Interval {lb: 0, ub: 10};
  const i5_10: Interval = Interval {lb: 5, ub: 10};
  const i0_5: Interval = Interval {lb: 0, ub: 5};
  const i20_30: Interval = Interval {lb: 20, ub: 30};
  const im30_m20: Interval = Interval {lb: -30, ub: -20};

  #[test]
  fn to_interval_id_test() {
    let id = i1_2.clone().to_interval();
    assert!(i1_2 == id);
    assert!(i1_2 == Interval::new(1, 2));
  }

  #[test]
  fn size_test() {
    assert!(zero.size() == 1);
    assert!(one.size() == 1);
    assert!(empty.size() == 0);
    assert!(invalid.size() == 0);

    assert!(i1_2.size() == 2);
    assert!(i0_10.size() == 11);
    assert!(im30_m20.size() == 11);
  }
}