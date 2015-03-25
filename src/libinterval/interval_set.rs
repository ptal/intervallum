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

use interval::Interval;
use ncollections::ops::*;
use ops::*;

use std::num::Int;

pub struct IntervalSet<Bound> {
  intervals: Vec<Interval<Bound>>,
  size: Bound
}

impl<Bound: Int> IntervalSet<Bound>
{
  fn front<'a>(&'a self) -> &'a Interval<Bound> {
    assert!(!self.intervals.is_empty(), "Cannot access the first element of an empty interval set.");
    &self.intervals[0]
  }

  fn back<'a>(&'a self) -> &'a Interval<Bound> {
    assert!(!self.intervals.is_empty(), "Cannot access the last element of an empty interval set.");
    &self.intervals[self.intervals.len() - 1]
  }

  fn span(&self) -> Interval<Bound> {
    if self.is_empty() {
      Interval::empty()
    }
    else {
      Interval::new(
        self.front().lower(),
        self.back().upper()
      )
    }
  }
}

impl<Bound: Int> Eq for IntervalSet<Bound> {}

impl<Bound: Int> PartialEq<IntervalSet<Bound>> for IntervalSet<Bound>
{
  fn eq(&self, other: &IntervalSet<Bound>) -> bool {
    if self.size() != other.size() { false }
    else {
      self.intervals == other.intervals
    }
  }
}

impl<Bound: Int> Range<Bound> for IntervalSet<Bound>
{
  fn new(lb: Bound, ub: Bound) -> IntervalSet<Bound> {
    assert!(lb <= ub, "Cannot build empty interval set with an invalid range. Use IntervalSet::empty().");
    let i = Interval::new(lb, ub);
    IntervalSet {
      intervals: vec![i],
      size: i.size()
    }
  }
}

impl<Bound: Int> Bounded for IntervalSet<Bound>
{
  type Bound = Bound;

  fn lower(&self) -> Bound {
    assert!(!self.intervals.is_empty(), "Cannot access lower bound on empty interval.");
    self.front().lower()
  }

  fn upper(&self) -> Bound {
    assert!(!self.intervals.is_empty(), "Cannot access upper bound on empty interval.");
    self.back().upper()
  }
}

impl <Bound: Int> Singleton<Bound> for IntervalSet<Bound>
{
  fn singleton(x: Bound) -> IntervalSet<Bound> {
    IntervalSet::new(x, x)
  }
}

impl<Bound: Int> Empty for IntervalSet<Bound>
{
  fn empty() -> IntervalSet<Bound> {
    IntervalSet {
      intervals: vec![],
      size: <Bound as Int>::zero()
    }
  }
}

impl<Bound: Int> Cardinality for IntervalSet<Bound>
{
  type Size = Bound;

  fn size(&self) -> Bound {
    self.size
  }

  fn is_singleton(&self) -> bool {
    self.intervals.len() == 1 && self.intervals[0].is_singleton()
  }

  fn is_empty(&self) -> bool {
    self.intervals.is_empty()
  }
}

impl<Bound: Int> Contains<Bound> for IntervalSet<Bound>
{
  fn contains(&self, value: &Bound) -> bool {
    if !self.span().contains(value) {
      false
    }
    else {
      let value = *value;
      let mut left = 0;
      let mut right = self.intervals.len() - 1;
      while left <= right {
        let mid_idx = (left + right) / 2;
        let mid = self.intervals[mid_idx];
        if mid.lower() > value {
          right = mid_idx - 1;
        }
        else if mid.upper() < value {
          left = mid_idx + 1;
        }
        else {
          return true;
        }
      }
      false
    }
  }
}

#[allow(non_upper_case_globals)]
#[cfg(test)]
mod tests {
  use super::*;
  use ncollections::ops::*;
  use interval::*;
  use ops::*;

  #[test]
  fn test_contains() {
    let i1_2 = IntervalSet::new(1i32, 2i32);
    let i1_2u5_8 = IntervalSet {
      intervals: vec![
        Interval::new(1,2),
        Interval::new(5,8)
      ],
      size: 6
    };

    assert!(i1_2.contains(&1));
    assert!(i1_2.contains(&2));
    assert!(!i1_2.contains(&0));
    assert!(!i1_2.contains(&3));

    assert!(!i1_2u5_8.contains(&0));
    for i in 1..3 {
      assert!(i1_2u5_8.contains(&i));
    }
    for i in 3..5 {
      assert!(!i1_2u5_8.contains(&i));
    }
    for i in 5..9 {
      assert!(i1_2u5_8.contains(&i));
    }
    for i in 9..13 {
      assert!(!i1_2u5_8.contains(&i));
    }
  }
}