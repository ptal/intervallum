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
    self.intervals[0].lower()
  }

  fn upper(&self) -> Bound {
    assert!(!self.intervals.is_empty(), "Cannot access upper bound on empty interval.");
    self.intervals[self.intervals.len()-1].upper()
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
