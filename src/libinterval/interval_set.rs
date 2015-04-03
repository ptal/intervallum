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

//! Closed and bounded generic interval set.
//!
//! It stores intervals in a set. The main advantage is the exact representation of an interval by allowing "holes". For example `[1..2] U [5..6]` is stored as `{[1..2], [5..6]}`. This structure is more space-efficient than a classic set collection (such as `BTreeSet`) if the data stored are mostly contiguous. Of course, it is less light-weight than [interval](../interval/index.html), but we keep the list of interval as small as possible by merging overlapping intervals.
//!
//! # See also
//! [interval](../interval/index.html)

use interval::Interval;
use ncollections::ops::*;
use ops::*;
use std::iter::{Peekable, IntoIterator};

use std::num::Int;

#[derive(Debug, Clone)]
pub struct IntervalSet<Bound: Width> {
  intervals: Vec<Interval<Bound>>,
  size: Bound::Output
}

impl<Bound: Width+Int> IntervalSet<Bound>
{
  pub fn interval_count(&self) -> usize {
    self.intervals.len()
  }

  fn from_interval(i: Interval<Bound>) -> IntervalSet<Bound> {
    IntervalSet {
      intervals: vec![i],
      size: i.size()
    }
  }

  fn front<'a>(&'a self) -> &'a Interval<Bound> {
    assert!(!self.is_empty(), "Cannot access the first interval of an empty set.");
    &self.intervals[0]
  }

  fn back<'a>(&'a self) -> &'a Interval<Bound> {
    assert!(!self.is_empty(), "Cannot access the last interval of an empty set.");
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

  fn push(&mut self, x: Interval<Bound>) {
    assert!(!x.is_empty(), "Cannot push empty interval.");
    assert!(self.is_empty() || !joinable(self.back(), &x),
      "The intervals array must be ordered and intervals must not be joinable. For a safe push, use the union operation.");

    self.size = self.size + x.size();
    self.intervals.push(x);
  }

  fn pop(&mut self) -> Option<Interval<Bound>> {
    if let Some(x) = self.intervals.pop() {
      self.size = self.size - x.size();
      Some(x)
    } else {
      None
    }
  }

  fn join_or_push(&mut self, x: Interval<Bound>) {
    if self.is_empty() {
      self.push(x);
    }
    else {
      assert!(!x.is_empty(), "Cannot push empty interval.");
      assert!(self.back().lower() <= x.lower(),
        "This operation is only for pushing interval to the back of the array, possibly overlapping with the last element.");

      let joint =
        if joinable(self.back(), &x) {
          self.pop().unwrap().hull(&x)
        }
        else {
          x
        };
      self.push(joint);
    }
  }
}

fn joinable<Bound: Width+Int>(first: &Interval<Bound>, second: &Interval<Bound>) -> bool {
  first.upper() + Bound::one() >= second.lower()
}

impl<Bound: Width+Int> Extend<Interval<Bound>> for IntervalSet<Bound>
{
  fn extend<I>(&mut self, iterable: I) where
   I: IntoIterator<Item=Interval<Bound>>
  {
    for interval in iterable {
      self.join_or_push(interval);
    }
  }
}

impl<Bound: Width+Int> Eq for IntervalSet<Bound> {}

impl<Bound: Width+Int> PartialEq<IntervalSet<Bound>> for IntervalSet<Bound>
{
  fn eq(&self, other: &IntervalSet<Bound>) -> bool {
    if self.size() != other.size() { false }
    else {
      self.intervals == other.intervals
    }
  }
}

impl<Bound: Width+Int> Range<Bound> for IntervalSet<Bound>
{
  fn new(lb: Bound, ub: Bound) -> IntervalSet<Bound> {
    assert!(lb <= ub, "Cannot build empty interval set with an invalid range. Use IntervalSet::empty().");
    let i = Interval::new(lb, ub);
    IntervalSet::from_interval(i)
  }
}

impl<Bound: Width+Int> Bounded for IntervalSet<Bound>
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

impl <Bound: Width+Int> Singleton<Bound> for IntervalSet<Bound>
{
  fn singleton(x: Bound) -> IntervalSet<Bound> {
    IntervalSet::new(x, x)
  }
}

impl<Bound: Width+Int> Empty for IntervalSet<Bound>
{
  fn empty() -> IntervalSet<Bound> {
    IntervalSet {
      intervals: vec![],
      size: <<Bound as Width>::Output>::zero()
    }
  }
}

impl<Bound: Width+Int> Cardinality for IntervalSet<Bound>
{
  type Size = <Bound as Width>::Output;

  fn size(&self) -> <Bound as Width>::Output {
    self.size
  }

  fn is_singleton(&self) -> bool {
    self.size() == <<Bound as Width>::Output>::one()
  }

  fn is_empty(&self) -> bool {
    self.size() == <<Bound as Width>::Output>::zero()
  }
}

impl<Bound: Width+Int> Contains<Bound> for IntervalSet<Bound>
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

fn advance_one<I, F, Item>(a : &mut Peekable<I>, b: &mut Peekable<I>, choose: F) -> Item where
 I: Iterator<Item=Item>,
 F: Fn(&Item, &Item) -> bool,
 Item: Bounded
{
  assert!(!a.is_empty() && !b.is_empty());
  let who_advance = {
    let i = a.peek().unwrap();
    let j = b.peek().unwrap();
    choose(i, j)
  };
  let to_advance = if who_advance { a } else { b };
  to_advance.next().unwrap()
}

fn advance_lower<I, Item>(a : &mut Peekable<I>, b: &mut Peekable<I>) -> Item where
 I: Iterator<Item=Item>,
 Item: Bounded
{
  advance_one(a, b, |i,j| i.lower() < j.lower())
}

// Advance the one with the lower upper bound.
fn advance_lub<I, Item>(a : &mut Peekable<I>, b: &mut Peekable<I>) -> Item where
 I: Iterator<Item=Item>,
 Item: Bounded
{
  advance_one(a, b, |i, j| i.upper() < j.upper())
}

fn from_lower_iterator<I, Bound>(a : &mut Peekable<I>, b: &mut Peekable<I>) -> IntervalSet<Bound> where
 I: Iterator<Item=Interval<Bound>>,
 Bound: Width+Int
{
  if a.is_empty() || b.is_empty() {
    IntervalSet::empty()
  } else {
    let first = advance_lower(a, b);
    IntervalSet::from_interval(first)
  }
}

impl<Bound: Width+Int> Union for IntervalSet<Bound>
{
  type Output = IntervalSet<Bound>;

  fn union(&self, rhs: &IntervalSet<Bound>) -> IntervalSet<Bound> {
    let mut a = &mut self.intervals.iter().cloned().peekable();
    let mut b = &mut rhs.intervals.iter().cloned().peekable();
    let mut res = from_lower_iterator(a, b);
    while !a.is_empty() && !b.is_empty() {
      let lower = advance_lower(a, b);
      res.join_or_push(lower);
    }
    res.extend(a);
    res.extend(b);
    res
  }
}

// Returns `false` when one of the iterator is consumed.
// Iterators are not consumed if the intervals are already overlapping.
fn advance_to_first_overlapping<I, Item>(a : &mut Peekable<I>, b: &mut Peekable<I>) -> bool where
 I: Iterator<Item=Item>,
 Item: Bounded + Overlap
{
  while !a.is_empty() && !b.is_empty() {
    let overlapping = {
      let i = a.peek().unwrap();
      let j = b.peek().unwrap();
      i.overlap(&j)
    };
    if overlapping {
      return true
    } else {
      advance_lower(a, b);
    }
  }
  false
}

impl<Bound: Width+Int> Intersection for IntervalSet<Bound>
{
  type Output = IntervalSet<Bound>;

  fn intersection(&self, rhs: &IntervalSet<Bound>) -> IntervalSet<Bound> {
    let mut a = &mut self.intervals.iter().cloned().peekable();
    let mut b = &mut rhs.intervals.iter().cloned().peekable();
    let mut res = IntervalSet::empty();
    while advance_to_first_overlapping(a, b) {
      {
        let i = a.peek().unwrap();
        let j = b.peek().unwrap();
        res.push(i.intersection(j));
      }
      advance_lub(a, b); // advance the one with the lowest upper bound.
    }
    res
  }
}

fn push_left_complement<Bound: Width+Int>(x: &Interval<Bound>, res: &mut IntervalSet<Bound>) {
  let min = <Bound as Width>::min_value();
  if x.lower() != min {
    res.push(Interval::new(min, x.lower() - Bound::one()));
  }
}

fn push_right_complement<Bound: Width+Int>(x: &Interval<Bound>, res: &mut IntervalSet<Bound>) {
  let max = <Bound as Width>::max_value();
  if x.upper() != max {
    res.push(Interval::new(x.upper() + Bound::one(), max));
  }
}

impl<Bound: Width+Int> Complement for IntervalSet<Bound>
{
  fn complement(&self) -> IntervalSet<Bound> {
    let mut res = IntervalSet::empty();
    if self.is_empty() {
      res.push(Interval::whole());
    }
    else {
      let one = Bound::one();
      push_left_complement(self.front(), &mut res);
      for i in 1..self.intervals.len() {
        let current = &self.intervals[i];
        let previous = &self.intervals[i-1];
        res.push(Interval::new(previous.upper() + one, current.lower() - one));
      }
      push_right_complement(self.back(), &mut res);
    }
    res
  }
}

#[allow(non_upper_case_globals)]
#[cfg(test)]
mod tests {
  use super::*;
  use ncollections::ops::*;
  use ops::*;
  use interval::*;

  fn test_inside_outside(is: IntervalSet<i32>, inside: Vec<i32>, outside: Vec<i32>) {
    for i in &inside {
      assert!(is.contains(i),
        format!("{} is not contained inside {:?}, but it should.", i, is));
    }
    for i in &outside {
      assert!(!is.contains(i),
        format!("{} is contained inside {:?}, but it should not.", i, is));
    }
  }

  // precondition: `intervals` must be a valid intern representation of the interval set.
  fn make_interval_set(intervals: Vec<(i32, i32)>) -> IntervalSet<i32> {
    let intervals: Vec<Interval<i32>> =
       intervals.into_iter()
      .map(|i| i.to_interval())
      .collect();
    let size = intervals.iter().fold(0, |a, i| a + i.size());
    IntervalSet {
      intervals: intervals,
      size: size
    }
  }

  fn test_result(test_id: String, result: IntervalSet<i32>, expected: IntervalSet<i32>) {
    assert!(result.size() == expected.size(),
      format!("{} | {:?} has a cardinality of {} instead of {}.",test_id, result, result.size(), expected.size()));
    assert!(result.interval_count() == expected.interval_count(),
      format!("{} | {:?} has {} intervals instead of {}.", test_id, result, result.interval_count(), expected.interval_count()));
    assert!(result.intervals == expected.intervals,
      format!("{} | {:?} is different from the expected value: {:?}.", test_id, result, expected));
  }

  fn test_binary_op_sym<F>(test_id: String, a: Vec<(i32,i32)>, b: Vec<(i32,i32)>, op: F, expected: Vec<(i32,i32)>) where
    F: Fn(&IntervalSet<i32>, &IntervalSet<i32>) -> IntervalSet<i32>
  {
    println!("Info: {}.", test_id);
    let a = make_interval_set(a);
    let b = make_interval_set(b);
    let expected = make_interval_set(expected);
    let result = op(&a, &b);
    test_result(test_id, result, expected);
  }

  fn test_op<F>(test_id: String, a: Vec<(i32,i32)>, op: F, expected: Vec<(i32,i32)>) where
    F: Fn(&IntervalSet<i32>) -> IntervalSet<i32>
  {
    println!("Info: {}.", test_id);
    let a = make_interval_set(a);
    let expected = make_interval_set(expected);
    let result = op(&a);
    test_result(test_id, result, expected);
  }

  #[test]
  fn test_contains() {
    let cases = vec![
      (vec![], vec![], vec![-2,-1,0,1,2]),
      (vec![(1,2)], vec![1,2], vec![-1,0,3,4]),
      (vec![(1,2),(7,9)], vec![1,2,7,8,9], vec![-1,0,3,4,5,6,10,11]),
      (vec![(1,2),(4,5),(7,9)], vec![1,2,4,5,7,8,9], vec![-1,0,3,6,10,11])
    ];

    for (is, inside, outside) in cases {
      let is = make_interval_set(is);
      test_inside_outside(is, inside, outside);
    }
  }

  #[test]
  fn test_complement() {
    let min = <i32 as Width>::min_value();
    let max = <i32 as Width>::max_value();

    let cases = vec![
      (1, vec![], vec![(min, max)]),
      (2, vec![(min, max)], vec![]),
      (3, vec![(0,0)], vec![(min,-1),(1,max)]),
      (4, vec![(-5,5)], vec![(min,-6),(6,max)]),
      (5, vec![(-5,-1),(1,5)], vec![(min,-6),(0,0),(6, max)]),
      (6, vec![(min,-1),(1,5)], vec![(0,0),(6, max)]),
      (7, vec![(-5,-1),(1,max)], vec![(min,-6),(0,0)]),
      (8, vec![(min,-1),(1,max)], vec![(0,0)]),
      (9, vec![(-5,-3),(0,1),(3,5)], vec![(min,-6),(-2,-1),(2,2),(6, max)])
    ];

    for (id, a, expected) in cases {
      test_op(format!("test #{} of complement", id), a.clone(), |x| x.complement(), expected);
      test_op(format!("test #{} of complement(complement)", id), a.clone(), |x| x.complement().complement(), a);
    }
  }

  #[test]
  fn test_union() {
    // Note: the first number is the test id, so it should be easy to identify which test has failed.
    // The two first vectors are the operands and the expected result is last.
    let sym_cases = vec![
      // identity tests
      (1, vec![], vec![], vec![]),
      (2, vec![], vec![(1,2)], vec![(1,2)]),
      (3, vec![], vec![(1,2),(7,9)], vec![(1,2),(7,9)]),
      (4, vec![(1,2),(7,9)], vec![(1,2)], vec![(1,2),(7,9)]),
      (5, vec![(1,2),(7,9)], vec![(1,2),(7,9)], vec![(1,2),(7,9)]),
      // front tests
      (6, vec![(-3,-1)], vec![(1,2),(7,9)], vec![(-3,-1),(1,2),(7,9)]),
      (7, vec![(-3,0)], vec![(1,2),(7,9)], vec![(-3,2),(7,9)]),
      (8, vec![(-3,1)], vec![(1,2),(7,9)], vec![(-3,2),(7,9)]),
      // middle tests
      (9, vec![(2,7)], vec![(1,2),(7,9)], vec![(1,9)]),
      (10, vec![(3,7)], vec![(1,2),(7,9)], vec![(1,9)]),
      (11, vec![(4,5)], vec![(1,2),(7,9)], vec![(1,2),(4,5),(7,9)]),
      (12, vec![(2,8)], vec![(1,2),(7,9)], vec![(1,9)]),
      (13, vec![(2,6)], vec![(1,2),(7,9)], vec![(1,9)]),
      (14, vec![(3,6)], vec![(1,2),(7,9)], vec![(1,9)]),
      // back tests
      (15, vec![(8,9)], vec![(1,2),(7,9)], vec![(1,2),(7,9)]),
      (16, vec![(8,10)], vec![(1,2),(7,9)], vec![(1,2),(7,10)]),
      (17, vec![(9,10)], vec![(1,2),(7,9)], vec![(1,2),(7,10)]),
      (18, vec![(6,10)], vec![(1,2),(7,9)], vec![(1,2),(6,10)]),
      (19, vec![(10,11)], vec![(1,2),(7,9)], vec![(1,2),(7,11)]),
      (20, vec![(11,12)], vec![(1,2),(7,9)], vec![(1,2),(7,9),(11,12)]),
      // mixed tests
      (21, vec![(-3,-1),(4,5),(11,12)], vec![(1,2),(7,9)], vec![(-3,-1),(1,2),(4,5),(7,9),(11,12)]),
      (22, vec![(-3,0),(3,6),(10,11)], vec![(1,2),(7,9)], vec![(-3,11)]),
      (23, vec![(-3,1),(3,7),(9,11)], vec![(1,2),(7,9)], vec![(-3,11)]),
      (24, vec![(-3,5),(7,11)], vec![(1,2),(7,9)], vec![(-3,5),(7,11)]),
      (25, vec![(-3,5),(7,8),(12,12)], vec![(1,2),(7,9)], vec![(-3,5),(7,9),(12,12)]),
      // englobing tests
      (26, vec![(-1,11)], vec![(1,2),(7,9)], vec![(-1,11)]),
    ];

    for (id, a, b, expected) in sym_cases {
      test_binary_op_sym(format!("test #{} of union", id), a, b, |x,y| x.union(y), expected);
    }
  }

  #[test]
  fn test_intersection() {
    // Note: the first number is the test id, so it should be easy to identify which test has failed.
    // The two first vectors are the operands and the expected result is last.
    let sym_cases = vec![
      // identity tests
      (1, vec![], vec![], vec![]),
      (2, vec![], vec![(1,2)], vec![]),
      (3, vec![], vec![(1,2),(7,9)], vec![]),
      (4, vec![(1,2),(7,9)], vec![(1,2)], vec![(1,2)]),
      (5, vec![(1,2),(7,9)], vec![(1,2),(7,9)], vec![(1,2),(7,9)]),
      // front tests
      (6, vec![(-3,-1)], vec![(1,2),(7,9)], vec![]),
      (7, vec![(-3,0)], vec![(1,2),(7,9)], vec![]),
      (8, vec![(-3,1)], vec![(1,2),(7,9)], vec![(1,1)]),
      // middle tests
      (9, vec![(2,7)], vec![(1,2),(7,9)], vec![(2,2),(7,7)]),
      (10, vec![(3,7)], vec![(1,2),(7,9)], vec![(7,7)]),
      (11, vec![(4,5)], vec![(1,2),(7,9)], vec![]),
      (12, vec![(2,8)], vec![(1,2),(7,9)], vec![(2,2),(7,8)]),
      (13, vec![(2,6)], vec![(1,2),(7,9)], vec![(2,2)]),
      (14, vec![(3,6)], vec![(1,2),(7,9)], vec![]),
      // back tests
      (15, vec![(8,9)], vec![(1,2),(7,9)], vec![(8,9)]),
      (16, vec![(8,10)], vec![(1,2),(7,9)], vec![(8,9)]),
      (17, vec![(9,10)], vec![(1,2),(7,9)], vec![(9,9)]),
      (18, vec![(6,10)], vec![(1,2),(7,9)], vec![(7,9)]),
      (19, vec![(10,11)], vec![(1,2),(7,9)], vec![]),
      (20, vec![(11,12)], vec![(1,2),(7,9)], vec![]),
      // mixed tests
      (21, vec![(-3,-1),(4,5),(11,12)], vec![(1,2),(7,9)], vec![]),
      (22, vec![(-3,0),(3,6),(10,11)], vec![(1,2),(7,9)], vec![]),
      (23, vec![(-3,1),(3,7),(9,11)], vec![(1,2),(7,9)], vec![(1,1),(7,7),(9,9)]),
      (24, vec![(-3,5),(7,11)], vec![(1,2),(7,9)], vec![(1,2),(7,9)]),
      (25, vec![(-3,5),(7,8),(12,12)], vec![(1,2),(7,9)], vec![(1,2),(7,8)]),
      // englobing tests
      (26, vec![(-1,11)], vec![(1,2),(7,9)], vec![(1,2),(7,9)]),
    ];

    for (id, a, b, expected) in sym_cases {
      test_binary_op_sym(format!("test #{} of intersection", id), a, b, |x,y| x.intersection(y), expected);
    }
  }
}