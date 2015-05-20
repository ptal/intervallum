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
//! It stores intervals in a set. The main advantage is the exact representation of an interval by allowing "holes". For example `[1..2] U [5..6]` is stored as `{[1..2], [5..6]}`. This structure is more space-efficient than a classic set collection (such as `BTreeSet`) if the data stored are mostly contiguous. Of course, it is less light-weight than [interval](../interval/index.html), but we keep the list of intervals as small as possible by merging overlapping intervals.
//!
//! # See also
//! [interval](../interval/index.html)

use interval::Interval;
use ncollections::ops::*;
use ops::*;
use std::iter::{Peekable, IntoIterator};
use std::fmt::{Formatter, Display, Error};
use std::result::fold;
use std::ops::{Add, Sub, Mul};

use num::{Zero, One, Num};

#[derive(Debug, Clone)]
pub struct IntervalSet<Bound: Width> {
  intervals: Vec<Interval<Bound>>,
  size: Bound::Output
}

impl<Bound: Width+Num> IntervalSet<Bound> where
   <Bound as Width>::Output: Clone
{
  pub fn interval_count(&self) -> usize {
    self.intervals.len()
  }

  fn from_interval(i: Interval<Bound>) -> IntervalSet<Bound> {
    let size = i.size().clone();
    IntervalSet {
      intervals: vec![i],
      size: size
    }
  }

  fn front<'a>(&'a self) -> &'a Interval<Bound> {
    debug_assert!(!self.is_empty(), "Cannot access the first interval of an empty set.");
    &self.intervals[0]
  }

  fn back_idx(&self) -> usize {
    self.intervals.len() - 1
  }

  fn back<'a>(&'a self) -> &'a Interval<Bound> {
    debug_assert!(!self.is_empty(), "Cannot access the last interval of an empty set.");
    &self.intervals[self.back_idx()]
  }

  fn span(&self) -> Interval<Bound> {
    if self.is_empty() {
      Interval::empty()
    }
    else {
      self.span_slice(0, self.back_idx())
    }
  }

  fn span_slice(&self, left: usize, right: usize) -> Interval<Bound> {
    Interval::new(
      self.intervals[left].lower(),
      self.intervals[right].upper()
    )
  }

  fn push(&mut self, x: Interval<Bound>) {
    debug_assert!(!x.is_empty(), "Cannot push empty interval.");
    debug_assert!(self.is_empty() || !joinable(self.back(), &x),
      "The intervals array must be ordered and intervals must not be joinable. For a safe push, use the union operation.");

    self.size = self.size.clone() + x.size();
    self.intervals.push(x);
  }

  fn pop(&mut self) -> Option<Interval<Bound>> {
    if let Some(x) = self.intervals.pop() {
      self.size = self.size.clone() - x.size();
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
      debug_assert!(!x.is_empty(), "Cannot push empty interval.");
      debug_assert!(self.back().lower() <= x.lower(),
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

  fn find_interval_between(&self, value: &Bound,
    mut left: usize, mut right: usize) -> (usize, usize)
  {
    debug_assert!(left <= right);
    debug_assert!(right < self.intervals.len());
    debug_assert!(self.span_slice(left, right).contains(value));

    while left <= right {
      let mid_idx = (left + right) / 2;
      let mid = &self.intervals[mid_idx];
      if &mid.lower() > value {
        right = mid_idx - 1;
      }
      else if &mid.upper() < value {
        left = mid_idx + 1;
      }
      else {
        return (mid_idx, mid_idx)
      }
    }
    (right, left)
  }

  // Returns the indexes of the left and right interval of `value`.
  // If the value is outside `self`, returns None.
  // If the value is inside one of the interval, the indexes will be equal.
  fn find_interval(&self, value: &Bound) -> Option<(usize, usize)> {
    if !self.span().contains(value) {
      None
    }
    else {
      Some(self.find_interval_between(value, 0, self.back_idx()))
    }
  }

  fn for_all_pairs<F>(&self, other: &IntervalSet<Bound>, f: F) -> IntervalSet<Bound> where
    F: Fn(&Interval<Bound>, &Interval<Bound>) -> Interval<Bound>
  {
    let mut res = IntervalSet::empty();
    for i in &self.intervals {
      for j in &other.intervals {
        res = res.union(&IntervalSet::from_interval(f(i,j)));
      }
    }
    res
  }

  // Precondition: `f` must not change the size of the interval.
  fn stable_map<F>(&self, f: F) -> IntervalSet<Bound> where
    F: Fn(&Interval<Bound>) -> Interval<Bound>
  {
    IntervalSet {
      intervals: self.intervals.iter().map(f).collect(),
      size: self.size.clone()
    }
  }

  fn map<F>(&self, f: F) -> IntervalSet<Bound> where
    F: Fn(&Interval<Bound>) -> Interval<Bound>
  {
    self.intervals.iter().fold(IntervalSet::empty(),
      |mut r, i| { r.push(f(i)); r })
  }
}

fn joinable<Bound: Width+Num>(first: &Interval<Bound>, second: &Interval<Bound>) -> bool {
  first.upper() + Bound::one() >= second.lower()
}

impl<Bound: Width+Num> Extend<Interval<Bound>> for IntervalSet<Bound>
{
  fn extend<I>(&mut self, iterable: I) where
   I: IntoIterator<Item=Interval<Bound>>
  {
    for interval in iterable {
      self.join_or_push(interval);
    }
  }
}

impl<Bound: Width+Num> Eq for IntervalSet<Bound> {}

impl<Bound: Width+Num> PartialEq<IntervalSet<Bound>> for IntervalSet<Bound>
{
  fn eq(&self, other: &IntervalSet<Bound>) -> bool {
    if self.size() != other.size() { false }
    else {
      self.intervals == other.intervals
    }
  }
}

impl<Bound: Width+Num> Range<Bound> for IntervalSet<Bound>
{
  fn new(lb: Bound, ub: Bound) -> IntervalSet<Bound> {
    debug_assert!(lb <= ub, "Cannot build empty interval set with an invalid range. Use IntervalSet::empty().");
    let i = Interval::new(lb, ub);
    IntervalSet::from_interval(i)
  }
}

impl<Bound: Width+Num> Whole for IntervalSet<Bound>
{
  fn whole() -> IntervalSet<Bound> {
    let mut res = IntervalSet::empty();
    res.push(Interval::whole());
    res
  }
}

impl<Bound: Width+Num+PartialOrd> Bounded for IntervalSet<Bound>
{
  type Bound = Bound;

  fn lower(&self) -> Bound {
    debug_assert!(!self.is_empty(), "Cannot access lower bound on empty interval.");
    self.front().lower()
  }

  fn upper(&self) -> Bound {
    debug_assert!(!self.is_empty(), "Cannot access upper bound on empty interval.");
    self.back().upper()
  }
}

impl <Bound: Width+Num> Singleton<Bound> for IntervalSet<Bound>
{
  fn singleton(x: Bound) -> IntervalSet<Bound> {
    IntervalSet::new(x.clone(), x)
  }
}

impl<Bound: Width+Num> Empty for IntervalSet<Bound>
{
  fn empty() -> IntervalSet<Bound> {
    IntervalSet {
      intervals: vec![],
      size: <<Bound as Width>::Output>::zero()
    }
  }
}

impl<Bound: Width+Num> Cardinality for IntervalSet<Bound>
{
  type Size = <Bound as Width>::Output;

  fn size(&self) -> <Bound as Width>::Output {
    self.size.clone()
  }

  fn is_singleton(&self) -> bool {
    self.size() == <<Bound as Width>::Output>::one()
  }

  fn is_empty(&self) -> bool {
    self.size() == <<Bound as Width>::Output>::zero()
  }
}

impl<Bound: Width+Num> Contains<Bound> for IntervalSet<Bound>
{
  fn contains(&self, value: &Bound) -> bool {
    if let Some((left, right)) = self.find_interval(value) {
      left == right
    } else {
      false
    }
  }
}

fn advance_one<I, F, Item>(a : &mut Peekable<I>, b: &mut Peekable<I>, choose: F) -> Item where
 I: Iterator<Item=Item>,
 F: Fn(&Item, &Item) -> bool,
 Item: Bounded
{
  debug_assert!(!a.is_empty() && !b.is_empty());
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
 Bound: Width+Num
{
  if a.is_empty() || b.is_empty() {
    IntervalSet::empty()
  } else {
    let first = advance_lower(a, b);
    IntervalSet::from_interval(first)
  }
}

impl<Bound: Width+Num> Union for IntervalSet<Bound>
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

impl<Bound: Width+Num> Intersection for IntervalSet<Bound>
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

fn push_left_complement<Bound: Width+Num>(x: &Interval<Bound>, res: &mut IntervalSet<Bound>) {
  let min = <Bound as Width>::min_value();
  if x.lower() != min {
    res.push(Interval::new(min, x.lower() - Bound::one()));
  }
}

fn push_right_complement<Bound: Width+Num>(x: &Interval<Bound>, res: &mut IntervalSet<Bound>) {
  let max = <Bound as Width>::max_value();
  if x.upper() != max {
    res.push(Interval::new(x.upper() + Bound::one(), max));
  }
}

impl<Bound: Width+Num> Complement for IntervalSet<Bound>
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
        res.push(Interval::new(
          previous.upper() + one.clone(),
          current.lower() - one.clone()));
      }
      push_right_complement(self.back(), &mut res);
    }
    res
  }
}

impl<Bound: Width+Num> Difference for IntervalSet<Bound> {
  type Output = IntervalSet<Bound>;

  fn difference(&self, rhs: &IntervalSet<Bound>) -> IntervalSet<Bound> {
    self.intersection(&rhs.complement())
  }
}

impl<Bound: Width+Num> SymmetricDifference for IntervalSet<Bound> {
  type Output = IntervalSet<Bound>;

  fn symmetric_difference(&self, rhs: &IntervalSet<Bound>) -> IntervalSet<Bound> {
    let union = self.union(rhs);
    let intersection = self.intersection(rhs);
    union.difference(&intersection)
  }
}

impl<Bound: Width+Num> Overlap for IntervalSet<Bound> {
  fn overlap(&self, rhs: &IntervalSet<Bound>) -> bool {
    let mut a = &mut self.intervals.iter().cloned().peekable();
    let mut b = &mut rhs.intervals.iter().cloned().peekable();
    advance_to_first_overlapping(a, b)
  }
}

impl<Bound: Width+Num> Disjoint for IntervalSet<Bound> {
  fn is_disjoint(&self, rhs: &IntervalSet<Bound>) -> bool {
    !self.overlap(rhs)
  }
}

impl<Bound: Width+Num> ShrinkLeft<Bound> for IntervalSet<Bound> where
  <Bound as Width>::Output: Clone
{
  fn shrink_left(&self, lb: Bound) -> IntervalSet<Bound> {
    if let Some((left, _)) = self.find_interval(&lb) {
      let mut res = IntervalSet::empty();
      if self.intervals[left].upper() >= lb {
        res.push(Interval::new(lb, self.intervals[left].upper()));
      }
      for i in (left+1)..self.intervals.len() {
        res.push(self.intervals[i].clone());
      }
      res
    }
    else {
      if self.is_empty() || lb > self.back().upper() {
        IntervalSet::empty()
      } else {
        self.clone()
      }
    }
  }
}

impl<Bound: Width+Num> ShrinkRight<Bound> for IntervalSet<Bound> where
  <Bound as Width>::Output: Clone
{
  fn shrink_right(&self, ub: Bound) -> IntervalSet<Bound> {
    if let Some((_, right)) = self.find_interval(&ub) {
      let mut res = IntervalSet::empty();
      for i in 0..right {
        res.push(self.intervals[i].clone());
      }
      if self.intervals[right].lower() <= ub {
        res.push(Interval::new(self.intervals[right].lower(), ub));
      }
      res
    }
    else {
      if self.is_empty() || ub < self.front().lower() {
        IntervalSet::empty()
      } else {
        self.clone()
      }
    }
  }
}

impl<Bound: Width+Num> Subset for IntervalSet<Bound>
{
  fn is_subset(&self, other: &IntervalSet<Bound>) -> bool {
    if self.is_empty() { true }
    else if self.size() > other.size() { false }
    else if !self.span().is_subset(&other.span()) { false }
    else {
      let mut left = 0;
      let right = other.intervals.len() - 1;
      for interval in &self.intervals {
        let (l, r) = other.find_interval_between(&interval.lower(), left, right);
        if l == r && interval.is_subset(&other.intervals[l]) {
          left = l;
        } else {
          return false;
        }
      }
      true
    }
  }
}

impl<Bound: Width+Num> ProperSubset for IntervalSet<Bound>
{
  fn is_proper_subset(&self, other: &IntervalSet<Bound>) -> bool {
    self.is_subset(other) && self.size() != other.size()
  }
}

forward_all_binop!(impl<Bound: +Num+Width> Add for IntervalSet<Bound>, add);

impl<'a, 'b, Bound: Num+Width> Add<&'b IntervalSet<Bound>> for &'a IntervalSet<Bound> {
  type Output = IntervalSet<Bound>;

  fn add(self, other: &IntervalSet<Bound>) -> IntervalSet<Bound> {
    self.for_all_pairs(other, |i, j| i + j)
  }
}

forward_all_binop!(impl<Bound: +Num+Width+Clone> Add for IntervalSet<Bound>, add, Bound);

impl<'a, 'b, Bound: Num+Width+Clone> Add<&'b Bound> for &'a IntervalSet<Bound> {
  type Output = IntervalSet<Bound>;

  fn add(self, other: &Bound) -> IntervalSet<Bound> {
    self.stable_map(|x| x + other.clone())
  }
}

forward_all_binop!(impl<Bound: +Num+Width> Sub for IntervalSet<Bound>, sub);

impl<'a, 'b, Bound: Num+Width> Sub<&'b IntervalSet<Bound>> for &'a IntervalSet<Bound> {
  type Output = IntervalSet<Bound>;

  fn sub(self, other: &IntervalSet<Bound>) -> IntervalSet<Bound> {
    self.for_all_pairs(other, |i, j| i - j)
  }
}

forward_all_binop!(impl<Bound: +Num+Width+Clone> Sub for IntervalSet<Bound>, sub, Bound);

impl<'a, 'b, Bound: Num+Width+Clone> Sub<&'b Bound> for &'a IntervalSet<Bound> {
  type Output = IntervalSet<Bound>;

  fn sub(self, other: &Bound) -> IntervalSet<Bound> {
    self.stable_map(|x| x - other.clone())
  }
}

forward_all_binop!(impl<Bound: +Num+Width> Mul for IntervalSet<Bound>, mul);

impl<'a, 'b, Bound: Num+Width> Mul<&'b IntervalSet<Bound>> for &'a IntervalSet<Bound> {
  type Output = IntervalSet<Bound>;

  // Caution: This is an over-approximation. For the same reason as `Interval::mul`.
  fn mul(self, other: &IntervalSet<Bound>) -> IntervalSet<Bound> {
    self.for_all_pairs(other, |i, j| i * j)
  }
}

forward_all_binop!(impl<Bound: +Num+Width+Clone> Mul for IntervalSet<Bound>, mul, Bound);

impl<'a, 'b, Bound: Num+Width+Clone> Mul<&'b Bound> for &'a IntervalSet<Bound> {
  type Output = IntervalSet<Bound>;

  // Caution: This is an over-approximation. For the same reason as `Interval::mul`.
  fn mul(self, other: &Bound) -> IntervalSet<Bound> {
    if self.is_empty() {
      IntervalSet::empty()
    } else if other == &Bound::zero() {
      IntervalSet::singleton(Bound::zero())
    } else if other == &Bound::one() {
      self.clone()
    } else {
      self.map(|i| i * other.clone())
    }
  }
}

impl<Bound: Display+Width+Num> Display for IntervalSet<Bound> where
 <Bound as Width>::Output: Display
{
  fn fmt(&self, formatter: &mut Formatter) -> Result<(), Error> {
    formatter.write_fmt(format_args!("{}{}", self.size(), "#{"))
    .and_then(|_| fold(self.intervals.iter().map(|i|
      formatter.write_fmt(format_args!("{}", i))), (), |_,_|()))
    .and_then(|_|
      formatter.write_str("}"))
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
        format!("{} is not contained inside {}, but it should.", i, is));
    }
    for i in &outside {
      assert!(!is.contains(i),
        format!("{} is contained inside {}, but it should not.", i, is));
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

  fn test_result(test_id: String, result: &IntervalSet<i32>, expected: &IntervalSet<i32>) {
    assert!(result.intervals == expected.intervals,
      format!("{} | {} is different from the expected value: {}.", test_id, result, expected));
  }

  fn test_binary_op_sym<F>(test_id: String, a: Vec<(i32,i32)>, b: Vec<(i32,i32)>, op: F, expected: Vec<(i32,i32)>) where
    F: Fn(&IntervalSet<i32>, &IntervalSet<i32>) -> IntervalSet<i32>
  {
    test_binary_op(test_id.clone(), a.clone(), b.clone(), |i,j| op(i,j), expected.clone());
    test_binary_op(test_id, b, a, op, expected);
  }

  fn test_binary_op<F>(test_id: String, a: Vec<(i32,i32)>, b: Vec<(i32,i32)>, op: F, expected: Vec<(i32,i32)>) where
    F: Fn(&IntervalSet<i32>, &IntervalSet<i32>) -> IntervalSet<i32>
  {
    println!("Info: {}.", test_id);
    let a = make_interval_set(a);
    let b = make_interval_set(b);
    let expected = make_interval_set(expected);
    test_result(test_id, &op(&a, &b), &expected);
  }


  fn test_binary_value_op<F>(test_id: String, a: Vec<(i32,i32)>, b: i32, op: F, expected: Vec<(i32,i32)>) where
    F: Fn(&IntervalSet<i32>, i32) -> IntervalSet<i32>
  {
    println!("Info: {}.", test_id);
    let a = make_interval_set(a);
    let expected = make_interval_set(expected);
    test_result(test_id, &op(&a, b), &expected);
  }

  fn test_binary_bool_op_sym<F>(test_id: String, a: Vec<(i32,i32)>, b: Vec<(i32,i32)>, op: F, expected: bool) where
    F: Fn(&IntervalSet<i32>, &IntervalSet<i32>) -> bool
  {
    test_binary_bool_op(test_id.clone(), a.clone(), b.clone(), |i,j| op(i,j), expected);
    test_binary_bool_op(test_id, b, a, op, expected);
  }

  fn test_binary_bool_op<F>(test_id: String, a: Vec<(i32,i32)>, b: Vec<(i32,i32)>, op: F, expected: bool) where
    F: Fn(&IntervalSet<i32>, &IntervalSet<i32>) -> bool
  {
    println!("Info: {}.", test_id);
    let a = make_interval_set(a);
    let b = make_interval_set(b);
    assert_eq!(op(&a, &b), expected);
  }

  fn test_op<F>(test_id: String, a: Vec<(i32,i32)>, op: F, expected: Vec<(i32,i32)>) where
    F: Fn(&IntervalSet<i32>) -> IntervalSet<i32>
  {
    println!("Info: {}.", test_id);
    let a = make_interval_set(a);
    let expected = make_interval_set(expected);
    let result = op(&a);
    test_result(test_id, &result, &expected);
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

  #[test]
  fn test_difference() {
    // Note: the first number is the test id, so it should be easy to identify which test has failed.
    // The two first vectors are the operands and the two last are expected results (the first
    // for a.difference(b) and the second for b.difference(a)).
    let cases = vec![
      // identity tests
      (1, vec![], vec![], vec![], vec![]),
      (2, vec![], vec![(1,2)], vec![], vec![(1,2)]),
      (3, vec![], vec![(1,2),(7,9)], vec![], vec![(1,2),(7,9)]),
      (4, vec![(1,2),(7,9)], vec![(1,2)], vec![(7,9)], vec![]),
      (5, vec![(1,2),(7,9)], vec![(1,2),(7,9)], vec![], vec![]),
      // front tests
      (6, vec![(-3,-1)], vec![(1,2),(7,9)], vec![(-3,-1)], vec![(1,2),(7,9)]),
      (7, vec![(-3,0)], vec![(1,2),(7,9)], vec![(-3,0)], vec![(1,2),(7,9)]),
      (8, vec![(-3,1)], vec![(1,2),(7,9)], vec![(-3,0)], vec![(2,2),(7,9)]),
      // middle tests
      (9, vec![(2,7)], vec![(1,2),(7,9)], vec![(3,6)], vec![(1,1),(8,9)]),
      (10, vec![(3,7)], vec![(1,2),(7,9)], vec![(3,6)], vec![(1,2),(8,9)]),
      (11, vec![(4,5)], vec![(1,2),(7,9)], vec![(4,5)], vec![(1,2),(7,9)]),
      (12, vec![(2,8)], vec![(1,2),(7,9)], vec![(3,6)], vec![(1,1),(9,9)]),
      (13, vec![(2,6)], vec![(1,2),(7,9)], vec![(3,6)], vec![(1,1),(7,9)]),
      (14, vec![(3,6)], vec![(1,2),(7,9)], vec![(3,6)], vec![(1,2),(7,9)]),
      // back tests
      (15, vec![(8,9)], vec![(1,2),(7,9)], vec![], vec![(1,2),(7,7)]),
      (16, vec![(8,10)], vec![(1,2),(7,9)], vec![(10,10)], vec![(1,2),(7,7)]),
      (17, vec![(9,10)], vec![(1,2),(7,9)], vec![(10,10)], vec![(1,2),(7,8)]),
      (18, vec![(6,10)], vec![(1,2),(7,9)], vec![(6,6),(10,10)], vec![(1,2)]),
      (19, vec![(10,11)], vec![(1,2),(7,9)], vec![(10,11)], vec![(1,2),(7,9)]),
      (20, vec![(11,12)], vec![(1,2),(7,9)], vec![(11,12)], vec![(1,2),(7,9)]),
      // mixed tests
      (21, vec![(-3,-1),(4,5),(11,12)], vec![(1,2),(7,9)], vec![(-3,-1),(4,5),(11,12)], vec![(1,2),(7,9)]),
      (22, vec![(-3,0),(3,6),(10,11)], vec![(1,2),(7,9)], vec![(-3,0),(3,6),(10,11)], vec![(1,2),(7,9)]),
      (23, vec![(-3,1),(3,7),(9,11)], vec![(1,2),(7,9)], vec![(-3,0),(3,6),(10,11)], vec![(2,2),(8,8)]),
      (24, vec![(-3,5),(7,11)], vec![(1,2),(7,9)], vec![(-3,0),(3,5),(10,11)], vec![]),
      (25, vec![(-3,5),(7,8),(12,12)], vec![(1,2),(7,9)], vec![(-3,0),(3,5),(12,12)], vec![(9,9)]),
      // englobing tests
      (26, vec![(-1,11)], vec![(1,2),(7,9)], vec![(-1,0),(3,6),(10,11)], vec![]),
    ];

    for (id, a, b, expected, expected_sym) in cases {
      test_binary_op(format!("test #{} of difference", id), a.clone(), b.clone(), |x,y| x.difference(y), expected);
      test_binary_op(format!("test #{} of difference", id), b, a, |x,y| x.difference(y), expected_sym);
    }
  }

  #[test]
  fn test_symmetric_difference() {
    // Note: the first number is the test id, so it should be easy to identify which test has failed.
    // The two first vectors are the operands and the expected result is last.
    let sym_cases = vec![
      // identity tests
      (1, vec![], vec![], vec![]),
      (2, vec![], vec![(1,2)], vec![(1,2)]),
      (3, vec![], vec![(1,2),(7,9)], vec![(1,2),(7,9)]),
      (4, vec![(1,2),(7,9)], vec![(1,2)], vec![(7,9)]),
      (5, vec![(1,2),(7,9)], vec![(1,2),(7,9)], vec![]),
      // front tests
      (6, vec![(-3,-1)], vec![(1,2),(7,9)], vec![(-3,-1),(1,2),(7,9)]),
      (7, vec![(-3,0)], vec![(1,2),(7,9)], vec![(-3,2),(7,9)]),
      (8, vec![(-3,1)], vec![(1,2),(7,9)], vec![(-3,0),(2,2),(7,9)]),
      // middle tests
      (9, vec![(2,7)], vec![(1,2),(7,9)], vec![(1,1),(3,6),(8,9)]),
      (10, vec![(3,7)], vec![(1,2),(7,9)], vec![(1,6),(8,9)]),
      (11, vec![(4,5)], vec![(1,2),(7,9)], vec![(1,2),(4,5),(7,9)]),
      (12, vec![(2,8)], vec![(1,2),(7,9)], vec![(1,1),(3,6),(9,9)]),
      (13, vec![(2,6)], vec![(1,2),(7,9)], vec![(1,1),(3,9)]),
      (14, vec![(3,6)], vec![(1,2),(7,9)], vec![(1,9)]),
      // back tests
      (15, vec![(8,9)], vec![(1,2),(7,9)], vec![(1,2),(7,7)]),
      (16, vec![(8,10)], vec![(1,2),(7,9)], vec![(1,2),(7,7),(10,10)]),
      (17, vec![(9,10)], vec![(1,2),(7,9)], vec![(1,2),(7,8),(10,10)]),
      (18, vec![(6,10)], vec![(1,2),(7,9)], vec![(1,2),(6,6),(10,10)]),
      (19, vec![(10,11)], vec![(1,2),(7,9)], vec![(1,2),(7,11)]),
      (20, vec![(11,12)], vec![(1,2),(7,9)], vec![(1,2),(7,9),(11,12)]),
      // mixed tests
      (21, vec![(-3,-1),(4,5),(11,12)], vec![(1,2),(7,9)], vec![(-3,-1),(1,2),(4,5),(7,9),(11,12)]),
      (22, vec![(-3,0),(3,6),(10,11)], vec![(1,2),(7,9)], vec![(-3,11)]),
      (23, vec![(-3,1),(3,7),(9,11)], vec![(1,2),(7,9)], vec![(-3,0),(2,6),(8,8),(10,11)]),
      (24, vec![(-3,5),(7,11)], vec![(1,2),(7,9)], vec![(-3,0),(3,5),(10,11)]),
      (25, vec![(-3,5),(7,8),(12,12)], vec![(1,2),(7,9)], vec![(-3,0),(3,5),(9,9),(12,12)]),
      // englobing tests
      (26, vec![(-1,11)], vec![(1,2),(7,9)], vec![(-1,0),(3,6),(10,11)]),
    ];

    for (id, a, b, expected) in sym_cases {
      test_binary_op_sym(format!("test #{} of symmetric difference", id),
        a, b, |x,y| x.symmetric_difference(y), expected);
    }
  }

  #[test]
  fn test_overlap() {
    // Note: the first number is the test id, so it should be easy to identify which test has failed.
    // The two first vectors are the operands and the expected result is last.
    let sym_cases = vec![
      // identity tests
      (1, vec![], vec![], false),
      (2, vec![], vec![(1,2)], false),
      (3, vec![], vec![(1,2),(7,9)], false),
      (4, vec![(1,2),(7,9)], vec![(1,2)], true),
      (5, vec![(1,2),(7,9)], vec![(1,2),(7,9)], true),
      // front tests
      (6, vec![(-3,-1)], vec![(1,2),(7,9)], false),
      (7, vec![(-3,0)], vec![(1,2),(7,9)], false),
      (8, vec![(-3,1)], vec![(1,2),(7,9)], true),
      // middle tests
      (9, vec![(2,7)], vec![(1,2),(7,9)], true),
      (10, vec![(3,7)], vec![(1,2),(7,9)], true),
      (11, vec![(4,5)], vec![(1,2),(7,9)], false),
      (12, vec![(2,8)], vec![(1,2),(7,9)], true),
      (13, vec![(2,6)], vec![(1,2),(7,9)], true),
      (14, vec![(3,6)], vec![(1,2),(7,9)], false),
      // back tests
      (15, vec![(8,9)], vec![(1,2),(7,9)], true),
      (16, vec![(8,10)], vec![(1,2),(7,9)], true),
      (17, vec![(9,10)], vec![(1,2),(7,9)], true),
      (18, vec![(6,10)], vec![(1,2),(7,9)], true),
      (19, vec![(10,11)], vec![(1,2),(7,9)], false),
      (20, vec![(11,12)], vec![(1,2),(7,9)], false),
      // mixed tests
      (21, vec![(-3,-1),(4,5),(11,12)], vec![(1,2),(7,9)], false),
      (22, vec![(-3,0),(3,6),(10,11)], vec![(1,2),(7,9)], false),
      (23, vec![(-3,1),(3,7),(9,11)], vec![(1,2),(7,9)], true),
      (24, vec![(-3,5),(7,11)], vec![(1,2),(7,9)], true),
      (25, vec![(-3,5),(7,8),(12,12)], vec![(1,2),(7,9)], true),
      // englobing tests
      (26, vec![(-1,11)], vec![(1,2),(7,9)], true),
    ];

    for (id, a, b, expected) in sym_cases {
      test_binary_bool_op_sym(format!("test #{} of overlap", id),
        a.clone(), b.clone(), |x,y| x.overlap(y), expected);
      test_binary_bool_op_sym(format!("test #{} of is_disjoint", id),
        a, b, |x,y| x.is_disjoint(y), !expected);
    }
  }

  #[test]
  fn test_shrink() {
    let min = <i32 as Width>::min_value();
    let max = <i32 as Width>::max_value();

    // Second and third args are the test value.
    // The fourth is the result of a shrink_left and the fifth of a shrink_right.
    let cases = vec![
      (1, vec![], 0, vec![], vec![]),
      (2, vec![(min, max)], 0, vec![(0, max)], vec![(min,0)]),
      (3, vec![(0,0)], 0, vec![(0,0)], vec![(0,0)]),
      (4, vec![(0,0)], -1, vec![(0,0)], vec![]),
      (5, vec![(0,0)], 1, vec![], vec![(0,0)]),
      (6, vec![(-5,5)], 0, vec![(0,5)], vec![(-5,0)]),
      (7, vec![(-5,5)], -5, vec![(-5,5)], vec![(-5,-5)]),
      (8, vec![(-5,5)], 5, vec![(5,5)], vec![(-5,5)]),
      (9, vec![(-5,-1),(1,5)], 0, vec![(1,5)], vec![(-5,-1)]),
      (10, vec![(-5,-1),(1,5)], 1, vec![(1,5)], vec![(-5,-1),(1,1)]),
      (11, vec![(-5,-1),(1,5)], -1, vec![(-1,-1),(1,5)], vec![(-5,-1)]),
      (12, vec![(min,-1),(1,5)], min, vec![(min,-1),(1,5)], vec![(min,min)]),
      (13, vec![(min,-1),(1,5)], max, vec![], vec![(min,-1),(1,5)]),
      (14, vec![(-5,-1),(1,max)], max, vec![(max, max)], vec![(-5,-1),(1,max)]),
      (15, vec![(min,-1),(1,max)], 0, vec![(1, max)], vec![(min, -1)]),
      (16, vec![(-5,-3),(0,1),(3,5)], 1, vec![(1,1),(3,5)], vec![(-5,-3),(0,1)])
    ];

    for (id, a, v, expected_left, expected_right) in cases {
      test_binary_value_op(format!("test #{} of shrink_left", id),
        a.clone(), v, |x, v| x.shrink_left(v), expected_left);
      test_binary_value_op(format!("test #{} of shrink_right", id),
        a, v, |x, v| x.shrink_right(v), expected_right);
    }
  }

  #[test]
  fn test_subset() {
    // Note: the first number is the test id, so it should be easy to identify which test has failed.
    // The two first vectors are the operands and the four last are expected results (resp.
    // `a.is_subset(b)`, `b.is_subset(a)`, `a.is_proper_subset(b)` and `b.is_proper_subset(a)`.
    let cases = vec![
      // identity tests
      (1, vec![], vec![], true, true, false, false),
      (2, vec![], vec![(1,2)], true, false, true, false),
      (3, vec![], vec![(1,2),(7,9)], true, false, true, false),
      (4, vec![(1,2),(7,9)], vec![(1,2)], false, true, false, true),
      (5, vec![(1,2),(7,9)], vec![(1,2),(7,9)], true, true, false, false),
      // middle tests
      (6, vec![(2,7)], vec![(1,2),(7,9)], false, false, false, false),
      (7, vec![(3,7)], vec![(1,2),(7,9)], false, false, false, false),
      (8, vec![(4,5)], vec![(1,2),(7,9)], false, false, false, false),
      (9, vec![(2,8)], vec![(1,2),(7,9)], false, false, false, false),
      // mixed tests
      (10, vec![(-3,-1),(4,5),(11,12)], vec![(-2,-1),(7,9)], false, false, false, false),
      (11, vec![(-3,0),(3,6),(10,11)], vec![(-2,-1),(4,4),(10,10)], false, true, false, true),
      (12, vec![(-3,0),(3,6),(10,11)], vec![(-3,0),(3,6),(10,11)], true, true, false, false),
      // englobing tests
      (13, vec![(-1,11)], vec![(1,2),(7,9)], false, true, false, true),
    ];

    for (id, a, b, expected, expected_sym, expected_proper, expected_proper_sym) in cases {
      test_binary_bool_op(format!("test #{} of subset", id), a.clone(), b.clone(), |x,y| x.is_subset(y), expected);
      test_binary_bool_op(format!("test #{} of subset", id), b.clone(), a.clone(), |x,y| x.is_subset(y), expected_sym);
      test_binary_bool_op(format!("test #{} of proper subset", id), a.clone(), b.clone(), |x,y| x.is_proper_subset(y), expected_proper);
      test_binary_bool_op(format!("test #{} of proper subset", id), b.clone(), a.clone(), |x,y| x.is_proper_subset(y), expected_proper_sym);
    }
  }

  #[test]
  fn test_arithmetics() {
    // Second and third args are the test values.
    // 4, 5, 6 and 7 are the results of `a + b`, `a - b`, `b - a` and `a * b`
    let cases = vec![
      (1, vec![], vec![], vec![], vec![], vec![], vec![]),
      (2, vec![], vec![(1,1),(3,5)], vec![], vec![], vec![], vec![]),
      (3, vec![(1,1),(3,5)], vec![(0,0)], vec![(1,1),(3,5)], vec![(1,1),(3,5)], vec![(-5,-3),(-1,-1)], vec![(0,0)]),
      (4, vec![(1,1),(3,5)], vec![(1,1)], vec![(2,2),(4,6)], vec![(0,0),(2,4)], vec![(-4,-2),(0,0)], vec![(1,1),(3,5)]),
      (5, vec![(1,1),(3,5)], vec![(0,1),(4,5)],
        vec![(1,10)],
        vec![(-4,5)],
        vec![(-5,4)],
        vec![(0,5),(12,25)]),
    ];

    for (id, a, b, e_add, e_sub, e_sub_sym, e_mul) in cases {
      test_binary_op_sym(format!("test #{} of `a+b`", id),
        a.clone(), b.clone(), |x,y| x + y, e_add);
      test_binary_op(format!("test #{} of `a-b`", id),
        a.clone(), b.clone(), |x,y| x - y, e_sub);
      test_binary_op(format!("test #{} of `b-a`", id),
        b.clone(), a.clone(), |x,y| x - y, e_sub_sym);
      test_binary_op_sym(format!("test #{} of `a*b`", id),
        a.clone(), b.clone(), |x,y| x * y, e_mul);
    }
  }

  #[test]
  fn test_arithmetics_bound() {
    let i1_35 = vec![(1,1),(3,5)];
    // Second and third args are the test value.
    // 4, 5 and 6 are the results of `a + b`, `a - b` and `a * b`
    let cases = vec![
      (1, vec![], 0, vec![], vec![], vec![]),
      (2, vec![(0,0)], 0, vec![(0,0)], vec![(0,0)], vec![(0,0)]),
      (3, i1_35.clone(), 0, i1_35.clone(), i1_35.clone(), vec![(0,0)]),
      (4, vec![], 1, vec![], vec![], vec![]),
      (5, vec![(0,0)], 1, vec![(1,1)], vec![(-1,-1)], vec![(0,0)]),
      (6, i1_35.clone(), 1, vec![(2,2),(4,6)], vec![(0,0),(2,4)], i1_35.clone()),
      (7, vec![], 3, vec![], vec![], vec![]),
      (8, vec![(0,0)], 3, vec![(3,3)], vec![(-3,-3)], vec![(0,0)]),
      (9, i1_35.clone(), 3, vec![(4,4),(6,8)], vec![(-2,-2),(0,2)], vec![(3,3),(9,15)])
    ];

    for (id, a, b, e_add, e_sub, e_mul) in cases {
      test_binary_value_op(format!("test #{} of `a+b`", id),
        a.clone(), b.clone(), |x,y| x + y, e_add);
      test_binary_value_op(format!("test #{} of `a-b`", id),
        a.clone(), b.clone(), |x,y| x - y, e_sub);
      test_binary_value_op(format!("test #{} of `a*b`", id),
        a.clone(), b.clone(), |x,y| x * y, e_mul);
    }
  }
}
