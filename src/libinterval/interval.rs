// Copyright 2015 Pierre Talbot (IRCAM)

// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Closed and bounded generic interval.
//!
//! Let `D` be an ordered set and `{i,j} ∈ D`. The interval `I` whose bounds are `{i,j}` is defined as `I = {x ∈ D | i <= x <= j}` and is denoted as `[i..j]`. Only interval with bound types implementing `Num` and `Width` is currently available.
//!
//! Most of the operations in `gcollections::ops::*` are implemented. Intervals specific operations, proposed in `ops::*`, are also implemented. There is no `union` operation since this interval representation is not precise enough, and so an union could be over-approximated. For example, consider `[1..2] U [5..6]`, the only possible representation is `[1..6]` which is not exact by the definition of union of sets. However, this operation exists and is named `hull`.
//!
//! # Examples
//!
//! ```rust
//! use crate::interval::Interval;
//! use crate::interval::ops::*;
//! use gcollections::ops::*;
//!
//! # fn main() {
//! let a = Interval::new(0, 5);
//! let b = Interval::singleton(10);
//!
//! let c = a.hull(&b);
//! let d = c.difference(&a);
//!
//! assert_eq!(c, Interval::new(0,10));
//! assert_eq!(d, Interval::new(6,10));
//! # }
//! ```
//!
//! # See also
//! [interval set](../interval_set/index.html).

use crate::ops::*;
use gcollections::ops::*;
use gcollections::*;
use serde::de::{self, SeqAccess, Visitor};
use serde::ser::SerializeTuple;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use trilean::SKleene;

use num_traits::{Num, Zero};
use std::cmp::{max, min};
use std::fmt::{self, Display, Error, Formatter};
use std::marker::PhantomData;
use std::ops::{Add, Mul, RangeFrom, RangeInclusive, RangeToInclusive, Sub};

/// Closed interval (endpoints included).
#[derive(Debug, Copy, Clone)]
pub struct Interval<Bound> {
    lb: Bound,
    ub: Bound,
}

impl<Bound> Serialize for Interval<Bound>
where
    Bound: Serialize + Width + Num,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        if self.is_empty() {
            serializer.serialize_none()
        } else {
            let mut tuple = serializer.serialize_tuple(2)?;
            tuple.serialize_element(&self.lb)?;
            tuple.serialize_element(&self.ub)?;
            tuple.end()
        }
    }
}

impl<'de, Bound> Deserialize<'de> for Interval<Bound>
where
    Bound: Width + Num + Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct IntervalVisitor<Bound> {
            marker: PhantomData<fn() -> Bound>,
        }
        impl<Bound> IntervalVisitor<Bound> {
            fn new() -> Self {
                IntervalVisitor {
                    marker: PhantomData,
                }
            }
        }
        impl<'de, Bound> Visitor<'de> for IntervalVisitor<Bound>
        where
            Bound: Width + Deserialize<'de> + Num,
        {
            type Value = Interval<Bound>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("tuple of two numbers or none")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let lower = seq
                    .next_element::<Bound>()?
                    .ok_or_else(|| de::Error::invalid_length(0, &self))?;
                let upper = seq
                    .next_element::<Bound>()?
                    .ok_or_else(|| de::Error::invalid_length(1, &self))?;
                let mut extra_elements = 0;
                while seq.next_element::<de::IgnoredAny>()?.is_some() {
                    extra_elements += 1;
                }
                if extra_elements > 0 {
                    return Err(de::Error::invalid_length(2 + extra_elements, &self));
                }
                Ok(Interval::new(lower, upper))
            }

            fn visit_none<E>(self) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(Interval::<Bound>::empty())
            }
        }
        deserializer.deserialize_any(IntervalVisitor::new())
    }
}

impl<Bound> IntervalKind for Interval<Bound> {}

impl<Bound> Collection for Interval<Bound> {
    type Item = Bound;
}

impl<Bound> Interval<Bound>
where
    Bound: Width + Num,
{
    fn into_optional(self) -> Optional<Bound> {
        if self.is_empty() {
            Optional::empty()
        } else if self.is_singleton() {
            Optional::singleton(self.lb)
        } else {
            panic!("Only empty interval or singleton can be transformed into an option.");
        }
    }
}

impl<Bound: Width + Num> Eq for Interval<Bound> {}

impl<Bound> PartialEq<Interval<Bound>> for Interval<Bound>
where
    Bound: Width + Num,
{
    /// Checks whether two intervals are equal.
    /// The bounds must be the same.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(8, 24), Interval::new(8, 24));
    /// assert_ne!(Interval::new(6, 9), Interval::new(6, 10));
    /// ```
    /// Any pair of empty intervals are equal to each other but no other interval.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::<usize>::empty(), Interval::<usize>::empty());
    /// assert_ne!(Interval::new(0, 1), Interval::empty());
    /// assert_ne!(Interval::empty(), Interval::singleton(11));
    /// ```
    fn eq(&self, other: &Interval<Bound>) -> bool {
        if self.is_empty() && other.is_empty() {
            true
        } else {
            self.lb == other.lb && self.ub == other.ub
        }
    }
}

impl<Bound> Interval<Bound>
where
    Bound: Clone,
{
    fn low(&self) -> Bound {
        self.lb.clone()
    }
    fn up(&self) -> Bound {
        self.ub.clone()
    }
}

impl<Bound> Interval<Bound>
where
    Bound: Width + Num,
{
    fn min_lb(ub: Bound) -> Interval<Bound> {
        Interval::new(<Bound as Width>::min_value(), ub)
    }

    fn max_ub(lb: Bound) -> Interval<Bound> {
        Interval::new(lb, <Bound as Width>::max_value())
    }
}

impl<Bound> Range for Interval<Bound>
where
    Bound: Width,
{
    /// Constructs an interval with the lower and upper bound (inclusive).
    /// ```
    /// # use interval::prelude::*;
    /// let interval = Interval::new(3, 8);
    /// assert_eq!(interval.lower(), 3);
    /// assert_eq!(interval.upper(), 8);
    /// assert!(interval.contains(&3));
    /// assert!(!interval.contains(&2));
    /// assert!(interval.contains(&8));
    /// assert!(!interval.contains(&9));
    /// assert!(!interval.is_empty());
    /// ```
    /// For intervals containing a single value, the [`Interval::singleton`] constructor is preferred.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(6, 6), Interval::singleton(6));
    /// ```
    /// For an empty interval, use the [`Interval::empty`] constructor.
    ///
    /// The bounds of the constructor are bounded by [`Interval::whole`].
    /// This means that not all possible intervals can be constructed.
    /// ```should_panic
    /// # use interval::prelude::*;
    /// Interval::<u8>::new(0, 255); // panics!
    /// Interval::<u8>::new(0, 254); // constructs normally
    ///
    /// Interval::<i8>::new(-128, 127); // panics!
    /// Interval::<i8>::new(-127, 127); // constructs normally
    /// ```
    fn new(lb: Bound, ub: Bound) -> Interval<Bound> {
        debug_assert!(
            lb >= <Bound as Width>::min_value(),
            "Lower bound exceeds the minimum value of a bound."
        );
        debug_assert!(
            ub <= <Bound as Width>::max_value(),
            "Upper bound exceeds the maximum value of a bound."
        );
        Interval { lb, ub }
    }
}

impl<Bound> Bounded for Interval<Bound>
where
    Bound: Num + Width + Clone,
{
    /// Returns the lower bound of an interval.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(8, 20).lower(), 8);
    /// assert_eq!(Interval::singleton(4).lower(), 4);
    /// ```
    /// However, this will panic on an empty interval.
    /// ```should_panic
    /// # use interval::prelude::*;
    /// Interval::<u8>::empty().lower(); // panics!
    /// ```
    fn lower(&self) -> Bound {
        debug_assert!(
            !self.is_empty(),
            "Cannot access lower bound on empty interval."
        );
        self.low()
    }

    /// Returns the upper bound of an interval.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(8, 20).upper(), 20);
    /// assert_eq!(Interval::singleton(4).upper(), 4);
    /// ```
    /// However, this will panic on an empty interval.
    /// ```should_panic
    /// # use interval::prelude::*;
    /// Interval::<u8>::empty().upper(); // panics!
    /// ```
    fn upper(&self) -> Bound {
        debug_assert!(
            !self.is_empty(),
            "Cannot access upper bound on empty interval."
        );
        self.up()
    }
}

impl<Bound> Singleton for Interval<Bound>
where
    Bound: Width + Clone,
{
    /// Constructs an interval containing a single value - the lower and upper bounds are the same.
    /// ```
    /// # use interval::prelude::*;
    /// let interval_5 = Interval::singleton(5);
    /// assert_eq!(interval_5.size(), 1 as u32);
    /// assert_eq!(interval_5.lower(), interval_5.upper());
    /// assert!(interval_5.contains(&5));
    /// assert!(!interval_5.is_empty());
    /// ```
    fn singleton(x: Bound) -> Interval<Bound> {
        Interval::new(x.clone(), x)
    }
}

impl<Bound> Empty for Interval<Bound>
where
    Bound: Width + Num,
{
    /// Constructs an empty interval.
    /// The type needs to be specified or inferred as `Interval` is parametrized by its input.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::<i32>::empty().size(), 0);
    /// assert_eq!(Interval::<u32>::empty().size(), 0);
    /// assert!(Interval::<u16>::empty().is_empty());
    /// ```
    fn empty() -> Interval<Bound> {
        Interval::new(Bound::one(), Bound::zero())
    }
}

impl<Bound> Whole for Interval<Bound>
where
    Bound: Width + Num,
{
    /// Calculates the maximum range of an interval.
    ///
    /// For an unsigned integer, this sets the minimum of the interval to the minimum of the type (e.g. `u32::min_value()`)
    /// and the maximum to one less than the maximum value (e.ge `u32::max_value() - 1`).
    ///
    /// For a signed integer, this sets the minimum of the interval to one more than the minimum of the type (e.g. `i32::min_value() + 1`)
    /// and the maximum to than the maximum value (e.ge `i32::max_value()`).
    /// This ensures that it is always possible to calculate the width without overflow (using the same number of bits).
    /// ```
    /// # use interval::prelude::*;
    /// // u8: 0 <-> 255
    /// assert_eq!(Interval::<u8>::whole(), Interval::new(0, 254));
    /// // i8: -128 <-> 127
    /// assert_eq!(Interval::<i8>::whole(), Interval::new(-127, 127));
    /// assert_eq!(Interval::<usize>::whole(), Interval::new(usize::min_value(), usize::max_value() - 1));
    /// assert_eq!(Interval::<isize>::whole(), Interval::new(isize::min_value() + 1, isize::max_value()));
    /// ```
    fn whole() -> Interval<Bound> {
        Interval::new(<Bound as Width>::min_value(), <Bound as Width>::max_value())
    }
}

/// `IsSingleton` and `IsEmpty` are defined automatically in `gcollections`.
impl<Bound> Cardinality for Interval<Bound>
where
    Bound: Width + Num,
{
    type Size = <Bound as Width>::Output;

    /// Calculates the size of an interval (the number of integers it contains).
    /// This includes both endpoints.
    /// The size of the interval is unsigned, but has the same number of bits as the interval bounds.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::<i32>::new(1, 10).size(), 10 as u32);
    /// assert_eq!(Interval::<usize>::new(1, 10).size(), 10 as usize);
    /// // Default is to use i32.
    /// assert_eq!(Interval::singleton(5).size(), 1 as u32);
    /// assert_eq!(Interval::<i64>::empty().size(), 0);
    /// // Doesn't overflow:
    /// assert_eq!(Interval::<usize>::whole().size(), usize::max_value());
    /// ```
    fn size(&self) -> <Bound as Width>::Output {
        if self.lb > self.ub {
            <<Bound as Width>::Output>::zero()
        } else {
            Bound::width(&self.lb, &self.ub)
        }
    }
}

impl<Bound> Disjoint for Interval<Bound>
where
    Bound: Width + Num,
{
    /// Calculates whether two intervals do *not* overlap.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(8, 9).is_disjoint(&Interval::new(1, 2)), true);
    /// assert_eq!(Interval::new(1, 5).is_disjoint(&Interval::new(3, 4)), false);
    /// assert_eq!(Interval::new(3, 5).is_disjoint(&Interval::new(5, 7)), false);
    /// assert_eq!(Interval::new(3, 3).is_disjoint(&Interval::new(3, 3)), false);
    /// assert_eq!(Interval::empty().is_disjoint(&Interval::new(2, 3)), true);
    /// assert_eq!(Interval::new(4, 6).is_disjoint(&Interval::empty()), true);
    /// assert_eq!(Interval::<usize>::empty().is_disjoint(&Interval::empty()), true);
    /// ```
    fn is_disjoint(&self, other: &Interval<Bound>) -> bool {
        self.is_empty() || other.is_empty() || self.lb > other.ub || other.lb > self.ub
    }
}

impl<Bound> Disjoint<Bound> for Interval<Bound>
where
    Bound: Num + Ord,
{
    /// Calculates whether a value is excluded from an interval.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(8, 9).is_disjoint(&1), true);
    /// assert_eq!(Interval::new(1, 5).is_disjoint(&3), false);
    /// assert_eq!(Interval::new(3, 5).is_disjoint(&5), false);
    /// assert_eq!(Interval::new(3, 3).is_disjoint(&3), false);
    /// assert_eq!(Interval::empty().is_disjoint(&6), true);
    /// ```
    fn is_disjoint(&self, value: &Bound) -> bool {
        !self.contains(value)
    }
}

macro_rules! primitive_interval_disjoint
{
  ( $( $source:ty ),* ) =>
  {$(
    impl Disjoint<Interval<$source>> for $source
    {
      #[doc = concat!(
        r#"
        Calculates whether a value is excluded from an interval.
        ```
        # use interval::prelude::*;
        assert_eq!((1 as "#, stringify!($source), r#").is_disjoint(&Interval::new(8, 9)), true);
        assert_eq!((3 as "#, stringify!($source), r#").is_disjoint(&Interval::new(1, 5)), false);
        assert_eq!((5 as "#, stringify!($source), r#").is_disjoint(&Interval::new(3, 5)), false);
        assert_eq!((3 as "#, stringify!($source), r#").is_disjoint(&Interval::new(3, 3)), false);
        assert_eq!((6 as "#, stringify!($source), r#").is_disjoint(&Interval::empty()), true);
        ```
        "#
      )]
      fn is_disjoint(&self, value: &Interval<$source>) -> bool {
        value.is_disjoint(self)
      }
    }
  )*}
}

primitive_interval_disjoint!(i8, u8, i16, u16, i32, u32, i64, u64, isize, usize);

impl<Bound> Disjoint<Optional<Bound>> for Interval<Bound>
where
    Bound: Num + Ord,
{
    /// Calculates whether an optional is excluded from an interval.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(8, 9).is_disjoint(&Optional::singleton(1)), true);
    /// assert_eq!(Interval::new(1, 5).is_disjoint(&Optional::singleton(3)), false);
    /// assert_eq!(Interval::new(3, 5).is_disjoint(&Optional::singleton(5)), false);
    /// assert_eq!(Interval::new(3, 3).is_disjoint(&Optional::singleton(3)), false);
    /// assert_eq!(Interval::<usize>::empty().is_disjoint(&Optional::singleton(6)), true);
    /// assert_eq!(Interval::new(4, 7).is_disjoint(&Optional::empty()), true);
    /// assert_eq!(Interval::<isize>::empty().is_disjoint(&Optional::empty()), true);
    /// ```
    fn is_disjoint(&self, value: &Optional<Bound>) -> bool {
        value.as_ref().map_or(true, |x| self.is_disjoint(x))
    }
}

macro_rules! optional_interval_disjoint
{
  ( $( $source:ty ),* ) =>
  {$(
    impl Disjoint<Interval<$source>> for Optional<$source>
    {
      #[doc = concat!(
        r#"
        Calculates whether an optional is excluded from an interval.
        ```
        # use interval::prelude::*;
        assert_eq!(Optional::<"#, stringify!($source), r#">::singleton(1).is_disjoint(&Interval::new(8, 9)), true);
        assert_eq!(Optional::<"#, stringify!($source), r#">::singleton(3).is_disjoint(&Interval::new(1, 5)), false);
        assert_eq!(Optional::<"#, stringify!($source), r#">::singleton(5).is_disjoint(&Interval::new(3, 5)), false);
        assert_eq!(Optional::<"#, stringify!($source), r#">::singleton(3).is_disjoint(&Interval::new(3, 3)), false);
        assert_eq!(Optional::<"#, stringify!($source), r#">::singleton(6).is_disjoint(&Interval::empty()), true);
        assert_eq!(Optional::<"#, stringify!($source), r#">::empty().is_disjoint(&Interval::new(4, 7)), true);
        assert_eq!(Optional::<"#, stringify!($source), r#">::empty().is_disjoint(&Interval::empty()), true);
        ```
        "#
      )]
      fn is_disjoint(&self, value: &Interval<$source>) -> bool {
        value.is_disjoint(self)
      }
    }
  )*}
}

optional_interval_disjoint!(i8, u8, i16, u16, i32, u32, i64, u64, isize, usize);

impl<Bound> Overlap for Interval<Bound>
where
    Bound: Width + Num,
{
    /// Calculates whether two intervals overlap.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(8, 9).overlap(&Interval::new(1, 2)), false);
    /// assert_eq!(Interval::new(1, 5).overlap(&Interval::new(3, 4)), true);
    /// assert_eq!(Interval::new(3, 5).overlap(&Interval::new(5, 7)), true);
    /// assert_eq!(Interval::new(3, 3).overlap(&Interval::new(3, 3)), true);
    /// assert_eq!(Interval::empty().overlap(&Interval::new(2, 3)), false);
    /// assert_eq!(Interval::new(4, 6).overlap(&Interval::empty()), false);
    /// assert_eq!(Interval::<usize>::empty().overlap(&Interval::empty()), false);
    /// ```
    fn overlap(&self, other: &Interval<Bound>) -> bool {
        !self.is_disjoint(other)
    }
}

impl<Bound> Overlap<Bound> for Interval<Bound>
where
    Bound: Width + Num,
{
    /// Calculates whether a value is included in an interval.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(8, 9).overlap(&1), false);
    /// assert_eq!(Interval::new(1, 5).overlap(&3), true);
    /// assert_eq!(Interval::new(3, 5).overlap(&5), true);
    /// assert_eq!(Interval::new(3, 3).overlap(&3), true);
    /// assert_eq!(Interval::empty().overlap(&6), false);
    /// ```
    fn overlap(&self, other: &Bound) -> bool {
        !self.is_disjoint(other)
    }
}

impl<Bound> Overlap<Optional<Bound>> for Interval<Bound>
where
    Bound: Width + Num,
{
    /// Calculates whether an optional is included from an interval.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(8, 9).overlap(&Optional::singleton(1)), false);
    /// assert_eq!(Interval::new(1, 5).overlap(&Optional::singleton(3)), true);
    /// assert_eq!(Interval::new(3, 5).overlap(&Optional::singleton(5)), true);
    /// assert_eq!(Interval::new(3, 3).overlap(&Optional::singleton(3)), true);
    /// assert_eq!(Interval::<usize>::empty().overlap(&Optional::singleton(6)), false);
    /// assert_eq!(Interval::new(4, 7).overlap(&Optional::empty()), false);
    /// assert_eq!(Interval::<isize>::empty().overlap(&Optional::empty()), false);
    /// ```
    fn overlap(&self, other: &Optional<Bound>) -> bool {
        !self.is_disjoint(other)
    }
}

macro_rules! primitive_interval_overlap
{
  ( $( $source:ty ),* ) =>
  {$(
    impl Overlap<Interval<$source>> for $source
    {
      #[doc = concat!(
        r#"
        Calculates whether a value is included in an interval.
        ```
        # use interval::prelude::*;
        assert_eq!((1 as "#, stringify!($source), r#").overlap(&Interval::new(8, 9)), false);
        assert_eq!((3 as "#, stringify!($source), r#").overlap(&Interval::new(1, 5)), true);
        assert_eq!((5 as "#, stringify!($source), r#").overlap(&Interval::new(3, 5)), true);
        assert_eq!((3 as "#, stringify!($source), r#").overlap(&Interval::new(3, 3)), true);
        assert_eq!((6 as "#, stringify!($source), r#").overlap(&Interval::empty()), false);
        ```
        "#
      )]
      fn overlap(&self, other: &Interval<$source>) -> bool {
        !self.is_disjoint(other)
      }
    }
  )*}
}

primitive_interval_overlap!(i8, u8, i16, u16, i32, u32, i64, u64, isize, usize);

macro_rules! optional_interval_overlap
{
  ( $( $source:ty ),* ) =>
  {$(
    impl Overlap<Interval<$source>> for Optional<$source>
    {
      #[doc = concat!(
        r#"
        Calculates whether an optional is included in an interval.
        ```
        # use interval::prelude::*;
        assert_eq!(Optional::<"#, stringify!($source), r#">::singleton(1).overlap(&Interval::new(8, 9)), false);
        assert_eq!(Optional::<"#, stringify!($source), r#">::singleton(3).overlap(&Interval::new(1, 5)), true);
        assert_eq!(Optional::<"#, stringify!($source), r#">::singleton(5).overlap(&Interval::new(3, 5)), true);
        assert_eq!(Optional::<"#, stringify!($source), r#">::singleton(3).overlap(&Interval::new(3, 3)), true);
        assert_eq!(Optional::<"#, stringify!($source), r#">::singleton(6).overlap(&Interval::empty()), false);
        assert_eq!(Optional::<"#, stringify!($source), r#">::empty().overlap(&Interval::new(4, 7)), false);
        assert_eq!(Optional::<"#, stringify!($source), r#">::empty().overlap(&Interval::empty()), false);
        ```
        "#
      )]
      fn overlap(&self, other: &Interval<$source>) -> bool {
        !self.is_disjoint(other)
      }
    }
  )*}
}

optional_interval_overlap!(i8, u8, i16, u16, i32, u32, i64, u64, isize, usize);

impl<Bound> Hull for Interval<Bound>
where
    Bound: Width + Num,
{
    type Output = Interval<Bound>;

    /// Calculates the smallest interval containing two intervals.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::hull(&Interval::new(1, 3), &Interval::new(5, 8)), Interval::new(1, 8));
    /// assert_eq!(Interval::new(1, 3).hull(&Interval::new(5, 8)), Interval::new(1, 8));
    /// assert_eq!(Interval::new(1, 6).hull(&Interval::new(4, 7)), Interval::new(1, 7));
    /// assert_eq!(Interval::new(3, 9).hull(&Interval::new(5, 6)), Interval::new(3, 9));
    /// assert_eq!(Interval::new(1, 3).hull(&Interval::empty()), Interval::new(1, 3));
    /// assert_eq!(Interval::<usize>::empty().hull(&Interval::empty()), Interval::empty());
    /// ```
    fn hull(&self, other: &Interval<Bound>) -> Interval<Bound> {
        if self.is_empty() {
            other.clone()
        } else if other.is_empty() {
            self.clone()
        } else {
            Interval::new(min(self.low(), other.low()), max(self.up(), other.up()))
        }
    }
}

impl<Bound> Hull<Bound> for Interval<Bound>
where
    Bound: Width + Num,
{
    type Output = Interval<Bound>;

    /// Calculates the smallest interval containing an interval and a value.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(5, 8).hull(&3), Interval::new(3, 8));
    /// assert_eq!(Interval::new(1, 3).hull(&2), Interval::new(1, 3));
    /// assert_eq!(Interval::new(2, 6).hull(&9), Interval::new(2, 9));
    /// assert_eq!(Interval::singleton(4).hull(&4), Interval::singleton(4));
    /// assert_eq!(Interval::empty().hull(&5), Interval::singleton(5));
    /// ```
    fn hull(&self, other: &Bound) -> Interval<Bound> {
        self.hull(&Interval::singleton(other.clone()))
    }
}

macro_rules! primitive_interval_hull
{
  ( $( $source:ty ),* ) =>
  {$(
    impl Hull<Interval<$source>> for $source
    {
      type Output = Interval<$source>;

      #[doc = concat!(
        r#"
        Calculates the smallest interval containing an interval and a value.
        ```
        # use interval::prelude::*;
        assert_eq!((3 as "#, stringify!($source), r#").hull(&Interval::new(5, 8)), Interval::new(3, 8));
        assert_eq!((2 as "#, stringify!($source), r#").hull(&Interval::new(1, 3)), Interval::new(1, 3));
        assert_eq!((9 as "#, stringify!($source), r#").hull(&Interval::new(2, 6)), Interval::new(2, 9));
        assert_eq!((4 as "#, stringify!($source), r#").hull(&Interval::singleton(4)), Interval::singleton(4));
        assert_eq!((5 as "#, stringify!($source), r#").hull(&Interval::empty()), Interval::singleton(5));
        ```
        "#
      )]
      fn hull(&self, other: &Interval<$source>) -> Interval<$source> {
        other.hull(self)
      }
    }
  )*}
}

primitive_interval_hull!(i8, u8, i16, u16, i32, u32, i64, u64, isize, usize);

impl<Bound> Contains for Interval<Bound>
where
    Bound: Ord,
{
    /// Calculates whether an interval contains a value.
    /// ```
    /// # use interval::prelude::*;
    /// let interval = Interval::new(1, 4);
    /// assert!(interval.contains(&1));
    /// assert!(interval.contains(&2));
    /// assert!(interval.contains(&3));
    /// assert!(interval.contains(&4));
    ///
    /// assert!(!interval.contains(&0));
    /// assert!(!interval.contains(&5));
    /// ```
    /// The empty interval contains nothing.
    /// ```
    /// # use interval::prelude::*;
    /// let empty = Interval::empty();
    /// assert!(!empty.contains(&-3));
    /// assert!(!empty.contains(&5));
    /// ```
    fn contains(&self, value: &Bound) -> bool {
        value >= &self.lb && value <= &self.ub
    }
}

impl<Bound> Subset for Interval<Bound>
where
    Bound: Width + Num,
{
    /// Calculates whether one interval is contained in another.
    /// The empty interval is a subset of everything.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(1, 4).is_subset(&Interval::new(2, 6)), false);
    /// assert_eq!(Interval::new(6, 7).is_subset(&Interval::new(3, 7)), true);
    /// assert_eq!(Interval::new(8, 9).is_subset(&Interval::new(1, 2)), false);
    /// assert_eq!(Interval::new(3, 6).is_subset(&Interval::new(4, 5)), false);
    /// assert_eq!(Interval::new(5, 8).is_subset(&Interval::new(5, 8)), true);
    ///
    /// assert_eq!(Interval::empty().is_subset(&Interval::new(5, 8)), true);
    /// assert_eq!(Interval::<usize>::empty().is_subset(&Interval::empty()), true);
    /// ```
    fn is_subset(&self, other: &Interval<Bound>) -> bool {
        if self.is_empty() {
            true
        } else {
            self.lb >= other.lb && self.ub <= other.ub
        }
    }
}

impl<Bound> ProperSubset for Interval<Bound>
where
    Bound: Width + Num,
{
    /// Calculates whether one interval is contained in another,
    /// but they are not equal.
    /// The empty interval is a proper subset of everything, except itself.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(1, 4).is_proper_subset(&Interval::new(2, 6)), false);
    /// assert_eq!(Interval::new(6, 7).is_proper_subset(&Interval::new(3, 7)), true);
    /// assert_eq!(Interval::new(8, 9).is_proper_subset(&Interval::new(1, 2)), false);
    /// assert_eq!(Interval::new(3, 6).is_proper_subset(&Interval::new(4, 5)), false);
    /// assert_eq!(Interval::new(5, 8).is_proper_subset(&Interval::new(5, 8)), false);
    ///
    /// assert_eq!(Interval::empty().is_proper_subset(&Interval::new(5, 8)), true);
    /// assert_eq!(Interval::<usize>::empty().is_proper_subset(&Interval::empty()), false);
    /// ```
    fn is_proper_subset(&self, other: &Interval<Bound>) -> bool {
        self.is_subset(other) && self != other
    }
}

impl<Bound> Intersection for Interval<Bound>
where
    Bound: Width + Num,
{
    type Output = Interval<Bound>;

    /// Calculates the intersection of two intervals.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::intersection(&Interval::new(1, 4), &Interval::new(2, 6)), Interval::new(2, 4));
    /// assert_eq!(Interval::new(1, 4).intersection(&Interval::new(2, 6)), Interval::new(2, 4));
    ///
    /// assert_eq!(Interval::new(6, 7).intersection(&Interval::new(3, 9)), Interval::new(6, 7));
    /// assert_eq!(Interval::new(8, 9).intersection(&Interval::new(1, 2)), Interval::empty());
    /// assert_eq!(Interval::new(5, 8).intersection(&Interval::new(8, 10)), Interval::singleton(8));
    /// ```
    fn intersection(&self, other: &Interval<Bound>) -> Interval<Bound> {
        Interval::new(max(self.low(), other.low()), min(self.up(), other.up()))
    }
}

impl<Bound> Intersection<Bound> for Interval<Bound>
where
    Bound: Width + Num,
{
    type Output = Interval<Bound>;
    /// Calculates whether value is contained in an interval.
    /// Returns the value if it is in the interval.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(3, 8).intersection(&4), Interval::singleton(4));
    /// assert_eq!(Interval::new(7, 9).intersection(&9), Interval::singleton(9));
    /// assert_eq!(Interval::new(1, 4).intersection(&1), Interval::singleton(1));
    /// assert_eq!(Interval::empty().intersection(&9), Interval::empty());
    /// ```

    fn intersection(&self, value: &Bound) -> Interval<Bound> {
        if self.contains(value) {
            Interval::singleton(value.clone())
        } else {
            Interval::empty()
        }
    }
}

impl<Bound> Intersection<Optional<Bound>> for Interval<Bound>
where
    Bound: Width + Num,
{
    type Output = Interval<Bound>;

    /// Calculates whether an optional is contained in an interval.
    /// Returns the optional if it is in the interval.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(3, 8).intersection(&Optional::singleton(4)), Interval::singleton(4));
    /// assert_eq!(Interval::new(7, 9).intersection(&Optional::singleton(9)), Interval::singleton(9));
    /// assert_eq!(Interval::new(1, 4).intersection(&Optional::singleton(0)), Interval::empty());
    /// assert_eq!(Interval::empty().intersection(&Optional::singleton(9)), Interval::empty());
    /// assert_eq!(Interval::new(2, 6).intersection(&Optional::empty()), Interval::empty());
    /// ```
    fn intersection(&self, value: &Optional<Bound>) -> Interval<Bound> {
        value
            .as_ref()
            .map_or(Interval::empty(), |x| self.intersection(x))
    }
}

macro_rules! optional_interval_intersection
{
  ( $( $source:ty ),* ) =>
  {$(
    impl Intersection<Interval<$source>> for Optional<$source>
    {
      type Output = Optional<$source>;
      #[doc = concat!(
        r#"
        Calculates whether the optional is contained in an interval.
        ```
        # use interval::prelude::*;
        assert_eq!(Optional::<"#, stringify!($source), r#">::singleton(4).intersection(&Interval::new(3, 8)), Optional::singleton(4));
        assert_eq!(Optional::<"#, stringify!($source), r#">::singleton(9).intersection(&Interval::new(7, 9)), Optional::singleton(9));
        assert_eq!(Optional::<"#, stringify!($source), r#">::singleton(0).intersection(&Interval::new(1, 4)), Optional::empty());
        assert_eq!(Optional::<"#, stringify!($source), r#">::singleton(9).intersection(&Interval::empty()), Optional::empty());
        assert_eq!(Optional::<"#, stringify!($source), r#">::empty().intersection(&Interval::new(2, 6)), Optional::empty());
        ```
        "#
      )]
      fn intersection(&self, other: &Interval<$source>) -> Optional<$source> {
        self.as_ref().map_or(Optional::empty(), |x| other.intersection(x).into_optional())
      }
    }
  )*}
}

optional_interval_intersection!(i8, u8, i16, u16, i32, u32, i64, u64, isize, usize);

impl<Bound> Difference for Interval<Bound>
where
    Bound: Width + Num,
{
    type Output = Interval<Bound>;

    /// Calculates the interval covering values in the left interval but not the right interval.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(4, 9).difference(&Interval::new(6, 11)), Interval::new(4, 5));
    /// // The lower [1, 2] and higher [3, 10] values are included, and the smallest interval containing them is [1, 10].
    /// assert_eq!(Interval::new(1, 10).difference(&Interval::new(2, 3)), Interval::new(1, 10));
    /// // 5 is included in both intervals so the difference starts at 6.
    /// assert_eq!(Interval::new(4, 7).difference(&Interval::new(4, 5)), Interval::new(6, 7));
    /// assert_eq!(Interval::new(2, 3).difference(&Interval::new(1, 10)), Interval::empty());
    /// assert_eq!(Interval::new(5, 6).difference(&Interval::empty()), Interval::new(5, 6));
    /// assert_eq!(Interval::empty().difference(&Interval::new(2, 6)), Interval::empty());
    /// ```
    fn difference(&self, other: &Interval<Bound>) -> Interval<Bound> {
        // A - B is equivalent to A /\ ~B
        // However the complement operation doesn't make sense here
        // because it'd nearly always ends up to the whole integer interval.
        // Instead we use this equivalence:
        //   A - B is equivalent to:
        //      A /\ [inf,B.lb-1]
        //    \/
        //      A /\ [B.ub+1, inf]
        let left = self.intersection(&Interval::min_lb(other.low() - Bound::one()));
        let right = self.intersection(&Interval::max_ub(other.up() + Bound::one()));
        left.hull(&right)
    }
}

impl<Bound> Difference<Bound> for Interval<Bound>
where
    Bound: Num + Clone,
{
    type Output = Interval<Bound>;

    /// Calculates the interval covering values in the left interval, excluding `value`.
    /// ```
    /// # use interval::prelude::*;
    /// // 5 is included in the interval but the smallest interval covering the new range is [4, 9].
    /// assert_eq!(Interval::new(4, 9).difference(&5), Interval::new(4, 9));
    /// assert_eq!(Interval::new(1, 5).difference(&7), Interval::new(1, 5));
    /// assert_eq!(Interval::new(4, 7).difference(&4), Interval::new(5, 7));
    /// assert_eq!(Interval::new(2, 6).difference(&6), Interval::new(2, 5));
    /// assert_eq!(Interval::new(8, 8).difference(&8), Interval::empty());
    /// assert_eq!(Interval::empty().difference(&2), Interval::empty());
    /// ```
    fn difference(&self, value: &Bound) -> Interval<Bound> {
        let mut this = self.clone();
        if value == &this.lb {
            this.lb = this.lb + Bound::one();
        } else if value == &this.ub {
            this.ub = this.ub - Bound::one();
        }
        this
    }
}

impl<Bound> Difference<Optional<Bound>> for Interval<Bound>
where
    Bound: Ord + Num + Clone,
{
    type Output = Interval<Bound>;

    /// Calculates the interval covering values in the left interval, excluding `value`.
    /// See [`Difference<Bound>`](#method.difference-1) for details of when the `Optional` contains a value.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(4, 9).difference(&Optional::singleton(5)), Interval::new(4, 9));
    /// assert_eq!(Interval::new(3, 5).difference(&Optional::empty()), Interval::new(3, 5));
    /// assert_eq!(Interval::new(8, 8).difference(&Optional::empty()), Interval::new(8, 8));
    /// ```
    fn difference(&self, value: &Optional<Bound>) -> Interval<Bound> {
        value
            .as_ref()
            .map_or_else(|| self.clone(), |x| self.difference(x))
    }
}

macro_rules! optional_interval_difference
{
  ( $( $source:ty ),* ) =>
  {$(
    impl Difference<Interval<$source>> for Optional<$source>
    {
      type Output = Optional<$source>;
      #[doc = concat!(
        r#"
        Calculates whether an optional is outside of an interval.
        ```
        # use interval::prelude::*;
        assert_eq!(Optional::<"#, stringify!($source), r#">::singleton(4).difference(&Interval::new(3, 8)), Optional::empty());
        assert_eq!(Optional::<"#, stringify!($source), r#">::singleton(8).difference(&Interval::new(7, 9)), Optional::empty());
        assert_eq!(Optional::<"#, stringify!($source), r#">::singleton(3).difference(&Interval::new(1, 4)), Optional::empty());
        assert_eq!(Optional::<"#, stringify!($source), r#">::singleton(9).difference(&Interval::empty()), Optional::singleton(9));
        assert_eq!(Optional::<"#, stringify!($source), r#">::empty().difference(&Interval::new(2, 6)), Optional::empty());
        ```
      "#)]
      fn difference(&self, other: &Interval<$source>) -> Optional<$source> {
        self.as_ref().map_or(Optional::empty(), |x|
          if other.contains(x) { Optional::empty() }
          else { Optional::singleton(x.clone()) }
        )
      }
    }
  )*}
}

optional_interval_difference!(i8, u8, i16, u16, i32, u32, i64, u64, isize, usize);

impl<Bound> ShrinkLeft for Interval<Bound>
where
    Bound: Num + Width,
{
    /// Updates the lower bound to be greater than or equal to a value.
    /// ```
    /// use interval::prelude::*;
    /// let a = Interval::new(5, 9);
    /// // Increase the lower bound.
    /// let b = a.shrink_left(7);
    /// assert_eq!(b, Interval::new(7, 9));
    /// // No effect on the lower bound.
    /// let c = a.shrink_left(4);
    /// assert_eq!(c, a);
    /// // Empty interval.
    /// let d = a.shrink_left(10);
    /// assert!(d.is_empty());
    /// ```
    fn shrink_left(&self, lb: Bound) -> Interval<Bound> {
        let mut this = self.clone();
        if lb > this.lb {
            this.lb = lb;
        }
        this
    }
}

impl<Bound> ShrinkRight for Interval<Bound>
where
    Bound: Num + Width,
{
    /// Updates the upper bound to be less than or equal to a value.
    /// ```
    /// use interval::prelude::*;
    /// let a = Interval::new(5, 9);
    /// // Decrease the upper bound.
    /// let b = a.shrink_right(8);
    /// assert_eq!(b, Interval::new(5, 8));
    /// // No effect on the upper bound.
    /// let c = a.shrink_right(12);
    /// assert_eq!(c, a);
    /// // Empty interval.
    /// let d = a.shrink_right(3);
    /// assert!(d.is_empty());
    /// ```
    fn shrink_right(&self, ub: Bound) -> Interval<Bound> {
        let mut this = self.clone();
        if ub < this.ub {
            this.ub = ub;
        }
        this
    }
}

forward_all_binop!(impl<Bound: +Num+Width> Add for Interval<Bound>, add);

impl<'a, 'b, Bound> Add<&'b Interval<Bound>> for &'a Interval<Bound>
where
    Bound: Num + Width,
{
    type Output = Interval<Bound>;

    /// Adds two intervals, by adding the lower and upper bounds to calculate a new interval.
    /// ```
    /// # use interval::prelude::*;
    /// let a = Interval::new(5, 9);
    /// let b = Interval::new(-2, 4);
    /// assert_eq!(a + b, Interval::new(3, 13));
    /// ```
    /// This method preserves empty intervals.
    /// ```
    /// # use interval::prelude::*;
    /// let a = Interval::new(5, 9);
    /// let b = Interval::empty();
    /// assert!((a + b).is_empty());
    /// ```
    fn add(self, other: &Interval<Bound>) -> Interval<Bound> {
        if self.is_empty() || other.is_empty() {
            Interval::empty()
        } else {
            Interval::new(self.lower() + other.lower(), self.upper() + other.upper())
        }
    }
}

forward_all_binop!(impl<Bound: +Num+Width+Clone> Add for Interval<Bound>, add, Bound);

impl<'a, 'b, Bound> Add<&'b Bound> for &'a Interval<Bound>
where
    Bound: Num + Width + Clone,
{
    type Output = Interval<Bound>;

    /// Adds a constant to an interval.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(5, 9) + 4, Interval::new(9, 13));
    /// ```
    /// This method preserves empty intervals.
    /// ```
    /// # use interval::prelude::*;
    /// assert!((Interval::empty() + 4).is_empty());
    /// ```
    /// It is not possible to add an interval to a constant.
    /// ```compile_fail
    /// # use interval::prelude::*;
    /// let _ = 4 + Interval::new(5, 9); // doesn't compile
    /// ```
    fn add(self, other: &Bound) -> Interval<Bound> {
        if self.is_empty() {
            Interval::empty()
        } else {
            Interval::new(self.lower() + other.clone(), self.upper() + other.clone())
        }
    }
}

forward_all_binop!(impl<Bound: +Num+Width> Sub for Interval<Bound>, sub);

impl<'a, 'b, Bound> Sub<&'b Interval<Bound>> for &'a Interval<Bound>
where
    Bound: Num + Width,
{
    type Output = Interval<Bound>;

    /// Subtracts two intervals to calculate the interval of the result.
    /// The upper bound of `a - b` is `a.upper() - b.lower()` and
    /// the lower bound is `a.lower() - b.upper()`.
    /// ```
    /// # use interval::prelude::*;
    /// let a = Interval::new(5, 9);
    /// let b = Interval::new(-2, 4);
    /// assert_eq!(a - b, Interval::new(1, 11));
    /// ```
    /// This method preserves empty intervals.
    /// ```
    /// # use interval::prelude::*;
    /// let a = Interval::new(5, 9);
    /// let b = Interval::empty();
    /// assert!((a - b).is_empty());
    /// ```
    fn sub(self, other: &Interval<Bound>) -> Interval<Bound> {
        if self.is_empty() || other.is_empty() {
            Interval::empty()
        } else {
            Interval::new(self.lower() - other.upper(), self.upper() - other.lower())
        }
    }
}

forward_all_binop!(impl<Bound: +Num+Width+Clone> Sub for Interval<Bound>, sub, Bound);

impl<'a, 'b, Bound> Sub<&'b Bound> for &'a Interval<Bound>
where
    Bound: Num + Width + Clone,
{
    type Output = Interval<Bound>;

    /// Subtracts a constant from an interval.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(5, 9) - 4, Interval::new(1, 5));
    /// ```
    /// This method preserves empty intervals.
    /// ```
    /// # use interval::prelude::*;
    /// assert!((Interval::empty() - 4).is_empty());
    /// ```
    /// It is not possible to subtract an interval from a constant.
    /// ```compile_fail
    /// # use interval::prelude::*;
    /// let _ = 4 - Interval::new(5, 9); // doesn't compile
    /// ```
    fn sub(self, other: &Bound) -> Interval<Bound> {
        if self.is_empty() {
            Interval::empty()
        } else {
            Interval::new(self.lower() - other.clone(), self.upper() - other.clone())
        }
    }
}

forward_all_binop!(impl<Bound: +Num+Width> Mul for Interval<Bound>, mul);

// Adapted from the code found in the Rust compiler sources.
// Rational: min_max was removed.
fn min_max<Iter, Item>(mut iter: Iter) -> (Item, Item)
where
    Iter: Iterator<Item = Item>,
    Item: Ord,
{
    debug_assert!(
        iter.size_hint().0 > 2,
        "`min_max` expects an iterator (`iter`) yielding at least two elements."
    );
    let (mut min, mut max) = {
        let x = iter.next().unwrap();
        let y = iter.next().unwrap();
        if x <= y {
            (x, y)
        } else {
            (y, x)
        }
    };

    loop {
        // `first` and `second` are the two next elements we want to look
        // at.  We first compare `first` and `second` (#1). The smaller one
        // is then compared to current minimum (#2). The larger one is
        // compared to current maximum (#3). This way we do 3 comparisons
        // for 2 elements.
        let first = match iter.next() {
            None => break,
            Some(x) => x,
        };
        let second = match iter.next() {
            None => {
                if first < min {
                    min = first;
                } else if first >= max {
                    max = first;
                }
                break;
            }
            Some(x) => x,
        };
        if first <= second {
            if first < min {
                min = first
            }
            if second >= max {
                max = second
            }
        } else {
            if second < min {
                min = second
            }
            if first >= max {
                max = first
            }
        }
    }
    (min, max)
}

impl<'a, 'b, Bound> Mul<&'b Interval<Bound>> for &'a Interval<Bound>
where
    Bound: Num + Width,
{
    type Output = Interval<Bound>;

    /// Multiplies two intervals by multiplying the lower and upper bounds.
    /// Caution: the resulting interval is often an over-approximation.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(0, 1) * Interval::new(3, 5), Interval::new(0, 5));
    /// ```
    /// The interval produced is the smallest possible interval,
    /// however, only the values 0, 3, 4 and 5 are possible results of this multiplication.
    ///
    /// This method preserves empty intervals.
    /// ```
    /// # use interval::prelude::*;
    /// assert!((Interval::empty() * Interval::new(2, 4)).is_empty());
    /// ```
    fn mul(self, other: &Interval<Bound>) -> Interval<Bound> {
        if self.is_empty() || other.is_empty() {
            Interval::empty()
        } else {
            let (min, max) = min_max(
                vec![
                    self.lower() * other.lower(),
                    self.lower() * other.upper(),
                    self.upper() * other.lower(),
                    self.upper() * other.upper(),
                ]
                .into_iter(),
            );
            Interval::new(min, max)
        }
    }
}

forward_all_binop!(impl<Bound: +Num+Width+Clone> Mul for Interval<Bound>, mul, Bound);

impl<'a, 'b, Bound> Mul<&'b Bound> for &'a Interval<Bound>
where
    Bound: Num + Width + Clone,
{
    type Output = Interval<Bound>;

    /// Multiplies an interval by a constant.
    /// Caution: the resulting interval is often an over-approximation.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(Interval::new(0, 1) * 3, Interval::new(0, 3));
    /// ```
    /// The interval produced is the smallest possible interval,
    /// however, only the values 0 and 3 are possible results of this multiplication.
    ///
    /// This method preserves empty intervals.
    /// ```
    /// # use interval::prelude::*;
    /// assert!((Interval::empty() * 4).is_empty());
    /// ```
    /// It is not possible to multiply a constant by an interval.
    /// ```compile_fail
    /// # use interval::prelude::*;
    /// let _ = 4 * Interval::new(5, 9); // doesn't compile
    /// ```
    fn mul(self, other: &Bound) -> Interval<Bound> {
        if self.is_empty() {
            Interval::empty()
        } else {
            Interval::new(self.lower() * other.clone(), self.upper() * other.clone())
        }
    }
}

impl<Bound> Display for Interval<Bound>
where
    Bound: Display + Width + Num,
{
    /// Formats an interval.
    /// Empty intervals are displayed as the empty set "{}".
    /// Non empty intervals are displayed as [lower..upper].
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(format!("{}", Interval::new(3, 5)), "[3..5]");
    /// assert_eq!(format!("{}", Interval::singleton(4)), "[4..4]");
    /// assert_eq!(format!("{}", Interval::<usize>::empty()), "{}");
    /// ```
    fn fmt(&self, formatter: &mut Formatter) -> Result<(), Error> {
        if self.is_empty() {
            formatter.write_str("{}")
        } else {
            formatter.write_fmt(format_args!("[{}..{}]", self.lb, self.ub))
        }
    }
}

pub trait ToInterval<Bound> {
    /// Converts a value to an interval.
    /// For example,
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(8.to_interval(), Interval::singleton(8));
    /// assert_eq!((3, 4).to_interval(), Interval::new(3, 4));
    /// assert_eq!(().to_interval(), Interval::<usize>::empty());
    /// ```
    fn to_interval(self) -> Interval<Bound>;
}

impl<Bound> ToInterval<Bound> for Interval<Bound> {
    /// Converts an interval to an interval with no action.
    /// ```
    /// # use interval::prelude::*;
    /// let interval = Interval::new(2, 6);
    /// assert_eq!(interval.to_interval(), interval);
    ///
    /// let empty = Interval::<i16>::empty();
    /// assert_eq!(empty.to_interval(), empty);
    /// ```
    fn to_interval(self) -> Interval<Bound> {
        self
    }
}

impl<Bound: Width + Num> ToInterval<Bound> for (Bound, Bound) {
    /// Converts a tuple to an interval using the first element as the lower bound
    /// and second element as the upper bound.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!((2, 6).to_interval(), Interval::new(2, 6));
    /// ```
    /// The first and second elements need the same type.
    /// ```compile_fail
    /// # use interval::prelude::*;
    /// let _ = (8 as u8, 9 as i8).to_interval(); // doesn't compile
    /// ```
    fn to_interval(self) -> Interval<Bound> {
        let (a, b) = self;
        Interval::new(a, b)
    }
}

impl<Bound: Width + Num> ToInterval<Bound> for () {
    /// Converts the empty tuple to an empty interval.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(().to_interval(), Interval::<usize>::empty());
    /// ```
    /// The type can be specified via the full trait or annotations.
    /// ```
    /// # use interval::prelude::*;
    /// let empty_full_trait = ToInterval::<i32>::to_interval(());
    /// let empty_annotated: Interval<i32> = ().to_interval();
    /// assert_eq!(empty_full_trait, Interval::empty());
    /// assert_eq!(empty_annotated, Interval::empty());
    /// ```
    fn to_interval(self) -> Interval<Bound> {
        Interval::empty()
    }
}

impl<Bound: Width + Num> ToInterval<Bound> for Bound {
    /// Converts a value to a singleton interval.
    /// ```
    /// # use interval::prelude::*;
    /// assert_eq!(9.to_interval(), Interval::singleton(9));
    /// ```
    fn to_interval(self) -> Interval<Bound> {
        Interval::singleton(self)
    }
}

impl<Bound: Width + Num> ToInterval<Bound> for RangeInclusive<Bound> {
    /// Converts an inclusive range to an interval.
    /// ```
    /// # use interval::prelude::*;
    /// let range = 2..=6; // out of bounds for Width trait
    /// assert_eq!(range.to_interval(), Interval::new(2, 6));
    /// ```
    /// The inclusive range is required because the endpoints are included in the interval.
    /// Therefore, the semi-exclusive range fails to compile.
    /// ```compile_fail
    /// # use interval::prelude::*;
    /// let range = 2..6; // semi-exclusive range
    /// let _ = range.to_interval(); // fail
    /// ```
    fn to_interval(self) -> Interval<Bound> {
        Interval::new(self.start().clone(), self.end().clone())
    }
}

impl<Bound: Width + Num> ToInterval<Bound> for RangeFrom<Bound> {
    /// Converts a range with a lower bound to an interval.
    /// ```
    /// # use interval::prelude::*;
    /// let range = 2..;
    /// assert_eq!(range.to_interval(), Interval::new(2, <i32 as Width>::max_value()));
    /// ```
    /// See [`Interval::whole`] for caveats on the lower bound,
    /// which means the following example fails to compile:
    /// ```should_panic
    /// # use interval::prelude::*;
    /// let range = 255u8..; // out of bounds for Width trait
    /// let _ = range.to_interval(); // fail
    /// ```
    fn to_interval(self) -> Interval<Bound> {
        Interval::new(
            self.start.clone(),
            max(<Bound as Width>::max_value(), self.start.clone()),
        )
    }
}

impl<Bound: Width + Num> ToInterval<Bound> for RangeToInclusive<Bound> {
    /// Converts a range with an upper bound to an interval.
    /// ```
    /// # use interval::prelude::*;
    /// let range = 0..=100u32;
    /// assert_eq!(range.to_interval(), Interval::new(0, 100));
    /// ```
    /// As with [`RangeInclusive`](#impl-ToInterval<Bound>-for-RangeInclusive<Bound>), the endpoint must be included:
    /// ```compile_fail
    /// # use interval::prelude::*;
    /// let range = ..100; // exclusive range
    /// let _ = range.to_interval(); // fail
    /// ```
    /// See [`Interval::whole`] for caveats on the upper bound,
    /// which means the following example fails to compile:
    /// ```should_panic
    /// # use interval::prelude::*;
    /// let range =..=255u8;
    /// let _ = range.to_interval(); // fail
    /// ```
    fn to_interval(self) -> Interval<Bound> {
        Interval::new(
            min(<Bound as Width>::min_value(), self.end.clone()),
            self.end.clone(),
        )
    }
}

impl<Bound> Join for Interval<Bound>
where
    Bound: Width + Num,
{
    fn join(self, other: Interval<Bound>) -> Interval<Bound> {
        self.intersection(&other)
    }
}

impl<Bound> Meet for Interval<Bound>
where
    Bound: Width + Num,
{
    fn meet(self, other: Interval<Bound>) -> Interval<Bound> {
        self.hull(&other)
    }
}

impl<Bound> Entailment for Interval<Bound>
where
    Bound: Width + Num,
{
    fn entail(&self, other: &Interval<Bound>) -> SKleene {
        if self.is_subset(other) {
            SKleene::True
        } else if other.is_subset(self) {
            SKleene::False
        } else {
            SKleene::Unknown
        }
    }
}

impl<Bound> Top for Interval<Bound>
where
    Bound: Width + Num,
{
    fn top() -> Interval<Bound> {
        Interval::empty()
    }
}

impl<Bound> Bot for Interval<Bound>
where
    Bound: Width + Num,
{
    fn bot() -> Interval<Bound> {
        Interval::whole()
    }
}

#[allow(non_upper_case_globals)]
#[cfg(test)]
mod tests {
    use serde_test::{assert_de_tokens, assert_de_tokens_error, assert_tokens, Token};

    use super::*;

    const empty: Interval<i32> = Interval { lb: 1, ub: 0 };
    const invalid: Interval<i32> = Interval { lb: 10, ub: -10 };
    const zero: Interval<i32> = Interval { lb: 0, ub: 0 };
    const one: Interval<i32> = Interval { lb: 1, ub: 1 };
    const ten: Interval<i32> = Interval { lb: 10, ub: 10 };

    const i0_1: Interval<i32> = Interval { lb: 0, ub: 1 };
    const i0_2: Interval<i32> = Interval { lb: 0, ub: 2 };
    const i1_2: Interval<i32> = Interval { lb: 1, ub: 2 };
    const i0_10: Interval<i32> = Interval { lb: 0, ub: 10 };
    const i1_10: Interval<i32> = Interval { lb: 1, ub: 10 };
    const i0_9: Interval<i32> = Interval { lb: 0, ub: 9 };
    const i0_15: Interval<i32> = Interval { lb: 0, ub: 15 };
    const im5_10: Interval<i32> = Interval { lb: -5, ub: 10 };
    const im5_m1: Interval<i32> = Interval { lb: -5, ub: -1 };
    const i5_10: Interval<i32> = Interval { lb: 5, ub: 10 };
    const i6_10: Interval<i32> = Interval { lb: 6, ub: 10 };
    const i0_5: Interval<i32> = Interval { lb: 0, ub: 5 };
    const i0_4: Interval<i32> = Interval { lb: 0, ub: 4 };
    const im5_5: Interval<i32> = Interval { lb: -5, ub: 5 };
    const i20_30: Interval<i32> = Interval { lb: 20, ub: 30 };
    const im30_m20: Interval<i32> = Interval { lb: -30, ub: -20 };

    #[test]
    fn to_interval_id_test() {
        let id = i1_2.clone().to_interval();
        assert_eq!(i1_2, id);
        assert_eq!(i1_2, Interval::new(1, 2));
    }

    #[test]
    fn equality_test() {
        assert_eq!(empty, empty);
        assert_eq!(empty, invalid);
        assert_eq!(invalid, empty);
        assert_eq!(i1_2, i1_2);
    }

    #[test]
    fn size_test() {
        let whole_i32: Interval<i32> = Interval::<i32>::whole();
        let whole_u32: Interval<u32> = Interval::<u32>::whole();

        assert_eq!(zero.size(), 1);
        assert_eq!(one.size(), 1);
        assert_eq!(empty.size(), 0);
        assert_eq!(invalid.size(), 0);

        assert_eq!(i1_2.size(), 2);
        assert_eq!(i0_10.size(), 11);
        assert_eq!(im30_m20.size(), 11);

        assert_eq!(whole_i32.size(), u32::max_value());
        assert_eq!(whole_u32.size(), u32::max_value());
    }

    #[test]
    fn contains_test() {
        assert!(i1_2.contains(&1));
        assert!(i1_2.contains(&2));
        assert!(!i1_2.contains(&0));
        assert!(!i1_2.contains(&3));

        assert!(zero.contains(&0));
        assert!(!zero.contains(&1));

        assert!(!empty.contains(&0));
        assert!(!empty.contains(&1));
        assert!(!empty.contains(&5));
        assert!(!empty.contains(&-5));

        assert!(!invalid.contains(&0));
        assert!(!invalid.contains(&-11));
        assert!(!invalid.contains(&11));
    }

    #[test]
    fn is_subset_test() {
        let cases = vec![
            (zero, zero, true),
            (i1_2, i1_2, true),
            (empty, empty, true),
            (invalid, invalid, true),
        ];

        // For each cases (x, y, res)
        // * x and y are the values
        // * res is a tuple (r, sym) where
        //    * r is true if x is a subset of y
        //    * sym is true if y is a subset of x
        let sym_cases = vec![
            // ||
            // |-|
            (empty, zero, (true, false)),
            (invalid, zero, (true, false)),
            (empty, invalid, (true, true)),
            // ||
            //|--|
            (empty, i1_2, (true, false)),
            (empty, i0_10, (true, false)),
            (invalid, i1_2, (true, false)),
            //  |--|
            // |----|
            (i1_2, i0_10, (true, false)),
            // |--|
            //     |--|
            (i0_4, i5_10, (false, false)),
            // |--|
            //    |--|
            (i0_5, i5_10, (false, false)),
            // |---|
            //   |---|
            (im5_5, i0_10, (false, false)),
            // |--|
            //         |--|
            (i0_10, i20_30, (false, false)),
            // |--|
            // |---|
            (i0_10, i0_15, (true, false)),
            // |---|
            //  |--|
            (im5_10, i0_10, (false, true)),
        ];

        for (x, y, r) in cases.into_iter() {
            assert!(
                x.is_subset(&y) == r,
                "{:?} is subset of {:?} is not equal to {:?}",
                x,
                y,
                r
            );
        }

        for (x, y, (r1, r2)) in sym_cases.into_iter() {
            assert!(
                x.is_subset(&y) == r1,
                "{:?} is subset of {:?} is not equal to {:?}",
                x,
                y,
                r1
            );
            assert!(
                y.is_subset(&x) == r2,
                "{:?} is subset of {:?} is not equal to {:?}",
                y,
                x,
                r2
            );
        }
    }

    #[test]
    fn is_proper_subset_test() {
        let cases = vec![
            (zero, zero, false),
            (i1_2, i1_2, false),
            (empty, empty, false),
            (invalid, invalid, false),
        ];

        // For each cases (x, y, res)
        // * x and y are the values
        // * res is a tuple (r, sym) where
        //    * r is true if x is a proper subset of y
        //    * sym is true if y is a proper subset of x
        let sym_cases = vec![
            // ||
            // |-|
            (empty, zero, (true, false)),
            (invalid, zero, (true, false)),
            (empty, invalid, (false, false)),
            // ||
            //|--|
            (empty, i1_2, (true, false)),
            (empty, i0_10, (true, false)),
            (invalid, i1_2, (true, false)),
            //  |--|
            // |----|
            (i1_2, i0_10, (true, false)),
            // |--|
            //     |--|
            (i0_4, i5_10, (false, false)),
            // |--|
            //    |--|
            (i0_5, i5_10, (false, false)),
            // |---|
            //   |---|
            (im5_5, i0_10, (false, false)),
            // |--|
            //         |--|
            (i0_10, i20_30, (false, false)),
            // |--|
            // |---|
            (i0_10, i0_15, (true, false)),
            // |---|
            //  |--|
            (im5_10, i0_10, (false, true)),
        ];

        for (x, y, r) in cases.into_iter() {
            assert!(
                x.is_proper_subset(&y) == r,
                "{:?} is proper subset of {:?} is not equal to {:?}",
                x,
                y,
                r
            );
        }

        for (x, y, (r1, r2)) in sym_cases.into_iter() {
            assert!(
                x.is_proper_subset(&y) == r1,
                "{:?} is proper subset of {:?} is not equal to {:?}",
                x,
                y,
                r1
            );
            assert!(
                y.is_proper_subset(&x) == r2,
                "{:?} is proper subset of {:?} is not equal to {:?}",
                y,
                x,
                r2
            );
        }
    }

    #[test]
    fn intersection_test() {
        let cases = vec![
            (zero, zero, zero),
            (i1_2, i1_2, i1_2),
            (empty, empty, empty),
            (invalid, invalid, invalid),
        ];

        // For each cases (x, y, res)
        // * x and y are the values
        // * res is the expected result, which should be the same
        // for x intersect y and y intersect x since the intersection
        // is commutative.
        let sym_cases = vec![
            // ||
            // |-|
            (empty, zero, empty),
            (invalid, zero, empty),
            (empty, invalid, empty),
            // ||
            //|--|
            (empty, i1_2, empty),
            (empty, i0_10, empty),
            (invalid, i1_2, empty),
            //  |--|
            // |----|
            (i1_2, i0_10, i1_2),
            // |--|
            //     |--|
            (i0_4, i5_10, empty),
            // |--|
            //    |--|
            (i0_5, i5_10, 5.to_interval()),
            // |---|
            //   |---|
            (im5_5, i0_10, (0, 5).to_interval()),
            // |--|
            //         |--|
            (i0_10, i20_30, empty),
            // |--|
            // |---|
            (i0_10, i0_15, i0_10),
            // |---|
            //  |--|
            (im5_10, i0_10, i0_10),
        ];

        for (x, y, r) in cases.into_iter() {
            assert!(
                x.intersection(&y) == r,
                "{:?} intersection {:?} is not equal to {:?}",
                x,
                y,
                r
            );
        }

        for (x, y, r) in sym_cases.into_iter() {
            assert!(
                x.intersection(&y) == r,
                "{:?} intersection {:?} is not equal to {:?}",
                x,
                y,
                r
            );
            assert!(
                y.intersection(&x) == r,
                "{:?} intersection {:?} is not equal to {:?}",
                y,
                x,
                r
            );
        }
    }

    #[test]
    fn intersection_value_optional_test() {
        let cases = vec![
            (1, empty, None, empty, None),
            (2, invalid, None, empty, None),
            (3, empty, Some(1), empty, None),
            (4, i0_10, None, empty, None),
            (5, i0_10, Some(0), zero, Some(0)),
            (6, i0_10, Some(10), ten, Some(10)),
            (7, i0_10, Some(1), one, Some(1)),
            (8, i0_10, Some(-1), empty, None),
            (9, i0_10, Some(11), empty, None),
            (10, one, Some(0), empty, None),
            (11, one, Some(1), one, Some(1)),
        ];
        for (id, x, y, r1, r2) in cases.into_iter() {
            let y = y.map_or(Optional::empty(), |y| Optional::singleton(y));
            let r2 = r2.map_or(Optional::empty(), |r2| Optional::singleton(r2));
            // Interval /\ Value.
            if !y.is_empty() {
                assert!(
                    x.intersection(y.as_ref().unwrap()) == r1,
                    "Test#{}: {:?} intersection {:?} is not equal to {:?}",
                    id,
                    x,
                    y.as_ref().unwrap(),
                    r1
                );
            }
            // Interval /\ Option<T>
            assert!(
                x.intersection(&y) == r1,
                "Test#{}: {:?} intersection {:?} is not equal to {:?}",
                id,
                x,
                y,
                r1
            );
            // Option<T> /\ Interval
            assert!(
                y.intersection(&x) == r2,
                "Test#{}: {:?} intersection {:?} is not equal to {:?}",
                id,
                y,
                x,
                r2
            );
        }
    }

    #[test]
    fn hull_test() {
        let cases = vec![
            (zero, zero, zero),
            (i1_2, i1_2, i1_2),
            (empty, empty, empty),
            (invalid, invalid, invalid),
        ];

        // For each cases (x, y, res)
        // * x and y are the values
        // * res is the expected result, which should be the same
        // for the union hull of (x,y) or (y,x) since the union hull
        // is commutative.
        let sym_cases = vec![
            // ||
            // |-|
            (empty, zero, zero),
            (invalid, zero, zero),
            (empty, invalid, empty),
            // ||
            //|--|
            (empty, i1_2, i1_2),
            (empty, i0_10, i0_10),
            (invalid, i1_2, i1_2),
            //  |--|
            // |----|
            (i1_2, i0_10, i0_10),
            // |--|
            //     |--|
            (i0_4, i5_10, i0_10),
            // |--|
            //    |--|
            (i0_5, i5_10, i0_10),
            // |---|
            //   |---|
            (im5_5, i0_10, (-5, 10).to_interval()),
            // |--|
            //         |--|
            (i0_10, i20_30, (0, 30).to_interval()),
            // |--|
            // |---|
            (i0_10, i0_15, i0_15),
            // |---|
            //  |--|
            (im5_10, i0_10, im5_10),
        ];

        for (x, y, r) in cases.into_iter() {
            assert!(
                x.hull(&y) == r,
                "{:?} hull {:?} is not equal to {:?}",
                x,
                y,
                r
            );
        }

        for (x, y, r) in sym_cases.into_iter() {
            assert!(
                x.hull(&y) == r,
                "{:?} hull {:?} is not equal to {:?}",
                x,
                y,
                r
            );
            assert!(
                y.hull(&x) == r,
                "{:?} hull {:?} is not equal to {:?}",
                y,
                x,
                r
            );
        }
    }

    #[test]
    fn is_disjoint_test() {
        let cases = vec![
            (zero, zero, false),
            (i1_2, i1_2, false),
            (empty, empty, true),
            (invalid, invalid, true),
        ];

        // For each cases (x, y, res)
        // * x and y are the values
        // * res is the expected result, which should be the same
        // for x is disjoint of y and y is disjoint of x since the
        // disjoint operation is commutative.
        let sym_cases = vec![
            // ||
            // |-|
            (empty, zero, true),
            (invalid, zero, true),
            (empty, invalid, true),
            // ||
            //|--|
            (empty, i1_2, true),
            (empty, i0_10, true),
            (invalid, i1_2, true),
            //  |--|
            // |----|
            (i1_2, i0_10, false),
            // |--|
            //     |--|
            (i0_4, i5_10, true),
            // |--|
            //    |--|
            (i0_5, i5_10, false),
            // |---|
            //   |---|
            (im5_5, i0_10, false),
            // |--|
            //         |--|
            (i0_10, i20_30, true),
            // |--|
            // |---|
            (i0_10, i0_15, false),
            // |---|
            //  |--|
            (im5_10, i0_10, false),
        ];

        for (x, y, r) in cases.into_iter() {
            assert!(
                x.is_disjoint(&y) == r,
                "{:?} is disjoint of {:?} is not equal to {:?}",
                x,
                y,
                r
            );
            assert!(
                x.overlap(&y) == !r,
                "{:?} overlap {:?} is not equal to {:?}",
                x,
                y,
                r
            );
        }

        for (x, y, r) in sym_cases.into_iter() {
            assert!(
                x.is_disjoint(&y) == r,
                "{:?} is disjoint of {:?} is not equal to {:?}",
                x,
                y,
                r
            );
            assert!(
                y.is_disjoint(&x) == r,
                "{:?} is disjoint of {:?} is not equal to {:?}",
                y,
                x,
                r
            );
            assert!(
                x.overlap(&y) == !r,
                "{:?} overlap {:?} is not equal to {:?}",
                x,
                y,
                r
            );
            assert!(
                y.overlap(&x) == !r,
                "{:?} overlap {:?} is not equal to {:?}",
                y,
                x,
                r
            );
        }
    }

    fn is_disjoint_cases() -> Vec<(u32, Interval<i32>, i32, bool)> {
        vec![
            (1, empty, 0, true),
            (2, invalid, 0, true),
            (3, i0_4, -1, true),
            (4, i0_4, 0, false),
            (5, i0_4, 2, false),
            (6, i0_4, 3, false),
            (7, i0_4, 5, true),
        ]
    }

    #[test]
    fn is_disjoint_bound_test() {
        let cases = is_disjoint_cases();
        for (id, x, y, r) in cases.into_iter() {
            assert!(
                x.is_disjoint(&y) == r,
                "Test#{}: {:?} is disjoint of {:?} is not equal to {:?}",
                id,
                x,
                y,
                r
            );
            assert!(
                y.is_disjoint(&x) == r,
                "Test#{}: {:?} is disjoint of {:?} is not equal to {:?}",
                id,
                y,
                x,
                r
            );
            assert!(
                x.overlap(&y) == !r,
                "Test#{}: {:?} overlap {:?} is not equal to {:?}",
                id,
                x,
                y,
                !r
            );
            assert!(
                y.overlap(&x) == !r,
                "Test#{}: {:?} overlap {:?} is not equal to {:?}",
                id,
                y,
                x,
                !r
            );
        }
    }

    #[test]
    fn is_disjoint_option_test() {
        let mut cases: Vec<(u32, Interval<i32>, Optional<i32>, bool)> = is_disjoint_cases()
            .into_iter()
            .map(|(id, a, b, e)| (id, a, Optional::singleton(b), e))
            .collect();
        cases.extend(vec![
            (8, empty, Optional::empty(), true),
            (9, invalid, Optional::empty(), true),
            (10, i0_4, Optional::empty(), true),
        ]);
        for (id, x, y, r) in cases.into_iter() {
            assert!(
                x.is_disjoint(&y) == r,
                "Test#{}: {:?} is disjoint of {:?} is not equal to {:?}",
                id,
                x,
                y,
                r
            );
            assert!(
                y.is_disjoint(&x) == r,
                "Test#{}: {:?} is disjoint of {:?} is not equal to {:?}",
                id,
                y,
                x,
                r
            );
            assert!(
                x.overlap(&y) == !r,
                "Test#{}: {:?} overlap {:?} is not equal to {:?}",
                id,
                x,
                y,
                !r
            );
            assert!(
                y.overlap(&x) == !r,
                "Test#{}: {:?} overlap {:?} is not equal to {:?}",
                id,
                y,
                x,
                !r
            );
        }
    }

    #[test]
    fn difference_test() {
        let cases = vec![
            (1, zero, zero, empty),
            (2, i1_2, i1_2, empty),
            (3, empty, empty, empty),
            (4, invalid, invalid, empty),
        ];

        // For each cases (x, y, res)
        // * x and y are the values
        // * res is a tuple (r, sym) where
        //    * x diff y == r
        //    * y diff x == sym
        let sym_cases = vec![
            // ||
            // |-|
            (5, empty, zero, (empty, zero)),
            (6, invalid, zero, (empty, zero)),
            (7, empty, invalid, (empty, empty)),
            // ||
            //|--|
            (8, empty, i1_2, (empty, i1_2)),
            (9, empty, i0_10, (empty, i0_10)),
            (10, invalid, i1_2, (empty, i1_2)),
            //  |--|
            // |----|
            (11, i1_2, i0_10, (empty, i0_10)),
            // |--|
            //     |--|
            (12, i0_4, i5_10, (i0_4, i5_10)),
            // |--|
            //    |--|
            (13, i0_5, i5_10, ((0, 4).to_interval(), i6_10)),
            // |---|
            //   |---|
            (14, im5_5, i0_10, (im5_m1, i6_10)),
            // |--|
            //         |--|
            (15, i0_10, i20_30, (i0_10, i20_30)),
            // |--|
            // |---|
            (16, i0_10, i0_15, (empty, (11, 15).to_interval())),
            // |---|
            //  |--|
            (17, im5_10, i0_10, (im5_m1, empty)),
        ];

        for (id, x, y, r) in cases.into_iter() {
            println!("Test #{}", id);
            assert!(
                x.difference(&y) == r,
                "{:?} difference {:?} is not equal to {:?}",
                x,
                y,
                r
            );
        }

        for (id, x, y, (r1, r2)) in sym_cases.into_iter() {
            println!("Test #{}", id);
            assert!(
                x.difference(&y) == r1,
                "{:?} difference {:?} is not equal to {:?}",
                x,
                y,
                r1
            );
            assert!(
                y.difference(&x) == r2,
                "{:?} difference {:?} is not equal to {:?}",
                y,
                x,
                r2
            );
        }
    }

    #[test]
    fn difference_value_option_test() {
        let cases = vec![
            (1, empty, None, empty, None),
            (2, invalid, None, empty, None),
            (3, empty, Some(1), empty, Some(1)),
            (4, i0_10, None, i0_10, None),
            (5, i0_10, Some(0), i1_10, None),
            (6, i0_10, Some(10), i0_9, None),
            (7, i0_10, Some(1), i0_10, None),
            (8, i0_10, Some(9), i0_10, None),
            (9, i0_10, Some(-1), i0_10, Some(-1)),
            (10, i0_10, Some(11), i0_10, Some(11)),
            (11, i0_10, Some(100), i0_10, Some(100)),
            (12, one, Some(1), empty, None),
        ];
        for (id, x, y, r1, r2) in cases.into_iter() {
            let y = y.map_or(Optional::empty(), |y| Optional::singleton(y));
            let r2 = r2.map_or(Optional::empty(), |r2| Optional::singleton(r2));
            // Interval - Value.
            if y.is_some() {
                assert!(
                    x.difference(y.as_ref().unwrap()) == r1,
                    "Test#{}: {:?} difference {:?} is not equal to {:?}",
                    id,
                    x,
                    y.as_ref().unwrap(),
                    r1
                );
            }
            // Interval - Option<T>
            assert!(
                x.difference(&y) == r1,
                "Test#{}: {:?} difference {:?} is not equal to {:?}",
                id,
                x,
                y,
                r1
            );
            // Option<T> - Interval
            assert!(
                y.difference(&x) == r2,
                "Test#{}: {:?} difference {:?} is not equal to {:?}",
                id,
                y,
                x,
                r2
            );
        }
    }

    #[test]
    fn shrink_left_test() {
        let cases = vec![
            (i0_10, -5, i0_10),
            (i0_10, 0, i0_10),
            (i0_10, 1, i1_10),
            (i0_10, 5, i5_10),
            (i0_10, 10, ten),
            (i0_10, 11, empty),
            (i0_10, 100, empty),
            (empty, 0, empty),
        ];
        for (x, y, r) in cases.into_iter() {
            assert!(
                x.shrink_left(y) == r,
                "{:?} shrink_left {:?} is not equal to {:?}",
                x,
                y,
                r
            );
        }
    }

    #[test]
    fn shrink_right_test() {
        let cases = vec![
            (i0_10, 15, i0_10),
            (i0_10, 10, i0_10),
            (i0_10, 9, i0_9),
            (i0_10, 5, i0_5),
            (i0_10, 0, zero),
            (i0_10, -1, empty),
            (i0_10, -100, empty),
            (empty, 0, empty),
        ];
        for (x, y, r) in cases.into_iter() {
            assert!(
                x.shrink_right(y) == r,
                "{:?} shrink_right {:?} is not equal to {:?}",
                x,
                y,
                r
            );
        }
    }

    #[test]
    fn add_sub_mul_bound_test() {
        // For each cases (x, y, r1, r2, r3)
        // * x and y are the values
        // * r1,r2 and r3 are the results of `x + y`, `x - y` and `x * y`
        let cases = vec![
            (zero, 0, zero, zero, zero),
            (i1_2, 0, i1_2, i1_2, zero),
            (empty, 0, empty, empty, empty),
            (invalid, 0, empty, empty, empty),
            (zero, 1, one, (-1, -1).to_interval(), zero),
            (i1_2, 1, (2, 3).to_interval(), (0, 1).to_interval(), i1_2),
            (empty, 1, empty, empty, empty),
            (invalid, 1, empty, empty, empty),
            (zero, 3, (3, 3).to_interval(), (-3, -3).to_interval(), zero),
            (
                i1_2,
                3,
                (4, 5).to_interval(),
                (-2, -1).to_interval(),
                (3, 6).to_interval(),
            ),
            (empty, 3, empty, empty, empty),
            (invalid, 3, empty, empty, empty),
        ];

        for &(x, y, r1, r2, r3) in &cases {
            assert!(x + y == r1, "{:?} + {:?} is not equal to {:?}", x, y, r1);
            assert!(x - y == r2, "{:?} - {:?} is not equal to {:?}", x, y, r2);
            assert!(x * y == r3, "{:?} * {:?} is not equal to {:?}", x, y, r3);
        }
    }

    #[test]
    fn add_test() {
        // For each cases (x, y, res)
        // * x and y are the values
        // * res is the result of `x + y`
        let sym_cases = vec![
            (zero, zero, zero),
            (i1_2, i1_2, (2, 4).to_interval()),
            (empty, empty, empty),
            (invalid, invalid, empty),
            // ||
            // |-|
            (empty, zero, empty),
            (invalid, zero, empty),
            (empty, invalid, empty),
            // ||
            //|--|
            (empty, i1_2, empty),
            (empty, i0_10, empty),
            (invalid, i1_2, empty),
            (zero, i0_10, i0_10),
            (i1_2, i0_10, (1, 12).to_interval()),
            (im5_10, i0_10, (-5, 20).to_interval()),
            (im5_10, im30_m20, (-35, -10).to_interval()),
        ];

        for &(x, y, r) in &sym_cases {
            assert!(x + y == r, "{:?} + {:?} is not equal to {:?}", x, y, r);
            assert!(y + x == r, "{:?} + {:?} is not equal to {:?}", y, x, r);
        }
    }

    #[test]
    fn sub_test() {
        // For each cases (x, y, res)
        // * x and y are the values
        // * res is the result of `x - y`
        let cases = vec![
            (zero, zero, zero),
            (i1_2, i1_2, (-1, 1).to_interval()),
            (empty, empty, empty),
            (invalid, invalid, empty),
            // ||
            // |-|
            (empty, zero, empty),
            (invalid, zero, empty),
            (empty, invalid, empty),
            // ||
            //|--|
            (empty, i1_2, empty),
            (empty, i0_10, empty),
            (invalid, i1_2, empty),
        ];

        // For each cases (x, y, (res1, res2))
        // * x and y are the values
        // * res1 is the result of `x - y` and res2 of `y - x`
        let sym_cases = vec![
            (zero, i0_10, ((-10, 0), (0, 10))),
            (i1_2, i0_10, ((-9, 2), (-2, 9))),
            (im5_10, i0_10, ((-15, 10), (-10, 15))),
            (im5_10, im30_m20, ((15, 40), (-40, -15))),
        ];

        for &(x, y, r) in &cases {
            assert!(x - y == r, "{:?} - {:?} is not equal to {:?}", x, y, r);
            assert!(y - x == r, "{:?} - {:?} is not equal to {:?}", y, x, r);
        }

        for &(x, y, (r1, r2)) in &sym_cases {
            let r1 = r1.to_interval();
            let r2 = r2.to_interval();
            assert!(x - y == r1, "{:?} - {:?} is not equal to {:?}", x, y, r1);
            assert!(y - x == r2, "{:?} - {:?} is not equal to {:?}", y, x, r2);
        }
    }

    #[test]
    fn mul_test() {
        // For each cases (x, y, res)
        // * x and y are the values
        // * res is the result of `x * y`
        let sym_cases = vec![
            (zero, zero, zero),
            (i1_2, i1_2, (1, 4).to_interval()),
            (empty, empty, empty),
            (invalid, invalid, empty),
            // ||
            // |-|
            (empty, zero, empty),
            (invalid, zero, empty),
            (empty, invalid, empty),
            // ||
            //|--|
            (empty, i1_2, empty),
            (empty, i0_10, empty),
            (invalid, i1_2, empty),
            (zero, i0_10, zero),
            (one, i0_10, i0_10),
            (i1_2, i0_10, (0, 20).to_interval()),
            (im5_10, i0_10, (-50, 100).to_interval()),
            (im5_10, im30_m20, (-300, 150).to_interval()),
        ];

        for &(x, y, r) in &sym_cases {
            assert!(x * y == r, "{:?} * {:?} is not equal to {:?}", x, y, r);
            assert!(y * x == r, "{:?} * {:?} is not equal to {:?}", y, x, r);
        }
    }

    #[test]
    fn test_lattice() {
        use gcollections::ops::lattice::test::*;
        use trilean::SKleene::*;
        let whole = Interval::<i32>::whole();
        let tester = LatticeTester::new(
            0,
            /* data_a */ vec![empty, empty, whole, zero, zero, zero, i1_2, i0_10, im5_5],
            /* data_b */ vec![zero, whole, empty, zero, one, i1_2, i0_10, im5_5, i6_10],
            /* a |= b*/
            vec![
                True, True, False, True, Unknown, Unknown, True, Unknown, Unknown,
            ],
            /* a |_| b */ vec![empty, empty, empty, zero, empty, empty, i1_2, i0_5, empty],
            /* a |-| b */ vec![zero, whole, whole, zero, i0_1, i0_2, i0_10, im5_10, im5_10],
        );
        tester.test_all();
    }

    #[test]
    fn test_ser_de_interval() {
        let interval = Interval::new(10, 20);
        assert_tokens(
            &interval,
            &[
                Token::Tuple { len: 2 },
                Token::I32(10),
                Token::I32(20),
                Token::TupleEnd,
            ],
        );
    }

    #[test]
    fn test_de_interval_mixed_types() {
        let interval = Interval::new(-5, 15);
        assert_de_tokens::<Interval<i32>>(
            &interval,
            &[
                Token::Tuple { len: 2 },
                Token::I32(-5),
                Token::I64(15),
                Token::TupleEnd,
            ],
        );
    }

    #[test]
    fn test_de_interval_extra_token() {
        assert_de_tokens_error::<Interval<i32>>(
            &[
                Token::Tuple { len: 3 },
                Token::I32(10),
                Token::I32(20),
                Token::I32(30),
                Token::TupleEnd,
            ],
            "invalid length 3, expected tuple of two numbers or none",
        );
    }

    #[test]
    fn test_de_interval_extra_tokens() {
        assert_de_tokens_error::<Interval<i32>>(
            &[
                Token::Tuple { len: 5 },
                Token::I32(10),
                Token::I32(20),
                Token::I32(30),
                Token::I32(40),
                Token::I32(50),
                Token::TupleEnd,
            ],
            "invalid length 5, expected tuple of two numbers or none",
        );
    }

    #[test]
    fn test_ser_de_interval_u8() {
        let interval = Interval::<u8>::new(10, 20);
        assert_tokens(
            &interval,
            &[
                Token::Tuple { len: 2 },
                Token::U8(10),
                Token::U8(20),
                Token::TupleEnd,
            ],
        );
    }

    #[test]
    fn test_ser_de_interval_i64() {
        let interval = Interval::<i64>::whole();
        assert_tokens(
            &interval,
            &[
                Token::Tuple { len: 2 },
                Token::I64(<i64 as Width>::min_value()),
                Token::I64(<i64 as Width>::max_value()),
                Token::TupleEnd,
            ],
        );
    }

    #[test]
    fn test_ser_de_empty_interval() {
        let interval = Interval::<i32>::empty();
        assert_tokens(&interval, &[Token::None]);
    }

    #[test]
    fn range_inclusive_to_interval_test() {
        let interval = (-4..=25).to_interval();
        assert_eq!(&interval, &Interval::new(-4, 25));
    }

    #[test]
    fn empty_range_inclusive_to_interval_test() {
        let interval = (8..=3).to_interval();
        assert_eq!(&interval, &Interval::empty());
    }

    #[test]
    fn range_from_to_interval_test() {
        let interval = (23u8..).to_interval();
        assert_eq!(&interval, &Interval::new(23, 254));
    }

    #[test]
    #[should_panic]
    fn range_from_u8_to_interval_edge_case_test() {
        let _ = (255u8..).to_interval();
    }

    #[test]
    #[should_panic]
    fn range_from_i8_to_interval_edge_case_test() {
        let _ = (-128i8..).to_interval();
    }

    #[test]
    fn range_to_inclusive_to_interval_test() {
        let interval = (..=8u8).to_interval();
        assert_eq!(&interval, &Interval::new(0, 8));
    }

    #[test]
    #[should_panic]
    fn range_to_inclusive_u8_to_interval_edge_case_test() {
        let _ = (..=255u8).to_interval();
    }

    #[test]
    #[should_panic]
    fn range_to_inclusive_i8_to_interval_edge_case_test() {
        let _ = (..=-128i8).to_interval();
    }
}
