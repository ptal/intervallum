// Copyright 2015 Pierre Talbot (IRCAM)

// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use ncollections::ops::*;
use num::One;

macro_rules! integer_basic_ops_impl
{
  ( $( $source:ty, $size:ty ),* ) =>
  {$(
    impl Cardinality for $source
    {
      type Size = $size;
      fn size(&self) -> $size {
        <$size as One>::one()
      }
    }

    impl Singleton<$source> for $source {
      fn singleton(value: $source) -> $source {
        value
      }
    }

    impl Bounded for $source {
      type Bound = $source;
      fn lower(&self) -> $source {
        *self
      }
      fn upper(&self) -> $source {
        *self
      }
    }

    impl Contains<$source> for $source
    {
      fn contains(&self, value: &$source) -> bool {
        self == value
      }
    }

    impl Disjoint for $source
    {
      fn is_disjoint(&self, value: &$source) -> bool {
        self != value
      }
    }

    impl Subset for $source
    {
      fn is_subset(&self, value: &$source) -> bool {
        self == value
      }
    }

    impl ProperSubset for $source
    {
      fn is_proper_subset(&self, _value: &$source) -> bool {
        false
      }
    }

    impl Overlap for $source
    {
      fn overlap(&self, value: &$source) -> bool {
        self == value
      }
    }
  )*}
}

integer_basic_ops_impl!(i8,u8,u8,u8,i16,u16,u16,u16,i32,u32,u32,u32,i64,u64,u64,u64,isize,usize,usize,usize);

#[cfg(test)]
mod tests {
  use ncollections::ops::*;

  #[test]
  fn simple_tests() {
    for ref i in -2i32..10 {
      assert_eq!(i.size(), 1u32);
      assert_eq!(i.is_singleton(), true);
      assert_eq!(i.is_empty(), false);
      let res: i32 = Singleton::singleton(*i);
      assert_eq!(res, *i);
      assert_eq!(i.lower(), *i);
      assert_eq!(i.upper(), *i);
      for ref j in -10..10 {
        assert_eq!(i.contains(j), j.contains(i));
        assert_eq!(i.contains(j), i == j);
        assert_eq!(i.is_subset(j), i.contains(j));
        assert_eq!(i.overlap(j), i.contains(j));
        assert_eq!(i.is_subset(j), j.is_subset(i));

        assert_eq!(i.is_disjoint(j), j.is_disjoint(i));
        assert_eq!(i.is_disjoint(j), i != j);
        assert_eq!(i.is_proper_subset(j), false);
        assert_eq!(j.is_proper_subset(i), false);
      }
    }
  }
}
