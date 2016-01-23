// Copyright 2015 Pierre Talbot (IRCAM)

// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use bit_set::BitSet as StdBitSet;
use std::ops::{Deref, DerefMut};

pub struct BitSet
{
  bs: StdBitSet
}

impl BitSet {
  pub fn wrap(bs: StdBitSet) -> BitSet {
    BitSet{bs: bs}
  }
}

impl Deref for BitSet
{
  type Target = StdBitSet;

  fn deref<'a>(&'a self) -> &'a StdBitSet {
    &self.bs
  }
}

impl DerefMut for BitSet
{
  fn deref_mut<'a>(&'a mut self) -> &'a mut StdBitSet {
    &mut self.bs
  }
}
