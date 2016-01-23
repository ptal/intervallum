// Copyright 2015 Pierre Talbot (IRCAM)

// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::collections::BTreeSet as StdBTreeSet;
use std::ops::{Deref, DerefMut};

pub struct BTreeSet<T>
{
  ts: StdBTreeSet<T>
}

impl<T: Ord> BTreeSet<T>
{
  pub fn wrap(ts: StdBTreeSet<T>) -> BTreeSet<T> {
    BTreeSet{ts: ts}
  }
}

impl<T> Deref for BTreeSet<T>
{
  type Target = StdBTreeSet<T>;

  fn deref<'a>(&'a self) -> &'a StdBTreeSet<T> {
    &self.ts
  }
}

impl<T> DerefMut for BTreeSet<T>
{
  fn deref_mut<'a>(&'a mut self) -> &'a mut StdBTreeSet<T> {
    &mut self.ts
  }
}
