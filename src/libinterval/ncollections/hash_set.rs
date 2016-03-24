// Copyright 2015 Pierre Talbot (IRCAM)

// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::collections::HashSet as StdHashSet;
use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hash};
use std::ops::{Deref, DerefMut};

pub struct HashSet<T, S = RandomState>
{
  hs: StdHashSet<T, S>
}

impl<T, S> HashSet<T, S> where
  T: Eq + Hash,
  S: BuildHasher
{
  pub fn wrap(hs: StdHashSet<T, S>) -> HashSet<T, S> {
    HashSet{hs: hs}
  }
}

impl<T, S> Deref for HashSet<T, S>
{
  type Target = StdHashSet<T, S>;

  fn deref<'a>(&'a self) -> &'a StdHashSet<T, S> {
    &self.hs
  }
}

impl<T, S> DerefMut for HashSet<T, S>
{
  fn deref_mut<'a>(&'a mut self) -> &'a mut StdHashSet<T, S> {
    &mut self.hs
  }
}
