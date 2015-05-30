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

use std::collections::HashSet as StdHashSet;
use std::collections::hash_map::RandomState;
use std::collections::hash_state::HashState;
use std::hash::Hash;
use std::ops::{Deref, DerefMut};

pub struct HashSet<T, S = RandomState>
{
  hs: StdHashSet<T, S>
}

impl<T, S> HashSet<T, S> where
  T: Eq + Hash,
  S: HashState
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
