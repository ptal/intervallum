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
