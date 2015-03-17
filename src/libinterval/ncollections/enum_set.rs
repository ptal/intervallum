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


use collections::enum_set::EnumSet as StdEnumSet;
use collections::enum_set::CLike;
use std::ops::{Deref, DerefMut};

pub struct EnumSet<T>
{
  es: StdEnumSet<T>
}

impl<E: CLike> EnumSet<E>
{
  pub fn wrap(es: StdEnumSet<E>) -> EnumSet<E> {
    EnumSet{es: es}
  }
}

impl<T> Deref for EnumSet<T>
{
  type Target = StdEnumSet<T>;

  fn deref<'a>(&'a self) -> &'a StdEnumSet<T> {
    &self.es
  }
}

impl<T> DerefMut for EnumSet<T>
{
  fn deref_mut<'a>(&'a mut self) -> &'a mut StdEnumSet<T> {
    &mut self.es
  }
}
