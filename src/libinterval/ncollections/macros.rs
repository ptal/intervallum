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

#![macro_use]

// Inspired by the macros from the BigUint impl. (doc.rust-lang.org/num/src/num/bigint.rs.html#235-280)
macro_rules! forward_val_val_binop {
  (impl<$($bn:ident: $(+ $bs:ident)*),*> $imp:ident for $res:ty, $method:ident, $arg:ty) => {
    impl<$($bn: $($bs+)*),*> $imp<$arg> for $res {
      type Output = $res;

      fn $method(self, other: $arg) -> $res {
        (&self).$method(&other)
      }
    }
  }
}

macro_rules! forward_ref_val_binop {
  (impl<$($bn:ident: $(+ $bs:ident)*),*> $imp:ident for $res:ty, $method:ident, $arg:ty) => {
    impl<'a, $($bn: $($bs+)*),*> $imp<$arg> for &'a $res {
      type Output = $res;

      fn $method(self, other: $arg) -> $res {
        self.$method(&other)
      }
    }
  }
}

macro_rules! forward_val_ref_binop {
  (impl<$($bn:ident: $(+ $bs:ident)*),*> $imp:ident for $res:ty, $method:ident, $arg:ty) => {
    impl<'b, $($bn: $($bs+)*),*> $imp<&'b $arg> for $res {
      type Output = $res;

      fn $method(self, other: &$arg) -> $res {
        (&self).$method(other)
      }
    }
  }
}

macro_rules! forward_all_binop {
  (impl<$($bn:ident: $(+ $bs:ident)*),*> $imp:ident for $res:ty, $method:ident, $arg:ty) => {
    forward_val_val_binop!(impl<$($bn: $(+ $bs)*),*> $imp for $res, $method, $arg);
    forward_ref_val_binop!(impl<$($bn: $(+ $bs)*),*> $imp for $res, $method, $arg);
    forward_val_ref_binop!(impl<$($bn: $(+ $bs)*),*> $imp for $res, $method, $arg);
  };
  (impl<$($bn:ident: $(+ $bs:ident)*),*> $imp:ident for $res:ty, $method:ident) => {
    forward_all_binop!(impl<$($bn: $(+ $bs)*),*> $imp for $res, $method, $res);
  };
}
