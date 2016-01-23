// Copyright 2015 Pierre Talbot (IRCAM)

// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

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
