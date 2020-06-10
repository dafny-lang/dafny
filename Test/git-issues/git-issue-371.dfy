// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module MA {
  module Inner {
    type T17 = x | 0 <= x < 17
  }
}

import MA.Inner  // currently disallowed, but I think it should be allowed
class ZZ {
var zz: Inner.T17;
}
