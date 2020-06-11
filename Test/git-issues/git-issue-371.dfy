// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module MA {
  module Inner {
    type T17 = x | 0 <= x < 17
  }
}

module MB {
  module I {
    export Z provides T42 
    type T42 = x | 0 <= x < 42
  } 
}


import MA.Inner
import MB.I`Z

class ZZ {
var zz: Inner.T17;
var yy: I.T42;
}
