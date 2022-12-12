// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  type TT = int
}

module MA {
  module Inner {
    type T17 = x | 0 <= x < 17
  }
}

module MB {
  module I {
    type T42 = x | 0 <= x < 42
    type T43 = x | 0 <= x < 43
  }
}

import M  // Error

module A {
  import M
  import M // error
}
