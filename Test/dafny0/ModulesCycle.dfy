// RUN: %exits-with 2 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module V {
  import t = T  // error: T is not visible (and isn't even a module)
}

module A {
  import B = C
}

module C {
  import D = A
}

module Kevin {  // error: cyclic import
  module Joe {
    module Nick {
      import Frankie
    }
  }
}

module Frankie {
  import Kevin
  const x := 3
}
