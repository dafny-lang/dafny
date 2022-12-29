// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  import B
  module S {
    import T
    const x := T.y
  }
}

module B {
}

module A.T {  // this is imported by A.S above
  const y := 15
}

module Duplicates {
  module A {
    module B { }
  }
  module A.B { }  // error: duplicate module name: B
  module M.N { }
  module M {
    module N { }  // error: duplicate module name: N
  }

  module E.I.E.I.O { }
  module E.I.E.I.O { }  // error: duplicate module name: O
}
