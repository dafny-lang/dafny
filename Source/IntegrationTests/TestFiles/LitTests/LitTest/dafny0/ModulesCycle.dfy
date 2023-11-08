// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


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
