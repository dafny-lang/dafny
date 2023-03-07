// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Checks that too many ^ gives an error
module A {
  module B {
    module D {
      import X = ^.C // D.C -- error
    }
    module E {
      import X = ^.^.C // B.C -- error
    }
    module F {
      import X = ^.^.^.C // A.C -- error
    }
    module G {
      import X = ^.^.^.^.C // _.C -- OK
    }
    module H {
      import X = ^.^.^.^.^.C // Error
    }
    module P {
      import X = ^
    }
    module Q {
      import X = ^.^.^
    }
  }
}

module C{}
