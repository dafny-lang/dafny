// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Checks that too many ^ gives an error
module A {
  module B {
    module C {
    }
    module D {
      import X = ^.C
    }
    module E {
      import X = ^.^.C
    }
    module F {
      import X = ^.^.^.C
    }
    module G {
      import X = ^.^.^.^.C
    }
  }
  module C {
  }
}

module C{}
