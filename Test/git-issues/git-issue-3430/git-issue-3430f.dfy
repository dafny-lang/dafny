// RUN: %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// No new features here
module A {
  module B {
    module C {
    }
    module D {
      import X = C
    }
  }
}

module D {
  import A.B.C
}
