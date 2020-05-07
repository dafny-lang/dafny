// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module TheBasics {
  trait A {
  }
  trait B {
  }
  trait C {
  }
  trait D {
  }
  trait X extends A, B {
  }
  trait Y extends C {
  }
  class K extends X, Y, D {
  }
}
