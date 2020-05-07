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

module ForbiddenCycles {
  // The following two traits would form a cycle
  trait A extends B { }  // error: cycle
  trait B extends A { }

  trait SelfLoop extends SelfLoop { }  // error: cycle

  trait K<Y> extends M<Y> { }  // error: cycle
  trait L<X> extends K<(X,int)> { }
  trait M<U> extends L<U --> int>, B { }

  trait P extends B { }
}
