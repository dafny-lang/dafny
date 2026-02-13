// RUN: %testDafnyForEachResolver "%s"

module Wrappers {
  datatype Option<T> = Some(value: T) | None

  class Box<T> {
    var value: T

    constructor(value: T) {
      this.value := value;
    }
  }
}

module A {

  import opened Wrappers

  function DefaultFooArg(): Option<Box<int>>

  method Foo(x: Option<Box<int>> := DefaultFooArg())
    modifies if x.Some? then {x.value} else {}
  {}
}

module B refines A {
  function DefaultFooArg(): Option<Box<int>> {
    None
  }
}

module C {
  import B

  method Bar() {
    B.Foo();
  }
}

// ------------------------
// Smaller repro, plus tests for function calls and datatype constructors with default-value parameters
  
module D {
  function F(): int { 3 }

  method Foo(u: int := F())
    requires u < 10
  {
  }

  function Bar(u: int := F()): int
    requires u < 10
  {
    0
  }

  type Small = x: int | x < 10

  datatype Cell = Cell(s: Small := F())

  method Test() {
    Foo();
    var bar := Bar();
    var cell := Cell();
  }
}
