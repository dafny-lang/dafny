// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/// This file checks that refinement works for members of newtypes and
/// datatypes.

abstract module A {
  datatype D = D {
    function f(): int
    function g(): int { 1 }
  }

  newtype NT0 = int {
    function f(): int
    function g(): int { 1 }
  }

  newtype NT = x: int | x >= 0 witness 0 {
    function f(): int
    function g(): int { 1 }
  }
}

module B refines A {
  datatype D ... {
    function f() : int { 1 }
    function g ...
  }

  newtype NT0 ... {
    function f() : int { 1 }
    function g ...
  }

  newtype NT ... {
    function f() : int { 1 }
    function g ...
  }
}

module Parent {
  type t
  newtype pos = n: nat | n > 0 witness 1
  datatype Bool = True | False
}

module Child refines Parent {
  type t
  newtype pos ... {
    method Print() { print this; }
  }
  datatype Bool ... {
    function AsDafnyBool() : bool { this.True? }
  }
}
