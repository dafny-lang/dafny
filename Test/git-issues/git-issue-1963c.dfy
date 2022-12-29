// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/// This file checks that refinement works for members of newtypes and
/// datatypes.

abstract module A {
  datatype D = D {
    function method f(): int
    function method g(): int { 1 }
  }

  newtype NT0 = int {
    function method f(): int
    function method g(): int { 1 }
  }

  newtype NT = x: int | x >= 0 witness 0 {
    function method f(): int
    function method g(): int { 1 }
  }
}

module B refines A {
  datatype D ... {
    function method f() : int { 1 }
    function method g ...
  }

  newtype NT0 ... {
    function method f() : int { 1 }
    function method g ...
  }

  newtype NT ... {
    function method f() : int { 1 }
    function method g ...
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
    function method AsDafnyBool() : bool { this.True? }
  }
}
