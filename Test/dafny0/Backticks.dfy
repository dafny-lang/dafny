// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var x: int
  var y: int
  ghost var z: int

  function F(): int
    reads `x
  {
    x
  }

  function G(): int
    reads `x
  {
    F()
  }

  function H(): int
    reads this
  {
    F()
  }

  function I(n: nat): int
    reads this
  {
    x + y + z + J(n)
  }

  function J(n: nat): int
    reads `x, this`z
    decreases {this}, n, 0
  {
    if n == 0 then 5 else
    I(n-1)  // error: insufficient reads clause
  }

  function K(n: nat): int
    reads `x
    decreases {this}, n+1
  {
    L(n)
  }

  function L(n: nat): int
    reads `x
  {
    if n < 2 then 5 else K(n-2)
  }

  method M()
    modifies `x
  {
    N();
  }

  method N()
    modifies `x
  {
    x := x + 1;
  }

  method O(n: nat)
    modifies this
  {
    P(n);
  }
  method P(n: nat)
    modifies `x
    decreases n, 0
  {
    x := x + 1;
    if n != 0 {
      O(n-1);  // error: insufficient modifies clause to make call
    }
  }
}
