// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Functions {
  function f(x: nat): nat
  {
    if x == 0 then 0 else
    if var b: bool :| true; b then
      var h := f;
      h(x-1)
    else
      (f)(x-1)
  }

  function f1(x: nat): nat { if x == 0 then 0 else f2(x - 1) }

  function f2(x: nat): nat { if x == 0 then 0 else (f1)(x - 1) }
}

module Requires {
  function t(x: nat): nat
  requires !t.requires(x);  // error: use of naked function in its own SCC
  { x }

  function g(x: nat): nat
  requires !(g).requires(x);  // error: use of naked function in its own SCC
  { x }

  function D(x: int): int  // used so termination errors don't mask other errors
  function g2(x: int): int decreases D(x) { h(x) }  // error: precondition violation
  function h(x: int): int
    requires !g2.requires(x);  // error: use of naked function in its own SCC
  { x }
}

module Reads {
  function t(x: nat): nat
  reads t.reads(x);
  { x }

  function g(x: nat): nat
  reads (g).reads(x);
  { x }

  function g2(x: int): int { h(x) }

  function h(x: int): int
    reads g2.reads(x);
  { x }
}

