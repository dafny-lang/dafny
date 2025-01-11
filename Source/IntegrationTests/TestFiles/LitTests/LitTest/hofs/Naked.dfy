// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


module Functions {
  ghost function f(x: nat): nat
  {
    if x == 0 then 0 else
    if var b: bool :| true; b then
      var h := f;
      h(x-1)
    else
      (f)(x-1)
  }

  ghost function f1(x: nat): nat { if x == 0 then 0 else f2(x - 1) }

  ghost function f2(x: nat): nat { if x == 0 then 0 else (f1)(x - 1) }
}

module Requires {
  ghost function t(x: nat): nat
    requires !t.requires(x)  // error: use of naked function in its own SCC
  { x }

  ghost function g(x: nat): nat
    requires !(g).requires(x)  // error: use of naked function in its own SCC
  { x }

  ghost function D(x: int): int  // used so termination errors don't mask other errors
  ghost function g2(x: int): int decreases D(x) { h(x) }
  ghost function h(x: int): int
    requires !g2.requires(x)  // error: use of naked function in its own SCC
  { x }
}

module Reads {
  ghost function t(x: nat): nat
    reads t.reads(x)
  { x }

  ghost function g(x: nat): nat
    reads (g).reads(x)
  { x }

  ghost function g2(x: int): int
  { h(x) }

  ghost function h(x: int): int
    reads g2.reads(x)
  { x }
}

module ReadsGenerics {
  class Cl<A> {
    ghost function t<B>(a: A, b: B): (A, B)
      reads t.reads(a, b)
    { (a, b) }

    ghost function g<B>(a: A, b: B): (A, B)
      reads (g).reads(a, b)
    { (a, b) }

    ghost function g2<B>(a: A, b: B): (A, B)
    { h(a, b) }

    ghost function h<B>(a: A, b: B): (A, B)
      reads g2.reads(a, b)
    { (a, b) }
  }
}
