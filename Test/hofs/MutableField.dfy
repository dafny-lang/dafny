// RUN: %exits-with 2 %dafny /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


class C {
  function method f(x : int) : int { x }

  var g : int -> int;

  method M() modifies this;
  {
    f := g; // not ok
  }
}

