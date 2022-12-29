// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


class C {
  function method f(x : int) : int { x }

  var g : int -> int;

  method M() modifies this;
  {
    f := g; // not ok
  }
}

