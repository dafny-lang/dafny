// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"



class C {
  function f(x : int) : int { x }

  var g : int -> int

  method M() modifies this
  {
    f := g; // not ok
  }
}

