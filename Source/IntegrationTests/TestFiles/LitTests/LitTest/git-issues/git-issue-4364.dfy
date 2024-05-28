// RUN: %testDafnyForEachResolver "%s"

module A {
  function foo(x: int): int {
    x * x
  }

  datatype T = foo(int)

  method M() {
    var x := foo(100);
    assert x is int;
  }
}

module B {
  import opened A
  
  method M() {
    var x := foo(100);
    assert x is T;
  }
}