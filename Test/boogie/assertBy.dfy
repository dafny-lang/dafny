// RUN: %dafny /compile:0 /print:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
method M() {
  var x := 0; // x#0
  assert x == 0 by {
    var x := x + 2; // x#1 as expected
    var y := 0; // y#0
  }
  var y := 200; // y#1, so this depends on what was generated inside assert-by
}