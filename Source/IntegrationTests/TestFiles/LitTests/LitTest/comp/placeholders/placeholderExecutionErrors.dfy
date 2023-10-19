// RUN: ! %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

placeholder module NeverReplaced {
  method Foo() returns (i: int) 
    ensures i >= 2
}

method Main() {
  var x := NeverReplaced.Foo();
  print x, "\n";
}