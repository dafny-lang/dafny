// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype D = D(x: int)

ghost function Foo(): ()
  ensures assert true by { var D(x) := D(0); } true
{ () }
