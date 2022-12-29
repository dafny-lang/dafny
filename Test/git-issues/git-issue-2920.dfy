// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype D = D(x: int)

function Foo(): ()
  ensures assert true by { var D(x) := D(0); } true
{ () }
