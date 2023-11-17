// RUN: %testDafnyForEachResolver "%s"


datatype D = D(x: int)

ghost function Foo(): ()
  ensures assert true by { var D(x) := D(0); } true
{ () }
