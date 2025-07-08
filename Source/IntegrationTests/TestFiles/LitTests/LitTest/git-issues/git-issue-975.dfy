// RUN: %testDafnyForEachResolver "%s"


ghost function f():nat
  ensures f() == 0
{                  // no problem for methods
  var x := 0;      // no problem without this
  assert true by {}
  0
}
