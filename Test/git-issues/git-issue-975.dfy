// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function f():nat
  ensures f() == 0
{                  // no problem for methods
  var x := 0;      // no problem without this
  assert true by {}
  0
}
