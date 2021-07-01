// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function f<X(0)>(): X
{
  var x: X :| true;
  x
}

type low_int = t | 0 <= t < 256
type high_int = t | 1000 <= t < 2000 witness 1000

method False()
  // Regression: the following postcondition was once provable
  ensures false
{
  var x: int := f();
  var y: low_int := f();
  var z: high_int := f();
  // Regression: the following assertions were once provable
  assert x == y; // error
  assert x == z; // error
}
