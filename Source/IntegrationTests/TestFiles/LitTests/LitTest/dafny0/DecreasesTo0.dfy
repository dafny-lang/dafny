// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


method GoodInstances(x: int, y: int) {
  assert true decreases to false;
  assert 1 decreases to 0;
  assert x decreases to x - 1;
  assert (x, y decreases to x, y - 1); // the parentheses here make this into a "decreases to" expression
  assert y > x ==> (x, (y decreases to x), y - 1) == (x, true, y - 1); // whereas this is a 3-tuple

  var s := {x, y, x*y};
  var s' := s - {x};
  assert  (s, s, s decreases to s, s, s') ;
  assert 0 nonincreases to 0;
}

method Nested() {
  assert (true, (true decreases to false)) == (true, true);
}

method BadInstance1() {
  assert 0 decreases to 1; // error
}

method BadInstance2(x: int) {
  assert x - 1 decreases to x; // error
}

method BadInstance3(x: int, y: int) {
  assert (x, y - 1 decreases to x, y); // error
}

method BadInstance4() {
  assert 0 nonincreases to 1; // error
}

method BadInstance5(i: int, b: bool) {
  assert i decreases to b; // error
}

method BadInstance6() {
  assert 0 decreases to false; // error
}

datatype Color = Red | Green | Blue

method Tuples(x: int) {
  if
  case true =>
    assert (Red, Green) decreases to Red;
  case true =>
    assert (Red, Green) decreases to (Red, Green); // error
  case true =>
    assert (Red, Green) nonincreases to (Red, Green);
  case true =>
    assert (Red, Green) decreases to Blue; // error
  case true =>
    assert x decreases to (x - 1, Blue); // error
  case true =>
    assert (x decreases to x - 1, Blue);
}

method Empties() {
  assert (nonincreases to);
  assert !(decreases to);
  assert (decreases to 2); // yes, because \top decreases to 2,\top
  assert (2 decreases to); // error, because 2,\top does not decreases to \top
}

method M0(c: bool) returns (b: bool)
  ensures b
  decreases c
{
  if c {
    b := M0(false);
  } else {
    b := true;
  }
}

method M1(c: bool) returns (b: bool)
  requires !c
  ensures b decreases to c
{
  b := true;
}
