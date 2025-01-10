// RUN: %testDafnyForEachResolver --expect-exit-code=2 --refresh-exit-code=4 "%s" -- --general-traits=datatype

trait Parent {}

datatype D extends Parent = D
codatatype Co extends Parent = Co

method TestAEq(d: D, co: Co, p: Parent) {
  // The expressions in these assertions once caused malformed Boogie
  if
  case true =>
    assert p == d; // error: possible assertion violation
  case true =>
    assert d == p; // error: possible assertion violation
  case true =>
    assert p == co; // error: possible assertion violation
  case true =>
    assert co == p; // error: possible assertion violation
}

method TestANeq(d: D, co: Co, p: Parent) {
  // The expressions in these assertions once caused malformed Boogie
  if
  case true =>
    assert p != d; // error: possible assertion violation
  case true =>
    assert d != p; // error: possible assertion violation
  case true =>
    assert p != co; // error: possible assertion violation
  case true =>
    assert co != p; // error: possible assertion violation
}

method TestB(d: D, co: Co, p: Parent) returns (ghost b: bool) {
  b := p == d;
  b := d == p;

  b := p == co;
  b := co == p;

  b := p != d;
  b := d != p;

  b := p != co;
  b := co != p;
}
