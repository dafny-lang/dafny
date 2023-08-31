// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M(x: int)
{
  var unit := ();
  var expr := (x);
  var pair := (x, x);
  var triple := (x, x, x);
}

method N(x: int, y: int)
{
  var unit: () := ();
  var expr: int := (x);
  var pair: (int,int) := (x, x);
  var triple: (int,int,int) := (y, x, x);

  assert unit == ();
  assert pair.0 == pair.1;
  assert triple.2 == x;
  assert triple.0 == triple.1;  // error: they may be different

  var k := (24, 100 / y);  // error: possible division by zero
  assert 2 <= k.0 < 29;

  var k0 := (5, (true, 2, 3.14));
  var k1 := (((false, 10, 2.7)), 100, 120);
  if k0.1 == k1.0 {
    assert false;
  } else if k0.1.1 < k1.0.1 {
    assert k1.2 == 120;
  }
}

module Regression {
  datatype MyDt = A | B | C
  class MyClass { }
  type MySynonym = int

  method M(tuple: (int, MyDt))
  {
    match tuple
    case (x, y) =>
  }

  method P(tuple: (MyClass, MyDt))
  {
    match tuple  // regression: this once used to crash
    case (x, y) =>
  }

  method Q(tuple: (MySynonym, MyDt))
  {
    match tuple
    case (x, y) =>
  }
}
