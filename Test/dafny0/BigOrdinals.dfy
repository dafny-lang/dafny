// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /rprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M(o: ORDINAL) returns (p: ORDINAL)
  ensures p == o
{
  var five := 5;
  p := five;
  p := o;
}

method As(o: ORDINAL, x: int) returns (p: ORDINAL, y: int)
{
  if
  case 0 <= x =>
    p := x as ORDINAL;
  case true =>
    p := x as ORDINAL;  // error: x may be negative
  case true =>
    y := o as int;  // error: o may be too big
  case true =>
    var r: ORDINAL := 67;
    y := r as int;
    assert y == 67;
}

method Plus(x: ORDINAL, y: ORDINAL, n: nat)
{
  if * {
    var a: ORDINAL := 100;
    var b: ORDINAL := 105;
    assert a + b == 205;
    assert a < b;
    assert a <= b;
    assert b < a;  // error
  } else if * {
    var z := x + y;
    assert x <= z;
  } else if * {
    var a: ORDINAL := 50;
    var z := x + a;
    if
    case true =>
      assert x <= z;
    case x == n as ORDINAL =>
      assert x <= z;
    case true =>
      assert a <= z;
  } else if * {
    assert x < x + 1;
  } else if * {
    assert x <= 1 + x;
    assert x < 1 + x;  // error: not known
  } else if * {
    assert 0 + x == x == x + 0;
  }
}

method Minus(a: ORDINAL, b: ORDINAL, c: ORDINAL, n: nat)
  requires 10 <= b
{
  if
  case true =>
    var g := a - 1;  // error: a might not be a successor
  case true =>
    var g := b - 12;  // error: b might not be enough of a successor
  case true =>
    var g := b - 1;  // error: in fact, b might not be a successor at all!
  case b == n as ORDINAL =>
    var g := b - 1;
    assert g + 1 == b;
  case b < a =>
    var g := a - 1;  // error: a might not be a successor
  case b < a && a == n as ORDINAL =>
    var g := a - 1;
  case b == n as ORDINAL =>
    assert b - 1 - 1 == b - 2;
  case 10 <= c.Offset =>
    assert c - 1 < c;
  case true =>
    assert c == c - 0;
}

method Less(a: ORDINAL, b: ORDINAL, c: ORDINAL)
{
  if
  case true =>
    assert a < a;  // error
  case true =>
    assert a <= a;
  case true =>
    assert a < b || a == b || b < a;
  case true =>
    assert a <= b || b <= a;
  case a < b && b < c =>
    assert a < c;
  case a <= b <= c =>
    assert a <= c;
  case true =>
    assert 0 <= a;
  case a != 0 =>
    assert 0 < a;
}

type ConstrainedOrdinal = o: ORDINAL | o != 16

method Constraints() returns (x: ORDINAL, y: ConstrainedOrdinal)
{
  if
  case true =>
    x := y;
  case true =>
    y := x;  // error: x may be 16
  case x != 16 =>
    y := x;
  case true =>
    x, y := 27, 27;
  case true =>
    x := 16;
    y := 16;  // error: may not assign 16 to a ConstrainedOrdinal
}

lemma Members(a: ORDINAL, n: nat)
{
  var b: ORDINAL := 25;
  assert b.IsNat;
  assert b.Offset == 25;
  assert !b.IsLimit;
  assert b.IsSucc;

  assert a == n as ORDINAL ==> a.IsNat && a.Offset == n;
  assert a.IsNat ==> exists m: nat :: a == m as ORDINAL;
  assert a.IsNat ==> a as int == a.Offset;

  assert a.Offset == 0 <==> a.IsLimit;
  assert a.Offset > 0 <==> a.IsSucc;
  assert a.IsNat ==> a == a.Offset as ORDINAL;

  if a.Offset != 0 {
    Members(a - 1, n);
  } else {
    forall a' | a' < a {
      Members(a', n);
    }
  }
}
