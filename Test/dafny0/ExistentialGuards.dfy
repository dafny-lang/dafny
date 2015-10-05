// RUN: %dafny /dprint:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(n: int)
{
  n % 2 == 0
}

predicate R(r: real)
{
  0.0 <= r
}

method M0()
{
  if x :| P(x) {
    var y := x + 3;
  }
}

method M1()
{
  if x: int :| P(x) {
  }
}

method M2()
{
  var x := true;
  if x, y :| P(x) && R(y) {  // this declares a new 'x'
    var z := x + 12;
  }
  x := x && false;
}

method M3()
{
  var x := true;
  if x: int, y :| P(x) && R(y) {
    var z := x + y.Trunc;
    var w := real(x) + y;
  }
}

method M4()
{
  if x, y: real :| P(x) && R(y) {
  }
}

method M5()
{
  if x: int, y: real :| P(x) && R(y) {
  }
}

method M6()
{
  if x {:myattribute x, "hello"} :| P(x) {
  }
  if x, y {:myattribute y, "sveika"} :| P(x) && R(y) {
  }
  if x: int {:myattribute x, "chello"} :| P(x) {
  }
  if x {:myattribute x, "hola"} {:yourattribute x + x, "hej"} :| P(x) {
  }
}

ghost method M7() returns (z: real, w: real)
  ensures -2.0 <= z
  ensures z == w  // error: does not hold
{
  var k;
  if x :| P(x) {
    k, z := 4, 18.0;
  } else if * {
    z := z + -z;
  } else if y :| R(y) {
    z := y;
  } else if y :| P(y) {
    k := y;
  } else {
    z :| R(z);
  }
  if P(k) {
    z := 18.0;
  }
}

ghost method M8(m: int, n: int)
  requires forall y :: m <= y < n ==> P(y)
{
  var t := -1;
  var u;
  if y :| m <= y < n && P(y) {
    u := y;
    if * {
      t := n - y;
    } else if * {
      t := y - m;
    } else if P(y) {
      t := 8;
    } else {
      t := -100;  // will never happen
    }
  }
  if t < 0 && m < n {
    assert P(m) && !P(m);
    assert false;
  }
  assert t < 0 ==> n <= m;
}

method P0(m: int, n: int)
  requires m < n
{
  ghost var even, alsoEven := 4, 8;
  if {
    case x :| P(x) =>
      even := x;
    case x: int :| P(x) =>
      even := x;
    case x, y :| P(x) && R(y) =>
      even, alsoEven := x, y.Trunc;  // this assigns to 'alsoEven' a possibly odd number
    case x: int, y :| P(x) && R(y) =>
      even := x;
    case m < n =>  // just to be different
    case x, y: real :| P(x) && R(y) =>
      even := x;
    case x: int, y: real :| P(x) && R(y) =>
      even := x;
  }
  assert P(even);
  assert P(alsoEven);  // error: may not hold
}

method P1(m: int, n: int)
{
  if {  // error: missing case
    case x :| m <= x < n && P(x) =>
  }
}

method P2(m: int, n: int)
  requires forall y :: m <= y < n ==> P(y)
{
  if {  // error: missing case
    case x :| m <= x < n && P(x) =>
  }
}

method P3(m: int, n: int)
  requires m < n && forall y :: m <= y < n ==> P(y)
{
  assert P(m);  // lemma that proves that the following 'if' covers all possibilities
  if {
    case x :| m <= x < n && P(x) =>
  }
}
