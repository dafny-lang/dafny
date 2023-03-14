// RUN: %exits-with 4 %dafny /dprint:- /env:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost predicate P(n: int)
{
  n % 2 == 0
}

ghost predicate R(r: real)
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
    var z := x + y.Floor;
    var w := x as real + y;
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
      even, alsoEven := x, y.Floor;  // this assigns to 'alsoEven' a possibly odd number
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

ghost function f(s:set<int>):int
{
  if x :| x in s then x else 0
}

// -------------- optional curly-brace syntax

predicate AltSyntaxP(x: int) { true }
datatype Color = Red | Green | Blue

method AltSyntax0(x: int, y: int, c: Color) returns (z: int) {
  if
  case x <= y =>
    z := 10;
  case k :| 0 <= k < 100 && AltSyntaxP(k) =>
    z := k;
  case y <= x =>
    z := 15;
}
method AltSyntax1(x: int, y: int, c: Color) returns (z: int) {
  if
  case x <= y =>
    z := 10;
  case k :| 0 <= k < 100 && AltSyntaxP(k) =>
    z := k;
  case y <= x =>
    z := 15;
  case false =>
    // empty list of statement
  case false =>
    // empty list of statement
}
method AltSyntax2(X: int, Y: int, c: Color) returns (z: int) {
  var x, y := X, Y;
  while
  case x < y =>
    z := 10;
    return;
  case y > x =>
    return 15;
}
method AltSyntax3(X: int, Y: int, c: Color) returns (z: int) {
  var x, y := X, Y;
  while
    decreases y - x
  case x < y =>
    z := 10;
    x := x + 1;
  case y > x =>
    z := 15;
    y := y - 1;
}
method AltSyntax4(X: int, Y: int, c: Color) returns (z: int) {
  var x, y := X, Y;
  while
    invariant true
    decreases y - x
  case x < y =>
    z := 10;
    x := x + 1;
}
method AltSyntax5(X: int, Y: int, c: Color) returns (z: int) {
  var x, y := X, Y;
  while
    invariant true
  case false =>
    z := 10;
    x := x + 1;
}
method AltSyntax6(X: int, Y: int, c: Color) returns (z: int) {
  var x, y := X, Y;
  while
    decreases y - x
  case x < y =>
    z := 10;
    x := x + 1;
  case y > x =>
    z := 15;
    y := y - 1;
  case false =>
    // empty list of statement
  case false =>
    // empty list of statement
}
method AltSyntax7(X: int, Y: int, c: Color) returns (z: int) {
  match c
  case Red =>
    z := X + Y;
  case Green =>
    z := X + Y;
  case Blue =>
    z := X + Y;
}
method AltSyntax8(X: int, Y: int, c: Color) returns (z: int) {
  match c
  case Red =>
    z := X + Y;
  case Green =>
    // empty list of statement
  case Blue =>
    // empty list of statement
}
method AltSyntax9(x: int, y: int, c: Color) returns (z: int) {
  if {
    case true =>
  }
  z := x + y;
  while {
    case false =>
  }
  z := x + y;
  match c {  // error (x2): missing cases
    case Red =>
  }
  z := x + y;
}
