// RUN: %dafny /print:"%t.print" /rprint:- /env:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M() {
  var h: bv8 := 5;
  var k := h * 128 / 128;
  assert k == 1;
  h := 3;
  k := h * 128 / 128;
  assert k == 1;

  h := *;
  k := k / h;  // error: division by zero
}

method N0(x: bv7, y: bv7) {
  var z := x / y;  // error: division by zero
}

method N1(x: bv7, y: bv7) {
  var z := x % y;  // error: division by zero
}

method N2(x: bv137, y: bv137) {
  var z := x / y;  // error: division by zero
}

method N3(x: bv0, y: bv0) {
  if * {
    var z := x / y;  // error: division by zero
  } else {
    var z := x % y;  // error: division by zero
  }
}

method N4(x: bv0, y: bv0) returns (z: bv0)
  ensures z == 0  // after all, there is only one value
{
  if {
    case true => z := x + y;
    case true => z := x - y;
    case true => z := x * y;
    case true => z := x & y;
    case true => z := x | y;
    case true => z := x ^ y;
    case true => z := !x;
    case true => z := -x;
    case true => // leave z unchanged
    case true => assert !(x < y);
    case true => assert x <= y;
    case true => assert x >= y;
    case true => assert !(x > y);
  }
}

method P(x: bv0, y: bv0)
  requires x != y  // this ain't possible
{
  assert false;  // no problem
}

method Q(x: bv10, y: bv10)
{
  if x < 0 {
    // not possible
    var z := x / y;  // no problem, because we won't ever get here
  }
}

method R(x: bv60, y: bv60)
{
  var a0, a1;
  
  a0, a1 := x < y, y > x;
  assert a0 == a1;

  a0, a1 := x <= y, y >= x;
  assert a0 == a1;

  /*
  if a0 && y <= x {
    assert x == y;
  }
  if x <= y {
    assert x != y ==> x < y;
  }
  */
}
