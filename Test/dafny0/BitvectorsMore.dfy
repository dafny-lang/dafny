// RUN: %exits-with 4 %dafny /print:"%t.print" /rprint:- /env:0 "%s" > "%t"
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

  /*  THE FOLLOWING TIME OUT:
  if a0 && y <= x {
    assert x == y;
  }
  if x <= y {
    assert x != y ==> x < y;
  }
  */
}

newtype EvenInt = x | x % 2 == 0
newtype SmallReal = r | -4.0 <= r < 300.0
newtype Handful = x | 0 <= x < 0x50

ghost predicate PQ(x: int, n: nat, r: real, even: EvenInt, small: SmallReal, b67: bv67, w: bv32, seven: bv7, bb: bv2, noll: bv0, h: Handful)
{
  x == x && n == n && r == r && even == even && small == small &&
  b67 == b67 && w == w && seven == seven && bb == bb && noll == noll && h == h
}

method Shifts0() returns (x: int, n: nat, r: real, even: EvenInt, small: SmallReal, b67: bv67, w: bv32, seven: bv7, bb: bv2, noll: bv0, h: Handful)
  ensures PQ(x, n, r, even, small, b67, w, seven, bb, noll, h)
{
  if {
    case x < 20     => b67 := b67 << x;  // error: x may be negative
    case 0 <= x      => b67 := b67 << x;  // error: x may exceed 67
    case 0 <= x < 67 => b67 := b67 << x;
    case true       => b67 := b67 << n;  // error: n may exceed 67
    case true       => b67 := b67 << h;  // error: h may exceed 67
  }
}
method Shifts1() returns (x: int, n: nat, r: real, even: EvenInt, small: SmallReal, b67: bv67, w: bv32, seven: bv7, bb: bv2, noll: bv0, h: Handful)
  ensures PQ(x, n, r, even, small, b67, w, seven, bb, noll, h)
{
  if {
    case even <= 66      => b67 := b67 << even;  // error: 'even' may be negative
    case 0 <= even       => b67 := b67 << even;  // error: 'even' may exceed 67
    case 0 <= even <= 66  => b67 := b67 << even;
  }
}
method Shifts2() returns (x: int, n: nat, r: real, even: EvenInt, small: SmallReal, b67: bv67, w: bv32, seven: bv7, bb: bv2, noll: bv0, h: Handful)
  ensures PQ(x, n, r, even, small, b67, w, seven, bb, noll, h)
{
  if {
    case true => b67 := b67 << b67;  // error: b67 may exceed 67
    case true => b67 := b67 << w;  // error: w may exceed 67
    case true => b67 := b67 << seven / 2;
    case true => b67 := b67 << bb;
    case true => b67 := b67 << noll;
  }
}
method Shifts3() returns (x: int, n: nat, r: real, even: EvenInt, small: SmallReal, b67: bv67, w: bv32, seven: bv7, bb: bv2, noll: bv0, h: Handful)
  ensures PQ(x, n, r, even, small, b67, w, seven, bb, noll, h)
{
  if {
    case true => w := w << b67;  // error: shift amount may exceed 32
    case true => w := w << w;  // error: shift amount may exceed 32
    case true => w := w << seven;  // error: shift amount may exceed 32
    case true => w := w << bb;
    case true => w := w << noll;
  }
}
method Shifts4() returns (x: int, n: nat, r: real, even: EvenInt, small: SmallReal, b67: bv67, w: bv32, seven: bv7, bb: bv2, noll: bv0, h: Handful)
  ensures PQ(x, n, r, even, small, b67, w, seven, bb, noll, h)
{
  if {
    case true => seven := seven << b67;  // error: shift amount may exceed 7
    case true => seven := seven << w;  // error: shift amount may exceed 7
    case true => seven := seven << seven;  // error: shift amount may exceed 7
    case true => seven := seven << bb;
    case true => seven := seven << noll;
  }
}
method Shifts5() returns (x: int, n: nat, r: real, even: EvenInt, small: SmallReal, b67: bv67, w: bv32, seven: bv7, bb: bv2, noll: bv0, h: Handful)
  ensures PQ(x, n, r, even, small, b67, w, seven, bb, noll, h)
{
  if {
    case true => bb := bb << b67;  // error: shift amount may exceed 2
    case true => bb := bb << w;  // error: shift amount may exceed 2
    case true => bb := bb << seven;  // error: shift amount may exceed 2
    case true => bb := bb << bb;  // error: shift amount may exceed 2
    case true => bb := bb << noll;
  }
}
method Shifts6() returns (x: int, n: nat, r: real, even: EvenInt, small: SmallReal, b67: bv67, w: bv32, seven: bv7, bb: bv2, noll: bv0, h: Handful)
  ensures PQ(x, n, r, even, small, b67, w, seven, bb, noll, h)
{
  if {
    case true => noll := noll << b67;  // error: shift amount may exceed 0
    case true => noll := noll << w;  // error: shift amount may exceed 0
    case true => noll := noll << seven;  // error: shift amount may exceed 0
    case true => noll := noll << bb;  // error: shift amount may exceed 0
    case true => noll := noll << noll;
  }
}

method TestActualShifting()
{
  var a: bv67 := 3;
  assert a << 2 == 12;
  assert a >> 0 == 3;
  assert a >> 1 == 1;
  assert a >> 2 == 0;

  var b: bv5 := 0x18;
  assert b << 1 == 0x10;
  assert b >> 0 == 0x18;
  assert b >> 1 == 0x0C;
  assert b >> 2 == 6;
}

method Rotate() returns (x: nat, bb: bv5) {
   if {
    case true => bb := bb.RotateLeft(x);  // error: rotate amount may exceed 5
    case true => bb := bb.RotateRight(x);  // error: rotate amount may exceed 5
  }
}

method TestActualRotate() {
  var a: bv5 := 12;
	assert a == a.RotateLeft(3).RotateRight(3);
}
