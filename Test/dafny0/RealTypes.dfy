// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method R1(ghost x: real, ghost y: real, i: int) {
  assert x + y == y + x;
  assert i as real as int == i;
  assert x.Floor as real <= x;
  if {
    case x.Floor as real >= x =>
      assert x.Floor == x as int;  // the cast to int is allowed here
    case true =>
      var t := x as int;  // error: x may be a non-integer
    case true =>
      assert x.Floor as real >= x; // error
  }
}

method R2(ghost x: real, ghost y: real) {
  assert x * x >= 0 as real;
  assert y != 0 as real ==> x / y * y == x;
  assert x / y * y == x; // error(s)
}

// Check that literals are handled properly
method R3() {
  ghost var x := 000_00_0_1.5_0_0_00_000_0;  // 1.5
  ghost var y := 000_000_003 as real;  // 3
  assert x == y / 2.000_000_0;
  assert x == y / 2.000_000_000_000_000_000_000_000_001;  // error
}

// Check that real value in decreases clause doesn't scare Dafny
function R4(x:int, r:real) : int
{
  if x < 0 then 5
  else R4(x - 1, r)
}

method RoundingDirection()
{
  assert 51.500277.Floor == 51;
  assert (-0.194771).Floor == -1;
  assert -0.194771.Floor == 0;
}
