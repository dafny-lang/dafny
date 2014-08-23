// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method R1(ghost x: real, ghost y: real, i: int) {
  assert x + y == y + x;
  assert int(real(i)) == i;
  assert real(x.Trunc) <= x;
  if {
    case real(x.Trunc) >= x =>
      assert x.Trunc == int(x);  // the cast to int is allowed here
    case true =>
      var t := int(x);  // error: x may be a non-integer
    case true =>
      assert real(x.Trunc) >= x; // error
  }
}

method R2(ghost x: real, ghost y: real) {
  assert x * x >= real(0);
  assert y != real(0) ==> x / y * y == x;
  assert x / y * y == x; // error(s)
}

// Check that literals are handled properly
method R3() {
  ghost var x := 1.5;
  ghost var y := real(3);
  assert x == y / 2.0000000;  
  assert x == y / 2.000000000000000000000000001;  // error
}

// Check that real value in decreases clause doesn't scare Dafny
function R4(x:int, r:real) : int
{
  if x < 0 then 5
  else R4(x - 1, r)
}

method RoundingDirection()
{
  assert 51.500277.Trunc == 51;
  assert (-0.194771).Trunc == -1;
  assert -0.194771.Trunc == 0;
}
