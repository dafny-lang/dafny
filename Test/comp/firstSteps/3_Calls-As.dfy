// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=py "%s" "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
//
// This fragment of comp/Calls.dfy serves to facilitate incremental compiler development.

method A0(x: int, y: bool) {
  return;
}

method A1(x: int, y: bool) returns (a: int) {
  return a;
}

method A2(x: int, y: bool) returns (a: int, b: bool) {
  return a, b;
}

method A3(x: int, y: bool) returns (a: int, b: bool, c: int) {
  var u;
  if x == 3 {
    u := c;
  } else if x == 4 {
    u := c + 0;
  } else {
    u := c + 0 + 0;
  }
  u := 1 * u;
  {
    var y := 65;
    u := 0 + u;
  }
  return a, b, u;
}

method Main()
{
  var a, b, c, d, e, f;
  A0(2, false);
  a := A1(2, false);
  b, c := A2(2, false);
  d, e, f := A3(2, false);
  print a, " ", b, " ", c, " ", d, " ", e, " ", f, "\n";
}
