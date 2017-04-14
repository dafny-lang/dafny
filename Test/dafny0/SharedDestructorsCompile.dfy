// RUN: %dafny /compile:3 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Dt =
  | A(x: int, y: real)
  | B(h: MyClass, x: int)
  | C(y: real)

class MyClass { }

method Main()
{
  var o := new MyClass;
  var s := [A(10, 12.0), B(o, 6), C(3.14)];
  assert s[0].x == 10 && s[0].y == 12.0;
  assert s[1].h == o && s[1].x == 6;
  assert s[2].y == 3.14;
  
  var d := s[0];
  print d, ":  x=", d.x, " y=", d.y, "\n";
  d := s[1];
  print d, ":  h=", d.h, " x=", d.x, "\n";
  d := s[2];
  print d, ":  y=", d.y, "\n";

  s := [A(71, 0.1), B(o, 71)];
  var i := 0;
  while i < |s|
  {
    print d, "\n";
    d := s[i];
    assert d.x == 71;
    i := i + 1;
  }
}
