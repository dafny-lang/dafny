// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait J1{
  var x: int;
}

trait J2{
  var y: int;
}

class C extends J1, J2{
}

method Main()
{
  var c := new C;
  var j1: J1 := new C;
  var j2: J2 := new C;

  c.x := 10;
  c.y := 20;
  j1.x := 20;
  j2.y := 10;

  print "c.x + c.y = " , c.x + c.y, "\n";
  print "j1.x + j2.y = " , j1.x + j2.y, "\n";

  assert c.x + c.y == j1.x + j2.y;
}
