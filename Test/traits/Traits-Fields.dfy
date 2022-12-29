// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait J
{
  var x: int;
}

class C extends J
{

}

method Main()
{
  var c := new C;
  var j: J? := new C;

  j.x := 8;
  c.x := 9;
  assert j.x + 1 == c.x;

  j := c;
  assert j.x == 9;

  print "j"; Print(j);
  print "c"; Print(c);

  c := null;
  assert j != null;
  j := null;
}

method Print(j: J)
{
  print ".x = ", j.x, "\n";
}
