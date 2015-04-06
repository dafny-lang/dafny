// RUN: %dafny /compile:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait TT
{
  function method Plus(x:int, y:int) : int
    requires x > y
  {
     x + y
  }
  function method Times(x:int, y:int) : int
    requires x > y
  static function method StaticMinus(x:int, y:int) : int
    requires x > y
  {
     x - y
  }

  method Double(x: int)
  {
    print "d=", x+x, "\n";
  }
  method AddFive(x: int)
  static method StaticTriple(x: int)
  {
    print "t=", 3*x, "\n";
  }
}

class CC extends TT
{
  function method Times(x:int, y:int) : int
    requires x>y
  {
    x * y
  }
  method AddFive(x: int)
  {
    print "a5=", x+5, "\n";
  }
}

method Client(t: TT)
  requires t != null
{
  var x := t.Plus(10, 2);
  print "x=", x, "\n";
  t.Double(400);
  t.AddFive(402);
  t.StaticTriple(404);
}

method Main()
{
  var c := new CC;
  var y := c.Plus(100, 20);
  print "y=", y, "\n";
  Client(c);
  var z := TT.StaticMinus(50, 20);
  print "z=", z, "\n";
  var z' := CC.StaticMinus(50, 20);
  print "z'=", z', "\n";
  var w := c.StaticMinus(50, 20);
  print "w=", w, "\n";

  c.Double(500);
  c.AddFive(502);
  c.StaticTriple(504);
  TT.StaticTriple(504);
  CC.StaticTriple(505);
}
