// RUN: %dafny /compile:3  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const one:int := 1
const two:int := one * 2
const three:int := one + two
const Pi:real := 3.14

class Calendar {
  static const months:int := 12
  static const weeks:int := 52
}

method Main() {
  print "one := ", one, "\n";
  print "two := ", two, "\n";
  print "three := ", three, "\n";
  assert three == 3;
  print "Pi := ", Pi, "\n";
  assert Pi == 3.14;
  var weeks := Calendar.weeks;
  print "months := ", Calendar.months, "\n";
  print "weeks := ", weeks, "\n";
  assert weeks == 52;

  var c := new C;
  var tu := c.M();  // 11
  print tu, " ";
  print c.G(c), " ";  // 16
  print c.H(c), " ";  // 173
  print C.x, " ";  // 6
  var g := new Generic<real>;
  var putItHere := g.y;
  print putItHere, " ";  // 63
  var go := g.M();
  print go, "\n";  // 63
}

class C {
  static const x: int := y+1
  static const y: int := 5
  var z: int
  static function method G(c: C): int
    requires c != null
    ensures G(c) == 16
  {
    x + y + c.y
  }
  
  const a: int := b+2
  const b: int := 50
  function method H(c: C): int
    requires c != null
    ensures H(c) == 50 + 52 + 50 + 6 + 5 + 5 + 5 == 173
  {
    a + b + c.b + x + y + c.y + C.y
  }
  
  method M() returns (r: int)
    ensures r == 11
  {
    r := x + y;
  }
}

class Generic<G> {
  const y: int := 63
  method M() returns (q: int)
    ensures q == 63
  {
    q := this.y;
  }
}
