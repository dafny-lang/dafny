// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

predicate SuppressNoTriggerWarning<X>(x: X) { true }

trait Tr {
  var x: int
}

class C extends Tr {
  var y: int
}

class D extends Tr {
  var z: int
}

method M(t: Tr)
  modifies t
{
  print "t.x=", t.x, "  ";
  var s: set<C> := set c: C | c == t && SuppressNoTriggerWarning(c);  // this line used to crash for the call M(d)
  if s == {} {
    print "The given Tr is not a C\n";
  } else {
    var c :| c in s;
    print "The given Tr is a C, and c.y=", c.y, "\n";
    c.y := c.y + 10;
  }
}

method Main() {
  var c := new C;
  var d := new D;
  c.x, c.y := 5, 6;
  d.x, d.z := 100, 102;

  M(c);
  M(d);
  M(c);
}

