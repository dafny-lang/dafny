// RUN: %dafny /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


method ResolutionErrors() {
    var x;
    var g5 := x, y => (y, x);   // fail at resolution
    var g6 := x, (y => (y, x)); // fail at resolution
}

// cannot assign functions

class Apa {
  function f() : int {
    0
  }
}

method Nope3() {
  var apa := new Apa;
  apa.f := () => 2;
}

method RequiresFail(f : int -> int)
  // ok
  requires f(0) == 0;
  requires f.requires(0);
  requires f.reads(0) == {};

  // fail
  requires f(0) == true;
  requires f(1,2) == 0;
  requires f(true) == 0;
  requires f.requires(true);
  requires f.requires(1) == 0;
  requires f.requires(1,2);
  requires f.reads(true) == {};
  requires f.reads(1) == 0;
  requires f.reads(1,2) == {};
{
}

method Bogus()
{
  var f;
  f := x reads 1 => x;
  f := x requires 1 => x;
}

predicate method Bool()
{
  true
}

method Bla() {
  assert Bool;
}

