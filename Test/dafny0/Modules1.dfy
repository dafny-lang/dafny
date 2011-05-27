module A imports B {
  class X {
    function Fx(z: Z): int
      requires z != null;
      decreases 5, 4, 3;
    { z.G() }  // fine; this goes to a different module
  }
  datatype Y = Cons(int, Y) | Empty;
}

class C {
  method M() { }
  function F(): int { 818 }
}

method MyMethod() { }

var MyField: int;

module B {
  class Z {
    method K() { }
    function G(): int
      decreases 10, 8, 6;
    { 25 }
  }
}

static function MyFunction(): int { 5 }

class D { }

method Proc0(x: int)
  decreases x;
{
  if (0 <= x) {
    Proc1(x - 1);
  }
}

method Proc1(x: int)
  decreases x;
{
  if (0 <= x) {
    Proc0(x - 1);
  }
}

method Botch0(x: int)
  decreases x;
{
  Botch1(x - 1);  // error: failure to keep termination metric bounded
}

method Botch1(x: int)
  decreases x;
{
  Botch0(x);  // error: failure to decrease termination metric
}
