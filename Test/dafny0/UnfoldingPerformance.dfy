// RUN: %exits-with 4 %dafny /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var x: nat
  function IgnoreFuel(): nat
    reads this
  {
    x
  }
}

function Fib(n: int): int
{
  if n < 2 then n else Fib(n-2) + Fib(n-1)
}

method Test0() {
  var c := new C;
  var f := Fib(c.IgnoreFuel());
  // with the bug, the following wwould take a long time before it reports an error
  // after the bug fix, this still fails, but quickly
  assert 0 <= f;
}

method Test1() {
  var c := new C;
  var f := Fib(c.x);
  // the following assert will also fail, but quickly
  assert 0 <= f;
}

method Test2() {
  var c := new C;
  c.x := 10;
  var f := Fib(c.IgnoreFuel());
  assert 0 <= f;  // passes
}

method Test3() {
  var c := new C;
  c.x := 10;
  var f := Fib(c.x);
  assert 0 <= f;  // passes
}

method Test4() {
  var c := new C;
  c.x := 10;
  var f := Fib(c.x - 2);
  assert 0 <= f;  // fails
}

method Test5(x: int)
  requires 9 <= x - 1 && x + 1 <= 11
{
  var c := new C;
  c.x := x;
  var f := Fib(c.x);
  // assert c.x == 10;  // Succeeds if we remind Z3 about the Lit value of c.x
  assert 0 <= f;  // fails, b/c we lose track of the Lit argument
}
