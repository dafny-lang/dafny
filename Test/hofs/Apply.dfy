// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


method Apply(x : int) returns (i : int)
  ensures i == x;
{
  i := (x => x)(x);
}

function method Const<A,B>(a : A) : B -> A {
  b => a
}

method Test(m : map<int, int -> int -> int>)
{
  assume forall i :: i in m;
  assume forall i, x :: m[i].requires(x);
  assume forall i, x, y :: m[i](x).requires(y);
  assume m[1](2)(3) > 5;
  assert ((m[1])(2))(3) > 4;
}

method Main() {
  assert forall x : int, y : int :: Const(x)(y) == (Const(x))(y);
  assert (a => b => a) == (u : int) => (v : int) => u;
  assert Const == (u : int) => (v : int) => u;
}

