// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function OnId(f : (bool -> bool) -> int) : int
  reads f.reads(x => x);
  requires f.requires(y => y);
{
  f(z => z)
}

method Equal() {
  var id1 : bool -> bool := x => x;
  var id2                := y => y;
  assert forall x :: id1(x) == id2(x);
  assert id1 == id2;
}

method K<A,B>(P : (A -> A) -> bool)
  requires P.requires(x => x);
  requires P(y => y);
{
  assert P(z => z);
  assert (x => y => x) == ((a : A) => (b : B) => a);
}

method Main() {
  Equal();
  var p := (x: real -> real) => x(25.0) <= 25.0;
  K<real,bool>(p);
  var f := (b: bool -> bool) => if b(true) then 10 else 11;
  var x := OnId(f);
  print x, " ", f(_ => false), "\n";
}
