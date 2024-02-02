// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


class C {

  var f: () ~> bool

  constructor()
    ensures Invariant()
  {
    f := () requires true => true;
  }

  ghost predicate Invariant()
    reads this, f.reads()
  {
    f.requires()
  }

}

method update(t: C)
  modifies t
  requires t.Invariant()
  ensures false
{
  // error: t.f calls itself without decreasing
  t.f := () reads t, t.f.reads() requires t.f.requires() => !t.f();
  assert t.f.requires() == old(t.f).requires();
  var b := t.f();
}

method Main()
{
  var t := new C();
  update(t);
}