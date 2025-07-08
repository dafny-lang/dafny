// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


class Ref {
  ghost var hogp: () ~> int
}

method LogicKnot(r1: Ref,r2: Ref)
  modifies r1, r2
  ensures false
{
  // error: r1.hogp and r2.hogp call each others without decreasing
  r1.hogp := () reads r2, r2.hogp.reads() => if r2.hogp.requires() then 1 + r2.hogp() else 0;
  r2.hogp := () reads r1, r1.hogp.reads() => if r1.hogp.requires() then 1 + r1.hogp() else 0;
}

method Main()
  ensures false
{
  var r1 := new Ref;
  var r2 := new Ref;
  LogicKnot(r1,r2);
}