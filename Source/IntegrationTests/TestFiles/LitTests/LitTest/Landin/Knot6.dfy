// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


class Ref {
  ghost var hogp: () ~> int
}

method LogicKnot1(r1: Ref,r2: Ref)
  modifies r1
  ensures r1.hogp == (() reads r2, r2.hogp.reads() => if r2.hogp.requires() then 1 + r2.hogp() else 0)
{
  // error: r1.hogp calls itself through r2.hogp without decreasing
  r1.hogp := () reads r2, r2.hogp.reads() => if r2.hogp.requires() then 1 + r2.hogp() else 0;
}

method LogicKnot2(r1: Ref,r2: Ref)
  modifies r2
  ensures r2.hogp == (() reads r1, r1.hogp.reads() => if r1.hogp.requires() then 1 + r1.hogp() else 0)
{
  // error: r1.hogp calls itself through r1.hogp without decreasing
  r2.hogp := () reads r1, r1.hogp.reads() => if r1.hogp.requires() then 1 + r1.hogp() else 0;
}

method Main()
  ensures false
{
  var r1 := new Ref;
  var r2 := new Ref;
  LogicKnot1(r1,r2);
  LogicKnot2(r1,r2);
}
