// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


class Ref1 {
  ghost var hogp: () ~> int
}

class Ref2 {
  ghost var r: Ref1
  constructor()
}

method Main()
  ensures false
{
  var r := new Ref2();
  r.r := new Ref1;
  // error: r.r.hogp calls itself without decreasing
  r.r.hogp := () reads r, r.r, r.r.hogp.reads() => if r.r.hogp.requires() then 1 + r.r.hogp() else 0;
}