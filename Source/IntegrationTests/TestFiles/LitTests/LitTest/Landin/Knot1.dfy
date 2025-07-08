// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


class Ref {
  ghost var hogp: () ~> int
}

method Main()
  ensures false
{
  var r := new Ref;
  // error: r.hogp calls itself without decreasing
  r.hogp := () reads r, r.hogp.reads() => if r.hogp.requires() then 1 + r.hogp() else 0;
}