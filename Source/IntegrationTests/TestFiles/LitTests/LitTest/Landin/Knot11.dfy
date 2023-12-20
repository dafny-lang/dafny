// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


datatype Pack<T> = Pack(ghost c: T)

class Ref {
  ghost var hogp: Pack<() ~> int>
}

method Main()
  ensures false
{
  var r := new Ref;
  // error: r.hogp calls itself without decreasing
  r.hogp := Pack(() reads r, r.hogp.c.reads() => if r.hogp.c.requires() then 1 + r.hogp.c() else 0);
}