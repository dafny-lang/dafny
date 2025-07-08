// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


datatype Pack<T> = Pack(ghost c: T)

class Y {
  const f: Pack<Y -> nat>
  constructor(f: Pack<Y -> nat>)
    ensures this.f == f
  {
    this.f := f;
  }
}

method Main()
  ensures false
{
  // error: x.f.c calls itself without decreasing
  var knot := new Y(Pack((x: Y) => 1 + x.f.c(x)));
  var a := knot.f.c(knot);
}