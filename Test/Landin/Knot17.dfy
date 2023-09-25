// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


trait YT {
  const f: YT -> nat
}

class Y extends YT {
  constructor(f: YT -> nat)
    ensures this.f == f
  {
    this.f := f;
  }
}

method Main()
  ensures false
{
  // error: knot.f calls itself without decreasing
  var knot := new Y((x: YT) => if x is Y then 1 + x.f(x as Y) else 0);
  var a := knot.f(knot);
}