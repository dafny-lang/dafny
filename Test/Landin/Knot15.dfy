// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


class Y {
  const f: YWithConstraint -> nat
  constructor(f: YWithConstraint -> nat)
    ensures this.f == f
  {
    this.f := f;
  }
}

type YWithConstraint = y: Y | true witness *

method Main()
  ensures false
{
  // error: knot.f calls itself without decreasing
  var knot := new Y((x: YWithConstraint) => 1 + x.f(x));
  var a := knot.f(knot);
}