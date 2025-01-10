// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


class Y {
  const f: Y -> nat // Type error here? because since Y can be accessed, -> should be ~>
  constructor(f: Y -> nat)
    ensures this.f == f
  {
    this.f := f;
  }
}

method Main()
  ensures false
{
  // error: knot.f calls itself without decreasing
  var knot := new Y((x: Y) => 1 + x.f(x)); // Why doesn't it have a reads clause? Because f can pretend that it does not
  var a := knot.f(knot);
}