// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


trait T<U> {
  const f: U -> nat // Type error here? because since Y can be accessed, -> should be ~>
}

class Y extends T<Y> {
  constructor(f: Y -> nat)
    ensures this.f == f
  {
    this.f := f;
  }
}

method Main()
  ensures false
{
  // error: x.f calls itself without decreasing
  var knot := new Y((x: Y) => 1 + x.f(x)); // Why doesn't it have a reads clause? Because f can pretend that it does not
  var a := knot.f(knot);
}