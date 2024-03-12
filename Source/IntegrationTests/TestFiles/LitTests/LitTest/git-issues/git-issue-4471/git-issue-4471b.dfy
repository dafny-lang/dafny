// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait YT<W> {
  const f: W
}

class Y extends YT<Y -> nat> {
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
  var arrow := (x: Y) => 1 + x.f(x);
  var knot := new Y(arrow);
  var a := knot.f(knot);
}