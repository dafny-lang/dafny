// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Y {
  const f: Y? -> nat
  constructor(f: Y? -> nat)
    ensures this.f == f
  {
    this.f := f;
  }
}

method Main()
  ensures false
{
  // error: knot.f calls itself without decreasing
  var knot := new Y((x: Y?) => if x == null then 0 else 1 + x.f(x));
  var a := knot.f(knot);
}