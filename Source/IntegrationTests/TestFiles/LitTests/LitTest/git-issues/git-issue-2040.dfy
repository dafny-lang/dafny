// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"

class C {
  var x: int
}

datatype D = B(c: C)

predicate P(d: D)
  // the following line once caused a crash in the resolver
  reads B.c // error: wrong number of arguments to B
{
  d.c.x >= 0
}
