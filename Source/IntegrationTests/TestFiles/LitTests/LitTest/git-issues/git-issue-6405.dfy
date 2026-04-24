// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"

// Regression test: a match expression on a single-constructor datatype in an
// ensures clause used to allow proving false, because CanCallAssumption for
// the let-expression body did not propagate the self-call allowance (cco).

datatype D = Pair(x: int, y: int)

function f(): D
  ensures match f() {case Pair(a, b) => a >= 0}
  ensures false
{ Pair(0, 0) }

// Also test that legitimate uses still verify:
function g(): D
  ensures match g() {case Pair(a, b) => a >= 0}
{ Pair(0, 0) }
