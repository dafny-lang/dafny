// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"

// Regression tests: a let-expression body in an ensures clause used to allow
// proving false, because CanCallAssumption for the let-expression body did
// not propagate the self-call allowance (cco). Two surface forms hit the
// same root cause:
// - #6405: a match expression on a single-constructor datatype, which the
//   MatchFlattener lowers to a LetExpr.
// - #6343: a `var` expression, which is already a LetExpr.

datatype D = Pair(x: int, y: int)

function f(): D
  ensures match f() {case Pair(a, b) => a >= 0}
  ensures false
{ Pair(0, 0) }

// Also test that legitimate uses still verify:
function g(): D
  ensures match g() {case Pair(a, b) => a >= 0}
{ Pair(0, 0) }

// #6343: `var` in ensures with a recursive self-call.
function h(elements: int): (r: int)
  ensures var i := 1; h(elements) == 0
{ 1 }

// Legitimate `var` in ensures:
function k(elements: int): (r: int)
  ensures var i := 1; r >= i - 1
{ 1 }
