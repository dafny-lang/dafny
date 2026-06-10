// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"

// Regression tests: a recursive self-call in a function's specification used to
// allow proving false, because CanCallAssumption dropped the self-call allowance
// (cco) on some sub-expressions. Several surface forms hit the same root cause:
// - #6405: a match expression on a single-constructor datatype, which the
//   MatchFlattener lowers to a LetExpr.
// - #6343: a `var` expression, which is already a LetExpr.
// - a revealed `const` field whose definition is inlined when the field is
//   selected on the result of a self-call (MemberSelectExpr / ConstantField).

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

datatype Wrapper = Wrap(val: int) {
  const c: int := this.val
}

// Const field selected on the result of a self-call must not let `false` be proved.
function constField(n: int): Wrapper
  ensures constField(n).c == 0
  ensures false
{ Wrap(0) }

// Legitimate const-field selection on a self-call still verifies.
function constFieldOk(n: int): Wrapper
  ensures constFieldOk(n).c == 0
{ Wrap(0) }
