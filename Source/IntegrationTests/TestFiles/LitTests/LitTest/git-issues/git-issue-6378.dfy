// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"

// Regression test: refined modules with assign-such-that statements caused
// crashes because (1) FunctionCallExpr.SubExpressions accessed Args which is
// null pre-resolution, and (2) the new resolver asserted FunctionCallExpr
// never appears directly, but it does in cloned {:trigger} attributes.

abstract module A {
  predicate P(x: int)
  method M() {
    var x :| P(x);
  }
}
module B refines A {
  predicate P(x: int) { x > 0 }
}
