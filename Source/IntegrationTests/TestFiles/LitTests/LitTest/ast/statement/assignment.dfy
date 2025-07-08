// RUN: %verify %s &> "%t"
// RUN: %diff "%s.expect" "%t"

method ByWellformedness(x: int) {
  var p: int := 3 / x by {
    assume {:axiom} x > 0;
  }
}