// RUN: %baredafny verify %args --warn-shadowing --warnings-as-errors %s > "%t" || true
// RUN: %diff "%s.expect" "%t"
method f(x: int) {
  var x := 0;
}
