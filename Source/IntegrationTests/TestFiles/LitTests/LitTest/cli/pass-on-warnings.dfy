// RUN: %build --warn-shadowing --pass-on-warnings "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
method f(x: int) {
  var x := 0;
}
