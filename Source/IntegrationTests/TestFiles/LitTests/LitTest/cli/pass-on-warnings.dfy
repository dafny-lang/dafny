// RUN: %build --warn-shadowing --succeed-on-warnings "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
method f(x: int) {
  var x := 0;
}
