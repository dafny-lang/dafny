// RUN: %build --warn-shadowing --allow-warnings "%s" > "%t"
// RUN: %build --warn-shadowing --warn-as-errors=false "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
method f(x: int) {
  var x := 0;
}
