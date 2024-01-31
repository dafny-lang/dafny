// RUN: %exits-with 2 %resolve --warn-shadowing --warn-as-errors "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
method f(x: int) {
  var x := 0;
}
