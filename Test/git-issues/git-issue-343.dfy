// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method f(a: seq<int>) {
  var t := a[a .. 1];
}
