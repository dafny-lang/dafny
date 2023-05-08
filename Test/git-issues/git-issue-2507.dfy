// RUN: %exits-with 2 %baredafny resolve --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Test(i: int) {
  assert i >= 0
  var j := 2;
}
