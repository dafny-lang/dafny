// RUN: %exits-with 2 %baredafny resolve --show-snippets "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M() {
  assert [] == [[]];
}
