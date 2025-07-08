// RUN: %exits-with 2 %baredafny resolve --use-basename-for-filename --show-snippets --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M() {
  assert [] == [[]];
}
