// RUN: %exits-with 4 %baredafny verify --use-basename-for-filename --show-snippets "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method m() {
  assert false;
}
