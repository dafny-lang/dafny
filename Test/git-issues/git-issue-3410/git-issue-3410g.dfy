// RUN: %exits-with 2 %baredafny resolve --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method m() {
  assert {:expect "",""} true;
  assert {:expect 10} true;
}
