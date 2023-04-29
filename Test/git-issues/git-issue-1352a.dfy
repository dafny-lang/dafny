// RUN: %exits-with 2 %baredafny resolve --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost method g() {}

method m() {
  var v := (m(); 0);
}
