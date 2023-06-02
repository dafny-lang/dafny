// RUN: %baredafny build --use-basename-for-filename "%s" > "%t"
// RUN: %exits-with 4 %baredafny build --use-basename-for-filename --enforce-determinism "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method m() {
  var a: array<int>;
  a := new int[10];
}
