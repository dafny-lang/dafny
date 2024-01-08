// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method m() {
  var f := st => set x | x in st;
}
