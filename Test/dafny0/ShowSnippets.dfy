// RUN: %dafny /compile:0 /showSnippets "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Never() requires true && false {}

method Test1() {
  assert false;
}

method Test2() {
  Never();
}
