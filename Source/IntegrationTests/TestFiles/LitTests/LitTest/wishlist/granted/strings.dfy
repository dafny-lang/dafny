// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method EqualityOfStrings() {
  assert "a" != "b"; // WISH -- granted
}
