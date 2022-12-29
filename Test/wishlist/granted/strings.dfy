// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method EqualityOfStrings() {
  assert "a" != "b"; // WISH -- granted
}
