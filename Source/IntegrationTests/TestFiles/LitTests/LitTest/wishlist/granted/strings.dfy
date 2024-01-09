// RUN: %testDafnyForEachResolver "%s"


method EqualityOfStrings() {
  assert "a" != "b"; // WISH -- granted
}
