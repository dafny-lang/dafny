// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method test() returns (a: bool, b: int) {
  return (true, 0);
}
