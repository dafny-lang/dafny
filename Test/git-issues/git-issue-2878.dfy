// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method test() returns (a: bool, b: int) {
  return (true, 0);
}