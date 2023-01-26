// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Test(f: int -> int) {
  assert seq(1, x => f(x))[0] == f(0);  // No problem
  assert seq(1, f)[0] == f(0);  // Error: assertion might not hold
}