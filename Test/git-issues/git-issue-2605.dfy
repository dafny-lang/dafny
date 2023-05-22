// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M(a: array<int>, j: int) {
  forall n | 0 <= n < 100
    ensures n / 0 == n / 0 // error (x2): division by zero
    ensures a[j] == a[j] // error (x2): array index out of bounds    
  {
    assert false; // error
  }
  assert false; // error
}
