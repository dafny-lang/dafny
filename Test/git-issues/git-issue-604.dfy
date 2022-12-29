// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Inv() returns (x: int) {
  x := 0;
  while x < 100
    invariant 0 <= x <= 100
  assert x == 25;
  return x;
}

method InvB() returns (x: int) {
  x := 0;
  while x < 100
    invariant 0 <= x <= 100
    decreases 100 - x
    {
      x := x + 1;
    }
  assert x == 25;
  return x;
}

