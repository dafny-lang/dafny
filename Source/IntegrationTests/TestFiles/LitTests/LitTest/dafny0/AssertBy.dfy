// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s" -- --print:-


method M0(x: int, y: int)
{
  assert x == 6;  // error
  assert y == 8;  // error
}

method M1(x: int, y: int)
{
  assert x == 6 by {
    assume x == 6;  // that was easy
    assume y == 8;  // hey, why not assume some more while we're at it
  }
  assert y == 8;  // error (yes, still -- the previous assumption should not be in effect here)
}
