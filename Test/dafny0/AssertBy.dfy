// RUN: %exits-with 4 %dafny /env:0 /dprint:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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
