// RUN: %exits-with 4 %baredafny verify %args --error-limit=2 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
method m(x: int) {
  if x == 1 {
    assert x != 1;
  } else if x == 2 {
    assert x != 2;
  } else if x == 3 {
    assert x != 3;
  }
}
