// RUN: %exits-with 4 %baredafny verify %args --error-limit=0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
method m(x: int) {
  if x == 1 {
    assert x != 1;
  } else if x == 2 {
    assert x != 2;
  } else if x == 3 {
    assert x != 3;
  } else if x == 4 {
    assert x != 4;
  } else if x == 5 {
    assert x != 5;
  } else if x == 6 {
    assert x != 6;
  }
}
