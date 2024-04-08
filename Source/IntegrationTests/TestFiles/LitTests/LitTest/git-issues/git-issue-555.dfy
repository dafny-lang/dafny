// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: ! %run --no-verify --target cs "%s" >> "%t"
// RUN: ! %run --no-verify --target js "%s" >> "%t"
// RUN: ! %run --no-verify --target go "%s" >> "%t"
// RUN: ! %run --no-verify --target java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"


method Main() {
  g(10);
  g(-10);
  f(10);
  f(-10);
}

method f(i: int) {
  assert i > 0;
  expect i > 0;
}

method g(i: int) {
  expect i > 0; // assumes i > 0
  assert i > 0;
}

