// RUN: %baredafny test %args "%s" >> "%t"
method {:test} Passing1() {
  expect 2 == 2;
}
