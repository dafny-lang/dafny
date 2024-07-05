// RUN: ! %run --target cs "%s" > "%t"
// RUN: ! %run --target go "%s" >> "%t"
// RUN: ! %run --target java "%s" >> "%t"
// RUN: ! %run --target js "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  expect 2 + 2 == 5, "Down with Doublethink!";
}
