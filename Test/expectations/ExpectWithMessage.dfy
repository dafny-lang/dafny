// RUN: ! %baredafny run %args --target=cs "%s" > "%t"
// RUN: ! %baredafny run %args --target=go "%s" >> "%t"
// RUN: ! %baredafny run %args --target=java "%s" >> "%t"
// RUN: ! %baredafny run %args --target=js "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  expect 2 + 2 == 5, "Down with Doublethink!";
}
