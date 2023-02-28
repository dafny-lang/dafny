// RUN: ! %baredafny run %args --target=cs "%s" > "%t"
// RUN: ! %baredafny run %args --target=go "%s" >> "%t"
// RUN: ! %baredafny run %args --target=java "%s" >> "%t"
// RUN: ! %baredafny run %args --target=js "%s" >> "%t"
// RUN: ! %baredafny run %args --target=py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype OOAgent = | OO7 {
  function Talk(): bool {
    true
  }
  function Die(): bool {
    false
  }
}

method TestExpect() {
  var jamesBond := OO7;
  // Do you...
  expect jamesBond.Talk();
  // No Mr. Bond, I...
  expect jamesBond.Die(); // Runtime error: expectation violation
}

method Main() {
  TestExpect();
}
