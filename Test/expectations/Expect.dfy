// RUN: ! %run --target=cs "%s" > "%t"
// RUN: ! %run --target=go "%s" >> "%t"
// RUN: ! %run --target=java "%s" >> "%t"
// RUN: ! %run --target=js "%s" >> "%t"
// RUN: ! %run --target=py "%s" >> "%t"
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
