// RUN: ! %baredafny run --use-basename-for-filename --cores:2 --verification-time-limit:300 --target=cs "%s" > "%t"
// RUN: ! %baredafny run --use-basename-for-filename --cores:2 --verification-time-limit:300 --target=go "%s" >> "%t"
// RUN: ! %baredafny run --use-basename-for-filename --cores:2 --verification-time-limit:300 --target=java "%s" >> "%t"
// RUN: ! %baredafny run --use-basename-for-filename --cores:2 --verification-time-limit:300 --target=js "%s" >> "%t"
// RUN: ! %baredafny run --use-basename-for-filename --cores:2 --verification-time-limit:300 --target=py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype OOAgent = | OO7 {
  function method Talk(): bool {
    true
  }
  function method Die(): bool {
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
