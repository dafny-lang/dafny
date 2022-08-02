// RUN: %baredafny run /compileTarget:cs %args "%s" > "%t"
// RUN: %baredafny run /compileTarget:go %args "%s" >> "%t"
// RUN: %baredafny run /compileTarget:java %args "%s" >> "%t"
// RUN: %baredafny run /compileTarget:js %args "%s" >> "%t"
// RUN: %baredafny run /compileTarget:py %args "%s" >> "%t"
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
