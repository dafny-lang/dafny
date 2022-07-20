// RUN: %dafny /compile:3 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:3 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /compile:3 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /compile:3 /compileTarget:py "%s" >> "%t"
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
