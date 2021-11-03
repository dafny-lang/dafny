// RUN: %dafny /compile:3 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:3 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /compile:3 /compileTarget:js "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype OOAgent = | OO7 {
  compiled function Talk(): bool {
    true
  }
  compiled function Die(): bool {
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
