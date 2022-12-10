// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
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

