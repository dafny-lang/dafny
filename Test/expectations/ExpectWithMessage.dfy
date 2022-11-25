// RUN: %dafny /compile:3 /compileTarget:cs "%s" > "%t" || true
// RUN: %dafny /compile:3 /compileTarget:go "%s" >> "%t" || true
// RUN: %dafny /compile:3 /compileTarget:java "%s" >> "%t" || true
// RUN: %dafny /compile:3 /compileTarget:js "%s" >> "%t" || true
// RUN: %diff "%s.expect" "%t"

method Main() {
  expect 2 + 2 == 5, "Down with Doublethink!";
}
