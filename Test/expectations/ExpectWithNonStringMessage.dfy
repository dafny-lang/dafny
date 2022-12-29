// RUN: %baredafny verify %args "%s" > "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Option<T> = None | Some(get: T)

method Main() {
  var x := Some("where over the rainbow");
  expect x.None?, x;
}
