// RUN: %verify --unicode-char false "%s" > "%t"
// RUN: ! %dafny /noVerify /compile:4 --unicode-char false /compileTarget:cs "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 --unicode-char false /compileTarget:go "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 --unicode-char false /compileTarget:java "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 --unicode-char false /compileTarget:js "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 --unicode-char false /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Option<T> = None | Some(get: T)

method Main() {
  var x := Some("where over the rainbow");
  expect x.None?, x;
}
