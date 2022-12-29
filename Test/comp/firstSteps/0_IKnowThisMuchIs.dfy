// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
//
// An extremely small program intended to be the first target input for
// brand new Dafny compilers. Avoids any use of strings (and therefore sequences)
// but requires representing booleans at runtime and the bare minimum support for
// the print statement.
//
// This program also serves the purpose of ensuring that new compiler authors
// immediately have Spandau Ballet stuck in their head. :)

method Main() {
  print true;
}
