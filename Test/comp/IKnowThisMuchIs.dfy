// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:py "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"

// RUN: %diff "%s.expect" "%t"

//
// An extremely small program intended to be the first target input for
// brand new Dafny compilers. Avoids any use of strings (and therefore sequences)
// but requires representing booleans at runtime and the bare minimum support for
// the print statement.
//
// This program also serves the purpose of ensuring that new compiler authors
// immediately have Spandau Ballet stuck in their head. :)
//
method Main() {
  print true;
}