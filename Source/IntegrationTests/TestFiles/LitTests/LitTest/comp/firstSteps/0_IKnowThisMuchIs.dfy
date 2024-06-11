// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment
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
