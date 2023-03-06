// RUN: %exits-with 0 %dafny /compile:0 /allocated:4 /functionSyntax:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait A {
  predicate f()
  method g() ensures f()     // Line 3
}

class B<T> extends A {       // Line 6
  predicate f() { true }     // Line 7
  method g() ensures f()
}

