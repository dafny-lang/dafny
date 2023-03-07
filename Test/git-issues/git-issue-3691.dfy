// RUN: %exits-with 0 %dafny /compile:0 /allocated:4 /functionSyntax:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait A {
  predicate f()
  method g() ensures f()
}

class B<T> extends A {
  predicate f() { true }
  method g() ensures f()
}
