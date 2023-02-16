// RUN: %baredafny verify %args "%s" > "%t"
// RUN: ! %baredafny run %args "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Foo()
method {:axiom} Bar()