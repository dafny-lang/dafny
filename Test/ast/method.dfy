// RUN: %baredafny verify --use-basename-for-filename "%s" > "%t"
// RUN: ! %baredafny run --use-basename-for-filename "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Foo()
method {:axiom} Bar()
