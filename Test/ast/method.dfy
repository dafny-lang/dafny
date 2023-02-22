// RUN: %baredafny verify --allow-axioms:false --use-basename-for-filename "%s" > "%t"
// RUN: ! %baredafny run --allow-axioms:false --use-basename-for-filename "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Foo() ensures false; ensures false;
method {:axiom} Bar() ensures false;
