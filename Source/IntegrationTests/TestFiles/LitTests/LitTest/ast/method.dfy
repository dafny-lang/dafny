// RUN: %verify --allow-axioms:false "%s" > "%t"
// RUN: ! %run --allow-axioms:false "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Foo() ensures false ensures false
method {:axiom} Bar() ensures false
