// RUN: %verify --allow-axioms:false "%s" > "%t"
// NONUNIFORM: warning will be the same for all back-end
// RUN: ! %run --allow-axioms:false "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Foo() ensures false ensures false
method {:axiom} Bar() ensures false

method BodylessLoop() ensures false {
  while(true) invariant true || false
}
