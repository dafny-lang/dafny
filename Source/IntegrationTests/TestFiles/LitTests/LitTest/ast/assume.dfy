// RUN: %verify --allow-axioms:false "%s" > "%t"
// RUN: %run --allow-axioms:false "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Foo() {
 assume false;
 assume {:axiom} false;
 
 var xs := { 1, 2 };
 var x :| assume x in xs;
}