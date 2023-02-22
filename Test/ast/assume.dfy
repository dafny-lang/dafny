// RUN: %baredafny verify --allow-axiom:false --use-basename-for-filename "%s" > "%t"
// RUN: %baredafny run --allow-axiom:false --use-basename-for-filename "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Foo() {
 assume false;
 assume {:axiom} false;
 
 var xs := { 1, 2 };
 var x :| assume x in xs;
}