// RUN: %testDafnyForEachResolver "%s"
// NONUNIFORM: warning will be the same for all back-end
// RUN: ! %run --allow-axioms:false "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Foo() {
 assume false;
 assume {:axiom} false;
 
 var xs := { 1, 2 };
 var x :| assume x in xs;

 var ys :- assume { 1 }; 
}