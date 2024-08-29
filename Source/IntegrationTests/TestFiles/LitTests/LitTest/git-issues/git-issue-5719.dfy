// RUN: %verify --type-system-refresh --general-traits=datatype "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait G {}

datatype D extends G = Dd

trait Thing<A, G1 extends G> {
  function Get(): (a: A)
    ensures P(a)

  predicate P(a: A) {
    Q(a)
  }

  predicate Q(a: A) 
}

method Test<A>(thing: Thing<A, D>) {
  var a := thing.Get();
  // assert thing.P(a); // this assertion was once needed to prove the next line
  assert thing.Q(a);
}
