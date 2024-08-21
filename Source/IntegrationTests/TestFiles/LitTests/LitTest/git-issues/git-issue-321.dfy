// RUN: %testDafnyForEachResolver --expect-exit-code=2 --refresh-exit-code=4 "%s"


method h(n: nat) {
  var a: array<nat> := new [n](i => i); // OK, element type inferred as "nat" (in legacy resolver, i is nat, which gives gives RHS as nat)
}

method k(n: nat) {
  var a: array := new [n]((i: nat) => i as nat); // OK
}

method p(n: nat) {
  var init: nat -> nat := i => i;
  var a: array := new [n](init); // OK
}

method q(n: nat) {
  var init: int -> int := i => i;
  var a: array<nat> := new [n](init); // ERROR with legacy resolver, which inferred RHS element type as "int"; new resolver infers "nat", so no error
  var b: array<nat> := new nat[n](init); // OK
  var c: array<nat> := new int[n](init); // ERROR (resolver error for old resolver; verifier error for new resolver)
}
