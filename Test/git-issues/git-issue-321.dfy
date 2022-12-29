// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method h(n: nat) {
  var a: array<nat> := new [n](i => i); // OK - i is nat, RHS is array<nat>
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
  var a: array<nat> := new [n](init); // ERROR
  var b: array<nat> := new nat[n](init); // OK
}
