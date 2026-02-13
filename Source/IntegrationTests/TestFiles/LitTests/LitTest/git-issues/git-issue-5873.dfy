// RUN: %verify --type-system-refresh --general-traits=datatype --bprint "%t.bpl" "%s"
// RUN: %boogie "%t.bpl" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Parent {
  method M() returns (r: nat)
  function F(): nat
}

datatype Dt<K(!new)> extends Parent = Dt {
  method M() returns (r: nat) {
    r := 0;
  }

  // The type parameter with (!new) once caused function override checks, like the one for this
  // function, to generate malformed Boogie.
  function F(): nat {
    0
  }
}
