// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  export provides l
  lemma l() ensures true {}
}

module N {
  import M
  function f(): nat { assert M.l(); 3 }
}

