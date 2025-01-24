// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  export provides l
  lemma l() ensures true {}
}

module N {
  import M
  ghost function f(): nat { assert M.l(); 3 }
}

