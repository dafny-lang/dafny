// RUN: %exits-with 2 %verify --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  export provides l
  lemma l() ensures true {}
}

module N {
  import M
  ghost function f(): nat { assert M.l(); 3 }
}

