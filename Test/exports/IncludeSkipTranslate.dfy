// RUN: %dafny /env:0 /dprint:"%t.dfy" /compile:0 "%s" > "%t.result"
// RUN: %diff "%s.expect" "%t.result"

include "ExportRefinement.dfy"

module Z {
  lemma Test() 
  ensures 1 < 2 // this should be the only verification condition produced, plus one top-level one from ExportRefinement
  {
  }
}
