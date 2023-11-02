// RUN: %testDafnyForEachResolver "%s"


include "ExportRefinement.dfy"

module Z {
  lemma Test()
  ensures 1 < 2 // this should be the only verification condition produced, plus one top-level one from ExportRefinement
  {
  }
}
