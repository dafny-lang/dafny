// RUN: %dafny /verifyAllModules /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../../docs/DafnyRef/examples/Example-TwoState-Increasing.dfy"
include "../../docs/DafnyRef/examples/Example-TwoState-Caller.dfy"
include "../../docs/DafnyRef/examples/Example-TwoState-Diff.dfy"
include "../../docs/DafnyRef/examples/Example-TwoState-DiffAgain.dfy"
include "../../docs/DafnyRef/examples/Example-TwoState-SeqSum.dfy"
include "../../docs/DafnyRef/examples/Example-TwoState-EtaExample.dfy"

class Cell {
  var data: int
  constructor (x: int)
    ensures data == x
  {
    data := x;
  }
}
