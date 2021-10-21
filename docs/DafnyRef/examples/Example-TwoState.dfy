
// This file only exists to include these examples as a test case.

include "Example-TwoState-Increasing.dfy"
include "Example-TwoState-Caller.dfy"
include "Example-TwoState-Diff.dfy"
include "Example-TwoState-DiffAgain.dfy"
include "Example-TwoState-SeqSum.dfy"
include "Example-TwoState-EtaExample.dfy"

class Cell {
  var data: int
  constructor (x: int)
    ensures data == x
  {
    data := x;
  }
}
