// RUN: ! %verify --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class CK {
  var x: int
  var y: int
  constructor Init() {
    x := 10;
  } // definite-assignment rules allow fields to be left unassigned [error: determinism]
}

method ArrayAllocation(n: nat, p: nat, q: nat)
{
  var a := new int[n]; // definite-assignment rules allow array elements to be left unassigned [error: determinism]
  var m := new bool[p,q]; // definite-assignment rules allow array elements to be left unassigned [error: determinism]
}

class Cell {
  var data: int

  constructor () {
    // .data is auto-initialized here
  } // [error: determinism]
}
