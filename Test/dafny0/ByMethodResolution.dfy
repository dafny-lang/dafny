// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module ByMethodResolution {
  function F(x: nat): int {
    x
  } by method {
    var j := 0;
    for i := 0 to x
      invariant i == -j
    {
      j := j - 1;
    }
    if * {
      return;
    } else {
      return -j, 3; // error: wrong number of out-parameters
    }
  }
  function G(ghost a: int, b: bool): (r: real) {
    0.0
  } by method {
    r := 1.8;
    r := 18; // error: cannot assign int to real
    return 3 as bv9; // error: wrong result type
  }
}
