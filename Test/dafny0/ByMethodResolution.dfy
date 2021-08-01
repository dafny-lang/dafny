// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Resolution {
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

module Export {
  module A {
    export
      provides F, G, H

    function F(): int {
      5
    }

    function method G(): int {
      5
    }

    function H(): int {
      5
    } by method {
      return 5;
    }
  }

  module B {
    import A
    method M() returns (ghost x: int, y: int) {
      x := A.F();
      x := A.G();
      x := A.H();
      y := A.F(); // error: F is ghost
      y := A.G();
      y := A.H();
    }
  }
}

module ByMethodGhostInterests {
  function Zero(): int { 0 }

  function F(x: nat): int {
    x + Zero()
  } by method {
    var j := 0;
    for i := 0 to x
      invariant i == -j
    {
      j := j - 1;
    }
    ghost var k := j;
    j := k; // error: cannot assign ghost to non-ghost
    return -j;
  }

  function G(ghost a: int, b: bool): real {
    0.0
  } by method {
    return if a == 3 then 3.0 else 0.0; // error: cannot use ghost in this context
  }

  method Caller() returns (x: int, r: real, ghost xx: int, ghost rr: real) {
    x := F(50);
    r := G(x, true);
    xx := F(50);
    rr := G(x, true);
  }
}
