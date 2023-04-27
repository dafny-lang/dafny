// RUN: %exits-with 2 %dafny "%s" > "%t"
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
      provides F, FP, F2, G, H

    ghost function F(): int {
      5
    }

    ghost predicate FP() {
      true
    }

    twostate function F2(): int {
      5
    }

    function G(): int {
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
    method M() returns (ghost x: int, y: int, b: bool) {
      x := A.F();
      x := A.G();
      x := A.H();
      y := A.F(); // error: F is ghost
      b := A.FP(); // error: FP is ghost
      y := A.F2(); // error: F2 is ghost
      y := A.G();
      y := A.H();
    }
  }
}

module ByMethodGhostInterests {
  ghost function Zero(): int { 0 }

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

module BadExtremeRecursion {
  // P and F are not allowed in the same recursive cluster
  least predicate P() {
    F() == 5 // error: this call is illegal
  }
  function F(): int {
    if P() then 5 else 3
  } by method {
    return 5;
  }

  // no problem with Q and G
  least predicate Q() {
    G() == 5
  }
  function G(): int {
    5
  } by method {
    ghost var u := Q();
    return 5;
  }

  // no problem with R0/H0'/H0
  least predicate R0() {
    H0'() == 5
  }
  ghost function H0'(): int {
    if H0() < 100 then 5 else 3 // in a ghost context, this calls the function part of H0
  }
  function H0(): int {
    5
  } by method {
    var x := H0'();
    var y := R0();
    return 5;
  }

  // R1/H1'/H1 are mutually recursive
  least predicate R1() {
    H1'() == 5 // error: R1 is in same recursive cluster as H1
  }
  function H1'(): int {
    if H1() < 100 then 5 else 3 // in a compiled context, this calls the method part of H1
  }
  function H1(): int {
    5
  } by method {
    var x :=  H1'();
    var y := R1();
    return 5;
  }

  // R2/H2'/H2 are mutually recursive
  least predicate R2() {
    H2'() == 5 // error: R2 is in same recursive cluster as H2
  }
  function H2'(): int {
    if H2() < 100 then 5 else 3 // in a compiled context, this calls the method part of H2
  }
  function H2(): int {
    if R2() then 5 else 3
  } by method { // the method part uses the function part in its specification, so there's a call-graph edge
    return 5;
  }
}
