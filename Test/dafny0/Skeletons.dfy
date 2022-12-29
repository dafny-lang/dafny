// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  method M(p: int) returns (y: int)
    requires p <= 30;
  {
    assume p < 100;
    var x;
    assume x == p + 20;
    x := x + 1;
    while (*)
      invariant x <= 120;
      decreases 120 - x;
    {
      if (x == 120) { break; }
      x := x + 1;
    }
    y := x;
  }
}

module B refines A {
  method M ...
  {
    assert p < 50;
    assert ...;
    var x := p + 20;
    assert ...;
    var k := x + 1;
    ...;
    while ...
      invariant k == x;
    {
      k := k + 1;
    }
    assert k == x || k == x + 1;  // there are two exits from the loop
  }
}


module C0 refines B {
  method M ...
    ensures y == 120;  // error: this holds only if the loop does not end early
  {
  }
}

module C1 refines B {
  method M ...
    ensures y <= 120;
  {
  }
}

module C2 refines B {
  method M ...
    ensures y == 120;
  {
    ...;
    while (true)
      ...
    assert k == x + 1;  // only one loop exit remains
    ...;
  }
}
