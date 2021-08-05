// RUN: %dafny /dprint:- /env:0 /noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  method M()
}

module B refines A {
  method M ... {
    while true
    while true
      invariant true
      invariant true
    while true
      decreases 5
    while true
      modifies {}
    while ...
    while true
      ...
    while true {
      var u := 0;
    }
    var x := 10;
  }

  method P(a: array<int>)
    modifies a
  {
    forall i | 0 <= i < 100 {
      a[i] := 200;
    }
    forall i | 0 <= i < 100
      ensures true
    forall i | 0 <= i < 100
      ensures true
    {
    }
  }
}

module C {
  method For() {
    ghost var (x, y) := (123, 234);
    var a := new int[100];
    for i := 0 to 100 {
      a[i] := i;
    }
    for i := 100 downto 0 {
      a[i] := i;
    }
    for i: nat := 0 to 100
    for i: nat := 100 downto 0
    for i := 0 to 100
      invariant a[5] == 5
      invariant a[12] == 12
    for i := 100 downto 0
      invariant a[5] == 5
    for i := 0 to 100
      invariant a[5] == 5
      invariant a[12] == 12
    {
    }
    for i := 100 downto 0
      invariant a[5] == 5
    {
      assert true;
    }
    for i := 0 to *
      decreases 100 - i
      invariant i <= 100
    for i := 0 to *
      decreases *
    {
    }
    var c := new Cell;
    for i := 0 to 100
      modifies c
      modifies {c}, {c}
    {
    }
    for i := 100 downto *
      modifies c
      decreases i
      modifies {c}, {c}
      invariant -68 <= i <= 68
      invariant i != 3
    {
    }
  }
  class Cell { var data: int }
}

module Ats {
  class Cell {
    var data: int

    method M()
    {
      label Label:
      assert old(data) == old@Label(data);
      assert unchanged(this) && unchanged@Label(this);
      var c := new Cell;
      assert fresh(c) && fresh@Label(c);
    }
  }
}
