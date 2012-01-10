module A {
  class X { }
  class T {
    method M(x: int) returns (y: int)
      requires 0 <= x;
      ensures 0 <= y;
    {
      y := 2 * x;
    }
    method Q() returns (q: int, r: int, s: int)
      ensures 0 <= q && 0 <= r && 0 <= s;
    {  // error: failure to establish postcondition about q
      r, s := 100, 200;
    }
  }
}

module B refines A {
  class C { }
  datatype Dt = Ax | Bx;
  class T {
    method P() returns (p: int)
    {
      p := 18;
    }
    method M(x: int) returns (y: int)
      ensures y % 2 == 0;  // add a postcondition
    method Q() returns (q: int, r: int, s: int)
      ensures 12 <= r;
      ensures 1200 <= s;  // error: postcondition is not established by
                          // inherited method body
  }
}
