module A {
  class C {
    method M(y: int) returns (x: int)
    {
      x := 6;
    }
  }
}

module B refines A {
  class C {
    var k: int;
    method M(y: int) returns (x: int)
      requires 0 <= y;  // error: cannot add a precondition
      modifies this;  // error: cannot add a modifies clause
      ensures 0 <= x;  // fine
  }
}
