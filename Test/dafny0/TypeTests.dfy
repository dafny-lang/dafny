class C {
  function F(c: C, d: D): bool { true }
  method M(x: int) returns (y: int, c: C)
    requires F(#D.A, this);  // 2 errors
    requires F(4, 5);  // 2 errors
    requires F(this, #D.A);  // good
  { }

  method Caller()
  {
    call m,n := M(true);  // error on in-parameter
    call n,m := M(m);  // 2 errors on out-parameters
  }
}

datatype D {
  A;
}
