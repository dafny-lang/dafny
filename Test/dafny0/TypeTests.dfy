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

datatype Nothing {  // error: no grounding constructor
}

datatype NeverendingList {  // error: no grounding constructor
  Cons(int, NeverendingList);
}

datatype MutuallyRecursiveDataType<T> {
  FromANumber(int);  // this is the base case
  Else(TheCounterpart<T>, C);
}

datatype TheCounterpart<T> {
  TreeLike(TheCounterpart<T>, TheCounterpart<T>);
  More(MutuallyRecursiveDataType<T>);
}

// these 'ReverseOrder_' order tests may be called white-box unit tests
datatype ReverseOrder_MutuallyRecursiveDataType<T> {
  FromANumber(int);  // this is the base case
  Else(ReverseOrder_TheCounterpart<T>, C);
}

datatype ReverseOrder_TheCounterpart<T> {
  TreeLike(ReverseOrder_TheCounterpart<T>, ReverseOrder_TheCounterpart<T>);
  More(ReverseOrder_MutuallyRecursiveDataType<T>);
}

