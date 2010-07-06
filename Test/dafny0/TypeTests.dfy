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

// ---------------------

class ArrayTests {
  ghost method G(a: array<int>)
    requires a != null && 10 <= |a|;
    modifies a;
  {
    a[7] := 13;  // error: array elements are not ghost locations
  }
}

// ---------------------

method DuplicateVarName(x: int) returns (y: int)
{
  var z: int;
  var z: int;  // error: redeclaration of local
  var x := x;  // redeclaration of in-parameter is fine
  var x := x;  // error: but a redeclaration of that local is not fine
  {
    var x := x;  // an inner local variable of the same name is fine
    var x := x;  // error: but a redeclaration thereof is not okay
    var y := y;  // duplicating an out-parameter here is fine
  }
  var y := y;  // error: redeclaration of an out-parameter is not allowed (it is
               // treated like an outermost-scoped local in this regard)
}
