class C {
  function F(c: C, d: D): bool { true }
  method M(x: int) returns (y: int, c: C)
    requires F(D.A, this);  // 2 errors
    requires F(4, 5);  // 2 errors
    requires F(this, D.A);  // good
  { }

  method Caller()
  {
    var m,n := M(true);  // error on in-parameter
    n,m := M(m);  // 2 errors on out-parameters
  }
}

datatype D = A;

datatype NeverendingList = Cons(int, NeverendingList);  // error: no grounding constructor

datatype MutuallyRecursiveDataType<T> =
  FromANumber(int) |  // this is the base case
  Else(TheCounterpart<T>, C);

datatype TheCounterpart<T> =
  TreeLike(TheCounterpart<T>, TheCounterpart<T>) |
  More(MutuallyRecursiveDataType<T>);

// these 'ReverseOrder_' order tests may be called white-box unit tests
datatype ReverseOrder_MutuallyRecursiveDataType<T> =
  FromANumber(int) |  // this is the base case
  Else(ReverseOrder_TheCounterpart<T>, C);

datatype ReverseOrder_TheCounterpart<T> =
  TreeLike(ReverseOrder_TheCounterpart<T>, ReverseOrder_TheCounterpart<T>) |
  More(ReverseOrder_MutuallyRecursiveDataType<T>);

// ---------------------

class ArrayTests {
  ghost method G(a: array<int>)
    requires a != null && 10 <= a.Length;
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

// ---------------------

method InitCalls() {
  var c := new C.F(null, null);  // error: F is not a method
  var d := new C.M(8);  // error: M has out parameters
  var e := new C.Caller();
}

// ---------------------

method ArrayRangeAssignments(a: array<C>, c: C)
  requires a != null && 10 <= a.Length;
{
  a[0..5] := new C;  // error: this is not allowed
  a[1..4] := *;  // error: this is not allowed
  a[2..3] := c;  // error: this is not allowed
  var s: seq<C> := [null,null,null,null,null];
  s[0..5] := new C;  // error: this is not allowed
  s[1..4] := *;  // error: this is not allowed
  s[2..3] := c;  // error: this is not allowed
}

// --------------------- tests of restrictions on subranges (nat)

method K() {
  var s: set<nat>;  // error: not allowed to instantiate 'set' with 'nat'
  var d: MutuallyRecursiveDataType<nat>;  // error: not allowed to instantiate with 'nat'
  var a := new nat[100];  // error: not allowed the type array<nat>
  var b := new nat[100,200];  // error: not allowed the type array2<nat>
}

// --------------------- more ghost tests, for assign-such-that statements

method M()
{
  ghost var b: bool;
  ghost var k: int, l: int;
  var m: int;

  // These three statements are allowed by the resolver, but the compiler will complain
  // if it ever gets them.
  k :| k < 10;
  k, m :| 0 <= k < m;
  m :| m < 10;

  // Because of the ghost guard, these 'if' statements are ghost contexts, so only
  // assignments to ghosts are allowed.
  if (b) {
    k :| k < 10;  // should be allowed
    k, l :| 0 <= k < l;  // ditto
  }
  if (b) {
    m :| m < 10;  // error: not allowed in ghost context
    k, m :| 0 <= k < m;  // error: not allowed in ghost context
  }
}
