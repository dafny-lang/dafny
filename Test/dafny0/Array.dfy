class A {
  method M() {
    var y := new A[100];
    y[5] := null;
  }

  method N0() {
    var a: array<int>;
    if (a != null && 5 < a.Length) {
      a[5] := 12;  // error: violates modifies clause
    }
  }

  method N1(a: array<int>)
    modifies a;
  {
    var b := a.Length;  // error: a may be null
  }

  method N2(a: array<int>)
    requires a != null;
    modifies a;
  {
    a[5] := 12;  // error: index may be outside bounds
  }

  method N3(a: array<int>)
    requires a != null && 5 < a.Length;
    modifies a;
    ensures (forall i :: 0 <= i && i < a.Length ==> a[i] == old(a[i]) || (i == 5 && a[i] == 12));
  {
    a[5] := 12;  // all is good
  }

  var zz0: array<A>;
  var zz1: array<B>;
  method O() {
    var zz2 := new A[25];
    assert zz2 != zz0;  // holds because zz2 is newly allocated
    var o: object := zz0;
    assert this != o;  // holds because zz0 has a different type
    /******  This would be a good thing to be able to verify, but the current encoding is not up to the task
    if (zz0 != null && zz1 != null && 2 <= zz0.Length && zz0.Length == zz1.Length) {
      o := zz1[1];
      assert zz0[1] == o ==> o == null;  // holds because zz0 and zz1 have different element types
    }
    ******/
    assert zz2[20] == null;  // error: no reason that this must hold
  }

  var x: array<int>;
  method P0()
    modifies this;
  {
    if (x != null && 100 <= x.Length) {
      x[5] := 12;  // error: violates modifies clause
    }
  }
  method P1()
    modifies this`x;
  {
    if (x != null && 100 <= x.Length) {
      x[5] := 12;  // error: violates modifies clause
    }
  }
  method P2()
    modifies x;
  {
    if (x != null && 100 <= x.Length) {
      x[5] := 12;  // fine
    }
  }

  method Q() {
    var a := new int[5];
    a[0],a[1],a[2],a[3],a[4] := 0,1,2,3,4;
	
	assert [1,2,3,4] == a[1..];
	assert [1,2,3,4] == a[1.. a.Length];
	assert [1] == a[1..2];
	assert [0,1] == a[..2];
	assert [0,1] == a[0..2];
	assert forall i :: 0 <= i <= a.Length ==> [] == a[i..i];
    assert [0,1,2,3,4] == a[..];
    assert forall i :: 0 <= i < a.Length ==> a[i] == i;
  }
}

class B { }

// -------------------------------

class ArrayTests {
  function F0(a: array<int>): bool
  {
    a != null && 10 <= a.Length &&
    a[7] == 13  // error: reads on something outside reads clause
  }

  var b: array<int>;
  function F1(): bool
    reads this;
  {
    b != null && 10 <= b.Length &&
    b[7] == 13  // error: reads on something outside reads clause
  }

  function F2(a: array<int>): bool
    reads this, b, a;
  {
    a != null && 10 <= a.Length &&
    a[7] == 13  // good
    &&
    b != null && 10 <= b.Length &&
    b[7] == 13  // good
  }

  method M0(a: array<int>)
    requires a != null && 10 <= a.Length;
  {
    a[7] := 13;  // error: updates location not in modifies clause
  }

  method M1()
    requires b != null && 10 <= b.Length;
    modifies this;
  {
    b[7] := 13;  // error: updates location not in modifies clause
  }

  method M2()
    modifies this;
  {
    var bb := new int[75];
    b := bb;  // fine
  }

  method M3(a: array<int>)
    requires a != null && 10 <= a.Length;
    requires b != null && 10 <= b.Length;
    modifies this, b, a;
  {
    a[7] := 13;  // good
    b[7] := 13;  // good
  }
}

// -------------------- induction attribute --------------------------------

ghost method Fill_I(s: seq<int>)
  requires forall i :: 1 <= i < |s| ==> s[i-1] <= s[i];
  ensures forall i,j {:induction i} :: 0 <= i < j < |s| ==> s[i] <= s[j];
{  // error: cannot prove postcondition
}

ghost method Fill_J(s: seq<int>)
  requires forall i :: 1 <= i < |s| ==> s[i-1] <= s[i];
  ensures forall i,j {:induction j} :: 0 <= i < j < |s| ==> s[i] <= s[j];
{
}

ghost method Fill_All(s: seq<int>)
  requires forall i :: 1 <= i < |s| ==> s[i-1] <= s[i];
  ensures forall i,j {:induction i,j} :: 0 <= i < j < |s| ==> s[i] <= s[j];
{
}

ghost method Fill_True(s: seq<int>)
  requires forall i :: 1 <= i < |s| ==> s[i-1] <= s[i];
  ensures forall i,j {:induction} :: 0 <= i < j < |s| ==> s[i] <= s[j];
{
}

ghost method Fill_False(s: seq<int>)
  requires forall i :: 1 <= i < |s| ==> s[i-1] <= s[i];
  ensures forall i,j {:induction false} :: 0 <= i < j < |s| ==> s[i] <= s[j];
{  // error: cannot prove postcondition
}

ghost method Fill_None(s: seq<int>)
  requires forall i :: 1 <= i < |s| ==> s[i-1] <= s[i];
  ensures forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j];
{  // error: cannot prove postcondition
}

// -------------- some regression tests; there was a time when array-element LHSs of calls were not translated correctly

method Test_ArrayElementLhsOfCall(a: array<int>, i: int, c: Cdefg<int>) returns (x: int)
  requires a != null && c != null;
  modifies a, c;
{
  if (0 <= i < a.Length) {
    a[i] := x;
    a[i] := Test_ArrayElementLhsOfCall(a, i-1, c);  // this line used to crash Dafny
    c.t := x;
    c.t := Test_ArrayElementLhsOfCall(a, i-1, c);  // this line used to crash Dafny
    var n: nat;
    n := x;  // error: subrange check is applied and it cannot be verified
    n := Test_ArrayElementLhsOfCall(a, i-1, c);  // error: subrange check is applied and it cannot be verified
  }
}

class Cdefg<T> {
  var t: T;
}
