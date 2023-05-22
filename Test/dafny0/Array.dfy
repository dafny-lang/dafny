// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class A {
  method M() {
    var y := new A?[100];
    y[5] := null;
  }

  method N0() {
    var a: array<int>;
    if 5 < a.Length {
      a[5] := 12;  // error: violates modifies clause
    }
  }

  method N1(a: array?<int>)
    modifies a
  {
    var b := a.Length;  // error: a may be null
  }

  method N2(a: array<int>)
    modifies a
  {
    a[5] := 12;  // error: index may be outside bounds
  }

  method N3(a: array<int>)
    requires 5 < a.Length
    modifies a
    ensures (forall i :: 0 <= i && i < a.Length ==> a[i] == old(a[i]) || (i == 5 && a[i] == 12));
  {
    a[5] := 12;  // all is good
  }

  var zz0: array<A?>
  var zz1: array<B?>
  method O() {
    var zz2 := new A?[25];
    assert zz2 != zz0;  // holds because zz2 is newly allocated
    var o: object? := zz0;
    assert this != o;  // holds because zz0 has a different type

    if 2 <= zz0.Length && zz0.Length == zz1.Length {
      o := zz1[1];
      assert zz0[1] == o ==> o == null;  // holds because zz0 and zz1 have different element types
    }

    assert zz2[20] == null;  // error: no reason that this must hold
  }

  var x: array<int>
  method P0()
    modifies this
  {
    if 100 <= x.Length {
      x[5] := 12;  // error: violates modifies clause
    }
  }
  method P1()
    modifies this`x
  {
    if 100 <= x.Length {
      x[5] := 12;  // error: violates modifies clause
    }
  }
  method P2()
    modifies x
  {
    if 100 <= x.Length {
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

  method ArrayToSequenceTests(a: array<int>, lo: int, hi: int)
  {
    if (a.Length == 10) {
      var s;
      s := a[2..5];
      assert |s| == 3;
      s := a[..5];
      assert |s| == 5;
      s := a[2..];
      assert |s| == 8;
      s := a[..];
      assert |s| == 10;
      s := a[..10] + a[0..];
    } else {
      if {
        case 0 <= lo <= a.Length =>
          var s := a[lo..] + a[..lo];
        case 0 <= lo <= a.Length && 0 <= hi <= a.Length =>
          var s := a[lo..hi];  // error: lo may be greater than hi
        case true =>
      }
    }
  }

  ghost function BadRangeReads(a: array<int>, all: bool): bool
  {
    a.Length == 10 &&
    if all then
      a[..] == []  // error: not allowed to read the elements of a
    else
      a[2..5] +       // error: not allowed to read the elements of a
      a[..5] +        // error: not allowed to read the elements of a
      a[2..] == []    // error: not allowed to read the elements of a
  }
  ghost function GoodRangeReads(a: array<int>, all: bool): bool
    reads a
  {
    a.Length == 10 &&
    if all then
      a[..] == []  // no prob, since we now have a reads clause
    else
      a[2..5] + a[..5] + a[2..] == []  // no prob, since we now have a reads clause
  }
  ghost function AnotherGoodRangeReads(a: array<int>, j: int): bool
  {
    0 <= j && j <= a.Length &&
    a[j..j] == []
  }

  ghost predicate Q0(s: seq<int>)
  ghost predicate Q1(s: seq<int>)
  method FrameTest(a: array<int>) returns (b: array<int>)
    requires Q0(a[..]);
  {
    b := CreateArray(a);
    assert Q0(a[..]);  // this should still be known after the call to CreateArray
    assert Q1(b[..]);
  }
  method CreateArray(a: array<int>) returns (b: array<int>)
    ensures fresh(b) && Q1(b[..])
}

class B { }

// -------------------------------

class ArrayTests {
  ghost function F0(a: array<int>): bool
  {
    10 <= a.Length &&
    a[7] == 13  // error: reads on something outside reads clause
  }

  var b: array<int>;
  ghost function F1(): bool
    reads this
  {
    10 <= b.Length &&
    b[7] == 13  // error: reads on something outside reads clause
  }

  ghost function F2(a: array<int>): bool
    reads this, b, a
  {
    10 <= a.Length &&
    a[7] == 13  // good
    &&
    10 <= b.Length &&
    b[7] == 13  // good
  }

  method M0(a: array<int>)
    requires 10 <= a.Length
  {
    a[7] := 13;  // error: updates location not in modifies clause
  }

  method M1()
    requires 10 <= b.Length
    modifies this
  {
    b[7] := 13;  // error: updates location not in modifies clause
  }

  method M2()
    modifies this
  {
    var bb := new int[75];
    b := bb;  // fine
  }

  method M3(a: array<int>)
    requires 10 <= a.Length
    requires 10 <= b.Length
    modifies this, b, a
  {
    a[7] := 13;  // good
    b[7] := 13;  // good
  }
}

// -------------------- induction attribute --------------------------------

ghost method Fill_I(s: seq<int>)
  requires forall i :: 1 <= i < |s| ==> s[i-1] <= s[i]
  ensures forall i,j {:induction i} :: 0 <= i < j < |s| ==> s[i] <= s[j]
{  // error: cannot prove postcondition
}

ghost method Fill_J(s: seq<int>)
  requires forall i :: 1 <= i < |s| ==> s[i-1] <= s[i]
  ensures forall i,j {:induction j} :: 0 <= i < j < |s| ==> s[i] <= s[j]
{
}

ghost method Fill_All(s: seq<int>)
  requires forall i :: 1 <= i < |s| ==> s[i-1] <= s[i]
  ensures forall i,j {:induction i,j} :: 0 <= i < j < |s| ==> s[i] <= s[j]
{
}

ghost method Fill_True(s: seq<int>)
  requires forall i :: 1 <= i < |s| ==> s[i-1] <= s[i]
  ensures forall i,j {:induction} :: 0 <= i < j < |s| ==> s[i] <= s[j]
{
}

ghost method Fill_False(s: seq<int>)
  requires forall i :: 1 <= i < |s| ==> s[i-1] <= s[i]
  ensures forall i,j {:induction false} :: 0 <= i < j < |s| ==> s[i] <= s[j]
{  // error: cannot prove postcondition
}

ghost method Fill_None(s: seq<int>)
  requires forall i :: 1 <= i < |s| ==> s[i-1] <= s[i]
  ensures forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j]
{  // error: cannot prove postcondition
}

// -------------- some regression tests; there was a time when array-element LHSs of calls were not translated correctly

method Test_ArrayElementLhsOfCall(a: array<nat>, i: int, c: Cdefg<nat>) returns (x: int)
  modifies a, c
{
  if 0 <= i < a.Length {
    a[i] := x;  // error: subrange check is applied and it cannot be verified
    a[i] := Test_ArrayElementLhsOfCall(a, i-1, c);  // this line used to crash Dafny
    c.t := x-1;  // error: subrange check is applied and it cannot be verified
    c.t := Test_ArrayElementLhsOfCall(a, i-1, c);  // this line used to crash Dafny
    var n: nat;
    n := Test_ArrayElementLhsOfCall(a, i-1, c);  // error: subrange check is applied and it cannot be verified
  }
}

class Cdefg<T> {
  var t: T
  constructor (t: T) {
    this.t := t;
  }
}

// ---------- allocation business -----------

class MyClass {
  ghost var Repr: set<object>
  ghost predicate Valid()
    reads this, Repr
}

method AllocationBusiness0(a: array<MyClass>, j: int)
  requires 0 <= j < a.Length
{
  var c := new MyClass;
  assert c !in a[j].Repr;  // the proof requires allocation axioms for arrays
}

method AllocationBusiness1(a: array<MyClass>, j: int)
  requires 0 <= j < a.Length
  requires a[j].Valid()
{
  var c := new MyClass;
  assert a[j].Valid();  // the allocation should not have invalidated the validity of a[j]
}

method AllocationBusiness2(a: array2<MyClass>, i: int, j: int)
  requires 0 <= i < a.Length0 && 0 <= j < a.Length1
{
  var c := new MyClass;
  assert c !in a[i,j].Repr;  // the proof requires allocation axioms for multi-dim arrays
}

// ------- a regression test, testing that dtype is set correctly after allocation ------

module DtypeRegression {
  ghost predicate array_equal(a: array<int>, b: array<int>)
    reads a, b
  {
    a[..] == b[..]
  }

  method duplicate_array(input: array<int>, len: int) returns (output: array<int>)
    requires len == input.Length
    ensures array_equal(input, output)
  {
    output := new int[len];
    var i := 0;
    while i < len
      invariant 0 <= i <= len;
      invariant forall j :: 0 <= j < i ==> output[j] == input[j];
    {
      output[i] := input[i];
      i := i + 1;
    }
  }
}

// ------- :| -------

class AssignSuchThat {
  var x: int

  method P() {
    x :| assume x == 10;  // error: P is not allowed to modify "this"
  }

  method Q0(a: array<int>)
    requires a.Length == 50
  {
    a[22] :| assume a[22] == 12;  // error: Q0 is not allowed to modify "a"
    assert a[22] == 12;
  }
  method Q1(a: array<int>)
    requires a.Length == 50
    modifies a
  {
    a[22] :| assume a[22] == 12;
    assert a[22] == 12;
  }
  method Q2(a: array<int>)
    requires a.Length == 50
    modifies a
  {
    a[22] :| assume a[22] == 12;
    assert a[22] == 0;  // error: a[22] is not 0
  }
  method R(that: AssignSuchThat)
    modifies this, that
  {
    this.x, that.x :| assume this.x == 5 && that.x == 5;  // error: duplicate LHSs (no regard to same final values in :| statements)
  }
}

// WISH: autoTriggers disabled because of induction
