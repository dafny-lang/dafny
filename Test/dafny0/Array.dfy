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
    var y := new object[100];
    y[5] := null;
    y[0..] := null;
    y[..83] := null;
    y[0..y.Length] := null;
  }

  method R() {
    var y := new int[100];
    y[55] := 80;
    y[10..] := 25;
    y[..83] := 30;
    y[50..60] := 35;
    y[55] := 90;

    assert y[54] == 35;
    assert y[55] == 90;
    assert y[83] == 25;
    assert y[8] == 30;
    assert y[90] + y[91] + y[0] + 20 == y.Length;
    assert y[93] == 24;  // error (it's 25)
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
