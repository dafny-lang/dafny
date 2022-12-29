// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ---------------------------------------

module Test {
  class C {
  }

  function arrSet(a: array<C>): set<object>
    reads a
  {
    set i : int | 0 <= i < a.Length :: a[i]
  }

  method test(a: array<C>, i: int, x: C)
    modifies a
    requires 0 <= i < a.Length
    requires x !in arrSet(a)
  {
    a[i] := x;
    assert arrSet(a) == arrSet(old(a)); // warning: old has no effect
  }
}

// ---------------------------------------

predicate P(s: seq<int>)
predicate Q(a: array<int>)
  reads a

class C {
  var x: int

  predicate PInClass(s: seq<int>)
  static predicate StaticPInClass(s: seq<int>)

  predicate QInClass(a: array<int>)
    reads a
  static predicate StaticQInClass(a: array<int>)
    reads a

  predicate R(y: int := x)
    reads this
}

method TestsNoReads(c: C, s: seq<int>, a: array<int>) {
  ghost var b;
  b := old(P(s)); // warning: old has no effect
  b := old(c.PInClass(s)); // warning: old has no effect
  b := old(C.StaticPInClass(s)); // warning: old has no effect
  b := old(c.StaticPInClass(s)); // warning: old has no effect

  b := old(Q(a));
  b := old(c.QInClass(a));
  b := old(C.StaticQInClass(a));
  b := old(c.StaticQInClass(a));

  b := old(c.R(3));
  b := old(c.R());
}

method Trigger()
  // The following should generate a warning, but preferably not two.
  // That is, if the old expression is copied into the trigger, it
  // is preferable that there's not a second warning for the 'old' there.
  ensures forall s :: P(s) == old(P(s)) // warning: old has no effect

  // A manually supplied trigger should have its own warning, though:
  ensures forall s {:trigger old(P(s))} :: P(s) == old(P(s)) // warning (x2): old has no effect
{
}

// An iterator has several auto-generated old expressions.
// These should not generate any warnings.
iterator Iter()
{
}

// ---------------------------------------

class D {
  var data: int
  const N: int
  var arr: array<real>

  method TestFields()
    ensures data == old(data)
    ensures N == old(N) // warning: old has no effect, since N is const
  {
  }

  method TestArrayElements(j: nat, a: array<real>)
    requires j < a.Length
    ensures a.Length == old(a.Length) // warning: old has no effect
    ensures a[j] == old(a[j])
    ensures a[j] == old(a)[j] // warning: old has no effect
    ensures a[j] == a[old(j)] // warning: old has no effect
  {
  }

  method MoreArrays(b: array<real>)
    requires 0 <= data && data + 1 < arr.Length == b.Length
    requires 1.0 <= arr[data] < arr[data + 1] < 2.0
    requires 4.0 <= b[data] < b[data + 1] < 5.0
    modifies this, arr
    ensures arr == b && data == old(data) + 1
    ensures arr[data] != old(arr[data])
    ensures arr[data] != old(arr)[data]
    ensures arr[data] != arr[old(data)]
    ensures var a, j := arr, data; old(arr[data]) != old(a[j])
  {
    forall i | 0 <= i < arr.Length {
      arr[i] := 2.0 * arr[i];
    }
    arr := b;
    data := data + 1;
  }

  method TestMatrixElements(i: nat, j: nat, m: array2<real>)
    requires i < m.Length0 && j < m.Length1
    ensures m.Length0 == old(m.Length1) // warning: old has no effect
    ensures m[i, j] == old(m[i, j])
    ensures m[i, j] == old(m)[i, j] // warning: old has no effect
    ensures m[i, j] == m[i, old(j)] // warning: old has no effect
  {
  }

  lemma Lemma(y: int)
    requires data == y
  {
  }
}


lemma StaticLemmaWithoutPrecondition(y: int)
{
}

// ---------------------------------------

method StmtExpr(d: D)
  requires d.data == 3
  modifies d
{
  ghost var a;
  d.data := 100;
  if {
  case true =>
    a := assert d.data < 5; 10; // error: assertion failure
  case true =>
    a := old(20 + assert d.data < 5; 10);
  case true =>
    a := old(d.Lemma(3); 10);
  case true =>
    a := old(d.Lemma(100); 10); // error: precondition violation
  case true =>
    a := (d.Lemma(old(100)); 10); // warning: old has no effect
  }
  a := assert d.data < old(105); 0; // warning: old has no effect
}

method CalcStmtExpr(d: D)
  requires d.data == 3
  modifies d
{
  ghost var a;
  d.data := 100;
  if {
  case true =>
    a := old(calc { } 10); // warning: old has no effect
  case true =>
    a := old(calc {
      2;
    ==  { assert d.data == 3; }
      2;
    } 10);
  case true =>
    a := old(calc {
      2;
    ==  { assert d.data == 100; } // error: assertion violation
      2;
    } 10);
  case true =>
    a := old(calc {
      2;
    ==  { d.Lemma(3); }
      2;
    } 10);
  case true =>
    a := old(calc {
      2;
    ==  { StaticLemmaWithoutPrecondition(3); }
      2;
    } 10);
  case true =>
    a := old(calc {
      2;
    ==  { d.Lemma(100); } // error: precondition violation
      2;
    } 10);
  }
}

twostate function CalcStmtExprFunction(d: D, selector: int): int
  requires old(d.data) == 3 && d.data == 100
  reads d
{
  match selector
  case 0 =>
    old(calc { } 10) // warning: old has no effect
  case 1 =>
    old(calc {
      2;
    ==  { assert d.data == 3; }
      2;
    } 10)
  case 2 =>
    old(calc {
      2;
    ==  { assert d.data == 100; } // error: assertion violation
      2;
    } 10)
  case 3 =>
    old(calc {
      2;
    ==  { d.Lemma(3); }
      2;
    } 10)
  case 4 =>
    old(calc {
      2;
    ==  { d.Lemma(100); } // error: precondition violation
      2;
    } 10)
  case _ =>
    10
}
