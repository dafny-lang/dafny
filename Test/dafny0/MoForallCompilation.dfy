// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  TestAggregateArrayUpdate();
  TestAggregateMultiArrayUpdate();
  TestAggregateFieldUpdate();
}

// ------------------------------------------------------------

method TestAggregateArrayUpdate() {
  var a := new real[8](i => i as real - 4.0);
  var b := new real[8];
  var c := new bool[8];
  forall i | 2-i <= 2 && i < a.Length {
    b[7-i] := a[i] + 4.0;
  }
  forall i | 0 <= i < a.Length {
    c[i] := a[i] < b[i];
  }
  PrintArray(a);  // -4.0 -3.0 -2.0 -1.0 0.0 1.0 2.0 3.0
  PrintArray(b);  // 7.0 6.0 5.0 4.0 3.0 2.0 1.0 0.0
  PrintArray(c);  // true true true true true true false false
}

method PrintArray(a: array) {
  var i := 0;
  while i < a.Length {
    print a[i], " ";
    i := i + 1;
  }
  print "\n";
}

// ------------------------------------------------------------

method TestAggregateMultiArrayUpdate() {
  var matrix := new int[12,3]((i,j) => i+j);
  PrintMatrix(matrix);

  // various ways of computing the transpose:
  var m' := new int[matrix.Length1, matrix.Length0](
    (i,j) requires 0 <= i < matrix.Length1 && 0 <= j < matrix.Length0 reads matrix => matrix[j,i]);
  var m0, m1, m2 := Transpose(matrix);
  PrintMatrix(m');
  PrintMatrix(m0);
  PrintMatrix(m1);
  PrintMatrix(m2);

  print MatrixEqual(m0, m'), "\n";  // true
  m'[2,2] := 87;
  print MatrixEqual(m0, m'), "\n";  // false
}

method PrintMatrix(m: array2<int>) {
  var i := 0;
  while i < m.Length0 {
    var j := 0;
    while j < m.Length1 {
      print m[i,j], " ";
      j := j + 1;
    }
    print "\n";
    i := i + 1;
  }
}

method Transpose<T(0)>(m: array2<T>) returns (m0: array2<T>, m1: array2<T>, m2: array2<T>)
  ensures fresh(m0) && fresh(m1) && fresh(m2)
  ensures MatrixEqual(m0, m1) && MatrixEqual(m0, m2)
{
  var X, Y := m.Length1, m.Length0;
  m0, m1, m2 := new T[X, Y], new T[X, Y], new T[X, Y];
  forall i,j | 0 <= i < X && 0 <= j < Y {
    m0[i,j] := m[j,i];
  }
  forall i: nat, j: nat | i < X && j < Y {
    m1[i,j] := m[j,i];
  }
  forall i: nat, j | -Y < -j && 3+i < X+3 && j >= 0 {
    m2[i,j] := m[j,i];
  }
}

predicate MatrixEqual<T(==)>(m: array2, m': array2)
  reads m, m'
{
  (m.Length0, m.Length1) == (m'.Length0, m'.Length1) &&
  forall i,j :: 0 <= i < m.Length0 && 0 <= j < m.Length1 ==> m[i,j] == m'[i,j]
}

// ------------------------------------------------------------

method TestAggregateFieldUpdate() {
  var a := Node.Create(4);
  var b := Node.Create(7);
  a.Print();
  b.Print();

  print b.StartsWith(a), "\n";  // false

  a.IncEverything(3);
  a.Print();
  print b.StartsWith(a), "\n";  // false
}

class Node {
  var Repr: set<Node>  // for the purpose of this test, Repr is non-ghost
  ghost predicate Valid()
    reads this, Repr
  {
    this in Repr &&
    (next != null ==>
      next in Repr && next.Repr <= Repr && this !in next.Repr && next.Valid())
  }

  var val: int
  var next: Node?

  constructor (val: int, next: Node?)
    requires next != null ==> next.Valid()
    ensures Valid() && fresh(Repr - if next == null then {} else next.Repr)
  {
    this.val, this.next := val, next;
    Repr := {this} + if next == null then {} else next.Repr;
  }

  static method Create(n: nat) returns (d: Node)
    ensures d.Valid() && fresh(d.Repr)
  {
    d := new Node(0, null);
    var i := 1;
    while i < n
      invariant d.Valid() && fresh(d.Repr)
    {
      d := new Node(i, d);
      i := i + 1;
    }
  }

  method Print()
    requires Valid()
  {
    var d := this;
    while d != null
      invariant d != null ==> d.Valid()
      decreases if d == null then {} else d.Repr
    {
      print d.val, " ";
      d := d.next;
    }
    print "\n";
  }

  predicate StartsWith(that: Node?)
    requires Valid() && (that != null ==> that.Valid())
    reads Repr, if that == null then {} else that.Repr
    decreases Repr
  {
    that != null ==>
      val == that.val && next != null && next.StartsWith(that.next)
  }

  method IncEverything(n: int)
    requires Valid()
    modifies Repr
    ensures Valid()
  {
    forall d | d in Repr {
      d.val := d.val + n;
    }
    StillValidAfterValChanges();
  }

  twostate lemma StillValidAfterValChanges()
    requires old(Valid())
    requires forall d :: d in old(Repr) ==> unchanged(d`next, d`Repr)
    ensures Valid()
    decreases old(Repr)
  {
    if next != null {
      next.StillValidAfterValChanges();
    }
  }
}
