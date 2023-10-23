// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class LazyInitArray<T(0)> {
  ghost var Contents: seq<T>
  var Zero: T
  /*private*/ var a: array<T>
  /*private*/ var b: array<int>
  /*private*/ var c: array<int>
  /*private*/ var n: int
  /*private*/ ghost var d: seq<int>
  /*private*/ ghost var e: seq<int>
  ghost predicate Valid()
    reads this, a, b, c
  {
    a.Length == |Contents| &&
    b.Length == |Contents| &&
    c.Length == |Contents| &&
    b != c && a != b && a != c &&
    0 <= n && n <= c.Length &&
    (forall i :: 0 <= i && i < |Contents| ==>
       Contents[i] == (if 0 <= b[i] && b[i] < n && c[b[i]] == i then a[i] else Zero)) &&
    (forall i :: 0 <= i && i < |Contents| ==>
              ((exists j :: 0 <= j && j < n && c[j] == i)
               <==>
               0 <= b[i] && b[i] < n && c[b[i]] == i)) &&
    // The idea behind d and e is the following:
    //  *  d is a permutation of the first |Contents| natural numbers
    //  *  e describes which permutation d is
    //  *  c[..n] == d[..n]
    |d| == |Contents| &&
    |e| == |Contents| &&
    (forall i :: 0 <= i && i < n ==> c[i] == d[i]) &&
    (forall i :: 0 <= i && i < |d| ==> 0 <= d[i] && d[i] < |d|) &&
    (forall i :: 0 <= i && i < |e| ==> 0 <= e[i] && e[i] < |e|) &&
    (forall i :: 0 <= i && i < |e| ==> d[e[i]] == i)
  }

  method Init(N: int, zero: T)
    requires 0 <= N
    modifies this, a, b, c
    ensures Valid()
    ensures |Contents| == N && Zero == zero
    ensures forall x :: x in Contents ==> x == zero
  {
    a := new T[N];
    b := new int[N];
    c := new int[N];
    n := 0;

    // initialize ghost variable Contents to a sequence of length N containing only zero's,
    // and ghost variables d and e to be the identity sequences of length N
    ghost var s := [];
    ghost var id := [];
    ghost var k := 0;
    while k < N
      invariant k <= N
      invariant |s| == k && forall i :: 0 <= i && i < |s| ==> s[i] == zero
      invariant |id| == k && forall i :: 0 <= i && i < k ==> id[i] == i
    {
      s := s + [zero];
      id := id + [k];
      k := k + 1;
    }

    d := id;
    e := id;
    Zero := zero;
    Contents := s;
  }

  method Get(i: int) returns (x: T)
    requires Valid()
    requires 0 <= i && i < |Contents|
    ensures x == Contents[i]
  {
    if 0 <= b[i] && b[i] < n && c[b[i]] == i {
      x := a[i];
    } else {
      x := Zero;
    }
  }

  method Set(i: int, x: T)
    requires Valid()
    requires 0 <= i && i < |Contents|
    modifies this, a, b, c
    ensures Valid()
    ensures |Contents| == |old(Contents)| && Contents == Contents[i := x]
    ensures Zero == old(Zero)
  {
    if 0 <= b[i] && b[i] < n && c[b[i]] == i {
    } else {
      assert n <= e[i];  // lemma
      b[i] := n;
      c[n] := i;
      ghost var t := d[n];
      ghost var k := e[i];
      d := d[n := i][k := t];
      e := e[i := n][t := k];
      n := n + 1;
    }

    a[i] := x;
    Contents := Contents[i := x];
  }
}
