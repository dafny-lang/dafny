// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file was created in the early stages of Dafny, when the
// language didn't even support arrays yet.  Still, as written,
// it does verify.

class SparseArray<T(0)> {
  ghost var Contents: seq<T>;
  var zero: T;
  /*private*/ var a: seq<T>;  // should really be an array
  /*private*/ var b: seq<int>;  // should really be an array
  /*private*/ var c: seq<int>;  // should really be an array
  /*private*/ var n: int;
  /*private*/ ghost var d: seq<int>;  // would be better as an array
  /*private*/ ghost var e: seq<int>;  // would be better as an array
  ghost function Valid(): bool
    reads this;
  {
    |a| == |Contents| &&
    |b| == |Contents| &&
    |c| == |Contents| &&
    0 <= n && n <= |c| &&
    (forall i :: 0 <= i && i < |Contents| ==>
       Contents[i] == (if 0 <= b[i] && b[i] < n && c[b[i]] == i then a[i] else zero)) &&
    (forall i :: 0 <= i && i < |Contents| ==>
              (i in c[..n] <==> 0 <= b[i] && b[i] < n && c[b[i]] == i)) &&
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
    requires 0 <= N;
    modifies this;
    ensures Valid();
    ensures |Contents| == N && this.zero == zero;
    ensures (forall x :: x in Contents ==> x == zero);
  {
    var aa : seq<T> := AllocateArray(N);  this.a := aa;
    var bb : seq<int> := AllocateArray(N);  this.b := bb;
    bb := AllocateArray(N);  this.c := bb;
    this.n := 0;

    // initialize ghost variable Contents to a sequence of length N containing only zero's,
    // and ghost variables d and e to be the identity sequences of length N
    ghost var s := [];
    ghost var id := [];
    ghost var k := 0;
    while (k < N)
      invariant k <= N;
      invariant |s| == k;
      // TODO: why doesn't this work instead of the next line?  invariant (forall x :: x in s ==> x == zero);
      invariant (forall i :: 0 <= i && i < |s| ==> s[i] == zero);
      invariant |id| == k && (forall i :: 0 <= i && i < k ==> id[i] == i);
    {
      s := s + [zero];
      id := id + [k];
      k := k + 1;
    }

    this.zero := zero;
    this.Contents := s;
    this.d := id;
    this.e := id;
  }
  method Get(i: int) returns (x: T)
    requires Valid();
    requires 0 <= i && i < |Contents|;
    ensures x == Contents[i];
  {
    if (0 <= b[i] && b[i] < n && c[b[i]] == i) {
      x := a[i];
    } else {
      x := zero;
    }
  }
  method Set(i: int, x: T)
    requires Valid();
    requires 0 <= i && i < |Contents|;
    modifies this;
    ensures Valid();
    ensures |Contents| == |old(Contents)| && Contents == Contents[i := x];
    ensures zero == old(zero);
  {
    if (0 <= b[i] && b[i] < n && c[b[i]] == i) {
    } else {
      assert n <= e[i];  // lemma
      b := b[i := n];
      c := c[n := i];
      ghost var t := d[n];
      ghost var k := e[i];
      d := d[n := i][k := t];
      e := e[i := n][t := k];
      n := n + 1;
    }
    a := a[i := x];
    Contents := Contents[i := x];
  }

}

/* The following method is here only to simulate support of arrays in Dafny */
/*private*/ method AllocateArray<G(0)>(n: int) returns (arr: seq<G>)
  requires 0 <= n;
  ensures |arr| == n;
{
  arr := [];
  var i := 0;
  while (i < n)
    invariant i <= n && |arr| == i;
  {
    var g: G;
    arr := arr + [g];
    i := i + 1;
  }
}
