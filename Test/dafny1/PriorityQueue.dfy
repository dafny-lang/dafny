// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class PriorityQueue {
  var N: nat  // capacity
  var n: nat  // current size
  ghost var Repr: set<object>  // set of objects that make up the representation of a PriorityQueue

  var a: array<int>  // private implementation of PriorityQueue

  ghost predicate Valid()
    reads this, Repr
  {
    MostlyValid() &&
    forall j :: 2 <= j <= n ==> a[j/2] <= a[j]
  }

  ghost predicate MostlyValid()
    reads this, Repr
  {
    this in Repr && a in Repr &&
    a.Length == N+1 &&
    0 <= n <= N
  }

  constructor Init(capacity: nat)
    ensures Valid() && fresh(Repr)
    ensures N == capacity
  {
    N := capacity;
    a := new int[capacity + 1];
    n := 0;
    Repr := {this, a};
  }

  method Insert(x: int)
    requires Valid() && n < N
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures n == old(n) + 1 && N == old(N)
  {
    n := n + 1;
    a[n] := x;
    SiftUp(n);
  }

  method SiftUp(k: int)
    requires 1 <= k <= n
    requires MostlyValid()
    requires forall j :: 2 <= j <= n && j != k ==> a[j/2] <= a[j]
    requires forall j :: 1 <= j <= n ==> j/2 != k  // k is a leaf
    modifies a
    ensures Valid()
  {
    var i := k;
    assert MostlyValid();
    while 1 < i
      invariant i <= k && MostlyValid()
      invariant forall j :: 2 <= j <= n && j != i ==> a[j/2] <= a[j]
      invariant forall j :: 1 <= j/2/2 && j/2 == i && j <= n ==> a[j/2/2] <= a[j]
    {
      if a[i/2] <= a[i] {
        return;
      }
      a[i/2], a[i] := a[i], a[i/2];
      i := i / 2;
    }
  }

  method RemoveMin() returns (x: int)
    requires Valid() && 1 <= n
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures n == old(n) - 1
  {
    x := a[1];
    a[1] := a[n];
    n := n - 1;
    SiftDown(1);
  }

  method SiftDown(k: int)
    requires 1 <= k
    requires MostlyValid()
    requires forall j :: 2 <= j <= n && j/2 != k ==> a[j/2] <= a[j]
    requires forall j :: 2 <= j <= n && 1 <= j/2/2 != k ==> a[j/2/2] <= a[j]
    // Alternatively, the line above can be expressed as:
    //     requires forall j :: 1 <= k/2 && j/2 == k && j <= n ==> a[j/2/2] <= a[j]
    modifies a
    ensures Valid()
  {
    var i := k;
    while 2*i <= n  // while i is not a leaf
      invariant 1 <= i && MostlyValid()
      invariant forall j :: 2 <= j <= n && j/2 != i ==> a[j/2] <= a[j]
      invariant forall j :: 2 <= j <= n && 1 <= j/2/2 != i ==> a[j/2/2] <= a[j]
    {
      var smallestChild;
      if 2*i + 1 <= n && a[2*i + 1] < a[2*i] {
        smallestChild := 2*i + 1;
      } else {
        smallestChild := 2*i;
      }
      if a[i] <= a[smallestChild] {
        return;
      }
      a[smallestChild], a[i] := a[i], a[smallestChild];
      i := smallestChild;
      assert 1 <= i/2/2 ==> a[i/2/2] <= a[i];
    }
  }
}

// ---------- Alternative specifications ----------

class PriorityQueue_Alternative {
  var N: nat  // capacity
  var n: nat  // current size
  ghost var Repr: set<object>  // set of objects that make up the representation of a PriorityQueue

  var a: array<int>  // private implementation of PriorityQueue

  ghost predicate Valid()
    reads this, Repr
  {
    MostlyValid() &&
    forall j :: 2 <= j <= n ==> a[j/2] <= a[j]
  }

  ghost predicate MostlyValid()
    reads this, Repr
  {
    this in Repr && a in Repr &&
    a.Length == N+1 &&
    0 <= n && n <= N
  }

  constructor Init(capacity: nat)
    ensures Valid() && fresh(Repr)
    ensures N == capacity
  {
    N := capacity;
    a := new int[capacity + 1];
    n := 0;
    Repr := {this, a};
  }

  method Insert(x: int)
    requires Valid() && n < N
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures n == old(n) + 1 && N == old(N)
  {
    n := n + 1;
    a[n] := x;
    SiftUp();
  }

  method SiftUp()
    requires MostlyValid()
    requires forall j :: 2 <= j <= n && j != n ==> a[j/2] <= a[j]
    modifies a
    ensures Valid()
  {
    var i := n;
    assert MostlyValid();
    while 1 < i
      invariant i <= n && MostlyValid()
      invariant forall j :: 2 <= j <= n && j != i ==> a[j/2] <= a[j]
      invariant forall j :: 1 <= j/2/2 && j/2 == i && j <= n ==> a[j/2/2] <= a[j]
    {
      if a[i/2] <= a[i] {
        return;
      }
      a[i/2], a[i] := a[i], a[i/2];
      i := i / 2;
    }
  }

  method RemoveMin() returns (x: int)
    requires Valid() && 1 <= n
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures n == old(n) - 1
  {
    x := a[1];
    a[1] := a[n];
    n := n - 1;
    SiftDown();
  }

  method SiftDown()
    requires MostlyValid()
    requires forall j :: 4 <= j <= n ==> a[j/2] <= a[j]
    modifies a
    ensures Valid()
  {
    var i := 1;
    while 2*i <= n  // while i is not a leaf
      invariant 1 <= i && MostlyValid()
      invariant forall j :: 2 <= j <= n && j/2 != i ==> a[j/2] <= a[j]
      invariant forall j :: 1 <= j/2/2 && j/2 == i && j <= n ==> a[j/2/2] <= a[j]
    {
      var smallestChild;
      if 2*i + 1 <= n && a[2*i + 1] < a[2*i] {
        smallestChild := 2*i + 1;
      } else {
        smallestChild := 2*i;
      }
      if a[i] <= a[smallestChild] {
        return;
      }
      a[smallestChild], a[i] := a[i], a[smallestChild];
      i := smallestChild;
      assert 1 <= i/2/2 ==> a[i/2/2] <= a[i];
    }
  }
}
